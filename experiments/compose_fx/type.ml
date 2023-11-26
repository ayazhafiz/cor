open Loc
open Symbol

type variable = [ `Var of int ] [@@deriving show]

type loc_tvar = loc * tvar
and ty_tag = string * loc_tvar list

(** Concrete type content *)
and ty_content =
  | TFn of loc_tvar * loc_tvar
  | TTag of { tags : ty_tag list; ext : loc_tvar }
  | TTagEmpty
  | TPrim of [ `Str | `Int | `Unit ]

and ty_alias_content = { alias : loc_symbol * loc_tvar list; real : tvar }

and ty =
  | Link of tvar  (** Link to a type *)
  | Unbd of string option
  | ForA of string option  (** generalized type *)
  | Content of ty_content
  | Alias of ty_alias_content

and tvar = { ty : ty ref; var : variable; recur : bool ref } [@@deriving show]
(** Mutable type cell *)

let tvar_deref tvar = !(tvar.ty)
let tvar_set tvar ty = tvar.ty := ty

let tvar_set_recur tvar recur =
  if !(tvar.recur) && not recur then failwith "recursive type variable";
  tvar.recur := recur

let tvar_recurs tvar = !(tvar.recur)
let tvar_v tvar = tvar.var

let tvar_int =
  { ty = ref (Content (TPrim `Int)); var = `Var 0; recur = ref false }

let tvar_str =
  { ty = ref (Content (TPrim `Str)); var = `Var 1; recur = ref false }

let min_var = 1000

let rec unlink tvar =
  match tvar_deref tvar with Link t -> unlink t | _ -> tvar

let rec unlink_w_alias tvar =
  match tvar_deref tvar with
  | Link t -> unlink_w_alias t
  | Alias { real; _ } -> unlink_w_alias real
  | _ -> tvar

let chase_tags tags ext : ty_tag list * tvar =
  let rec go : ty_tag list -> tvar -> _ =
   fun all_tags ext ->
    match tvar_deref @@ unlink ext with
    | Link _ -> failwith "unreachable"
    | Unbd _ -> (all_tags, ext)
    | ForA _ -> (all_tags, ext)
    | Content TTagEmpty -> (all_tags, ext)
    | Content (TTag { tags; ext }) -> go (all_tags @ tags) (snd ext)
    | Content (TFn _) -> failwith "not a tag"
    | Content (TPrim _) -> failwith "not a tag"
    | Alias { real; _ } -> go all_tags real
  in
  go tags ext

type fresh_tvar = ty -> tvar

let is_empty_tag : tvar -> bool =
 fun t ->
  match tvar_deref @@ unlink t with
  | Content (TTag { tags = []; _ }) | Content TTagEmpty -> true
  | _ -> false

(* name *)

type claimed_names = (variable * string) list
type type_hit_counts = (variable * int) list

let preprocess : tvar list -> claimed_names * type_hit_counts =
 fun tys ->
  let replace tbl k v =
    let tbl' = List.remove_assoc k !tbl in
    tbl := (k, v) :: tbl'
  in
  let update tbl k f d =
    let v = match List.assoc_opt k !tbl with None -> d | Some v -> f v in
    replace tbl k v
  in
  let claimed = ref [] in
  let hits = ref [] in
  let rec go_ty : variable list -> tvar -> unit =
   fun visited t ->
    let t = unlink t in
    let var = tvar_v t in
    if List.mem var visited then ()
    else
      let visited = var :: visited in
      match tvar_deref t with
      | Link _ -> failwith "unreachable"
      | ForA (Some name) -> replace claimed var name
      | Unbd (Some name) -> replace claimed var name
      | ForA None | Unbd None -> update hits var (fun h -> h + 1) 1
      | Content TTagEmpty -> ()
      | Content (TPrim _) -> ()
      | Content (TTag { tags; ext }) ->
          let tag_vars = List.map snd tags |> List.flatten |> List.map snd in
          List.iter (go_ty visited) tag_vars;
          go_ty visited @@ snd ext
      | Content (TFn (in', out')) ->
          go_ty visited @@ snd in';
          go_ty visited @@ snd out'
      | Alias { real; alias = _name, vars } ->
          let alias_vars = List.map snd vars in
          List.iter (go_ty visited) alias_vars;
          go_ty visited real
  in
  List.iter (go_ty []) tys;
  (List.rev !claimed, List.rev !hits)

let fresh_name_generator () =
  let tbl = ref [] in
  fun hint ->
    let rec find_named n i =
      let cand = match i with 0 -> n | i -> Printf.sprintf "%s%d" n i in
      if List.mem cand !tbl then find_named n (i + 1) else cand
    in
    let rec find_unnamed n =
      let letter = Char.chr @@ (97 + (n mod 26)) in
      let extra = max 0 (n - 25) in
      let cand =
        if extra = 0 then Char.escaped letter
        else Printf.sprintf "%c%d" letter extra
      in
      if List.mem cand !tbl then find_unnamed (n + 1) else cand
    in
    let name =
      match hint with Some hint -> find_named hint 0 | None -> find_unnamed 0
    in
    tbl := name :: !tbl;
    name

type named_vars = (variable * [ `Wild | `Name of string ]) list

let name_vars : tvar list -> named_vars =
 fun tys ->
  let claimed, hits = preprocess tys in
  let fresh_name = fresh_name_generator () in
  let names' =
    List.map (fun (i, name) -> (i, `Name (fresh_name (Some name)))) claimed
  in
  let names'' =
    List.map
      (fun (i, hits) ->
        let name = if hits == 1 then `Wild else `Name (fresh_name None) in
        (i, name))
      hits
  in
  names' @ names''

(* format *)

let ellipsis = ".."

let pp_tvar :
    Symbol.t -> variable list -> named_vars -> Format.formatter -> tvar -> unit
    =
 fun symbols visited names f t ->
  let open Format in
  let pp_named var c =
    let name =
      match List.assoc_opt var names with
      | Some `Wild -> Printf.sprintf "%c*" c
      | Some (`Name n) -> Printf.sprintf "%c%s" c n
      | None ->
          let (`Var i) = var in
          Printf.sprintf "<%c%d>" c i
    in
    pp_print_string f name
  in
  let int_of_parens_ctx = function
    | `Free -> 1
    | `AppHead -> 2
    | `FnHead -> 3
  in
  let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2 in
  let with_parens needs_parens inside =
    if needs_parens then pp_print_string f "(";
    inside ();
    if needs_parens then pp_print_string f ")"
  in
  let rec go_head deep parens t =
    let var = tvar_v t in
    match (tvar_deref @@ unlink t, deep) with
    | Unbd _, _ -> pp_named var '?'
    | ForA _, _ -> pp_named var '\''
    | Link _, _ -> failwith "unreachable"
    | Content TTagEmpty, _ -> pp_print_string f "[]"
    | Content (TPrim `Str), _ -> pp_print_string f "Str"
    | Content (TPrim `Int), _ -> pp_print_string f "Int"
    | Content (TPrim `Unit), _ -> pp_print_string f "{}"
    | Content (TTag { tags; ext }), _ ->
        let tags, ext = chase_tags tags @@ snd ext in
        fprintf f "@[<hv 2>[@,";
        List.iteri
          (fun i (tag, args) ->
            fprintf f "@[<hov 2>%s" tag;
            List.iter (fun _ -> fprintf f "@ %s" ellipsis) args;
            fprintf f "@]";
            if i < List.length tags - 1 then fprintf f ",@ ")
          tags;
        fprintf f "@,]";
        let print_ext () = go_head deep `Free ext in
        if not (is_empty_tag ext) then print_ext ();
        fprintf f "@]"
    | Content (TFn (in', out)), _ ->
        fprintf f "@[<hov 2>";
        let pty () =
          go_head true `FnHead @@ snd in';
          fprintf f "@ -> ";
          go_head true `Free @@ snd out
        in
        with_parens (parens >> `Free) pty;
        fprintf f "@]"
    | Alias { alias = head, args; real = _ }, true -> (
        match args with
        | [] -> pp_symbol symbols f @@ snd head
        | _ ->
            let pty () =
              fprintf f "@[<hov 2>%a@ " (pp_symbol symbols) (snd head);
              List.iteri
                (fun i _ ->
                  if i > 0 then fprintf f "@ ";
                  pp_print_string f ellipsis)
                args;
              fprintf f "@]"
            in
            with_parens (parens >> `Free) pty)
    | Alias { alias = head, args; real = _ }, false -> (
        let rec go_args = function
          | [] -> ()
          | [ (_, arg) ] -> go_head true `AppHead arg
          | (_, arg) :: args ->
              go_head true `AppHead arg;
              fprintf f "@ ";
              go_args args
        in
        match args with
        | [] -> fprintf f "%a" (pp_symbol symbols) (snd head)
        | _ ->
            let pty () =
              fprintf f "@[<hov 2>%a@ " (pp_symbol symbols) (snd head);
              go_args args;
              fprintf f "@]"
            in
            with_parens (parens >> `Free) pty)
  in
  let rec go_tag : variable list -> ty_tag -> unit =
   fun visited (tag_name, payloads) ->
    fprintf f "@[<hov 2>%s" tag_name;
    List.iter
      (fun (_, p) ->
        fprintf f "@ ";
        go visited `AppHead p)
      payloads;
    fprintf f "@]"
  and go visited parens t =
    let t = unlink t in
    let var = tvar_v t in
    let recurs = tvar_recurs @@ t in
    let inner f () =
      if List.mem var visited then (
        (* if not recurs then failwith "type is recursive, but not marked"; *)
        (* This is a recursive type *)
        fprintf f "@[<hov 2><%s" ellipsis;
        go_head false `Free t;
        fprintf f ">@]")
      else
        let visited = var :: visited in
        match tvar_deref t with
        | Unbd _ -> pp_named var '?'
        | ForA _ -> pp_named var '\''
        | Link t -> go visited parens t
        | Content TTagEmpty -> pp_print_string f "[]"
        | Content (TPrim `Str) -> pp_print_string f "Str"
        | Content (TPrim `Int) -> pp_print_string f "Int"
        | Content (TPrim `Unit) -> pp_print_string f "{}"
        | Content (TTag { tags; ext }) ->
            let tags, ext = chase_tags tags @@ snd ext in
            fprintf f "@[<hv 2>[@,";
            List.iteri
              (fun i t ->
                go_tag visited t;
                if i < List.length tags - 1 then fprintf f ",@ ")
              tags;
            fprintf f "@,]";
            let print_ext () = go visited `Free ext in
            if not (is_empty_tag ext) then print_ext ();
            fprintf f "@]"
        | Content (TFn (in', out)) ->
            fprintf f "@[<hov 2>";
            let pty () =
              go visited `FnHead @@ snd in';
              fprintf f "@ -> ";
              go visited `Free @@ snd out
            in
            with_parens (parens >> `Free) pty;
            fprintf f "@]"
        | Alias { alias = head; real }
          when Symbol.syn_of symbols (snd @@ fst head) = "X" ->
            go visited parens real
        | Alias { alias = head, args; real = _ } ->
            let header f () =
              let rec go_args = function
                | [] -> ()
                | [ (_, arg) ] -> go visited `AppHead arg
                | (_, arg) :: args ->
                    go visited `AppHead arg;
                    fprintf f "@ ";
                    go_args args
              in
              match args with
              | [] -> fprintf f "%a" (pp_symbol symbols) (snd head)
              | _ ->
                  let pty () =
                    fprintf f "@[<hov 2>%a@ " (pp_symbol symbols) (snd head);
                    go_args args;
                    fprintf f "@]"
                  in
                  with_parens (parens >> `Free) pty
            in
            fprintf f "@[<hov 2>%a@]" header ()
    in
    if recurs then fprintf f "@[<hov 2>%%%a@]" inner () else inner f ()
  in
  go visited `Free t

let string_of_tvar width symbols names tvar =
  (*let (`Var var) = (unlink tvar).var in
    "(" ^ string_of_int var ^ ") "
    ^*)
  Util.with_buffer (fun f -> pp_tvar symbols [] names f tvar) width
