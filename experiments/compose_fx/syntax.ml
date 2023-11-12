open Util
open Language

type lineco = int * int [@@deriving show]
(** line * col *)

type loc = lineco * lineco [@@deriving show]
(** start * end *)

let noloc = ((0, 0), (0, 0))

type loc_str = loc * string [@@deriving show]
type variable = [ `Var of int ] [@@deriving show]

type loc_tvar = loc * tvar
and ty_tag = string * loc_tvar list

(** Concrete type content *)
and ty_content =
  | TFn of loc_tvar * loc_tvar
  | TTag of { tags : ty_tag list; ext : loc_tvar }
  | TTagEmpty
  | TPrim of [ `Str | `Unit ]

and ty =
  | Unbd
  | Link of tvar  (** Link to a type *)
  | ForA of string option  (** generalized type *)
  | Content of ty_content
  | Alias of { alias : loc_str * loc_tvar list; real : tvar }

and tvar = { ty : ty ref; var : variable } [@@deriving show]
(** Mutable type cell *)

let tvar_deref tvar = !(tvar.ty)
let tvar_set tvar ty = tvar.ty := ty
let tvar_v tvar = tvar.var

let rec unlink tvar =
  match tvar_deref tvar with Link t -> unlink t | _ -> tvar

let chase_tags tags ext : ty_tag list * tvar =
  let rec go : ty_tag list -> tvar -> _ =
   fun all_tags ext ->
    match tvar_deref @@ unlink ext with
    | Link _ -> failwith "unreachable"
    | Unbd -> (all_tags, ext)
    | ForA _ -> (all_tags, ext)
    | Content TTagEmpty -> (all_tags, ext)
    | Content (TTag { tags; ext }) -> go (all_tags @ tags) (snd ext)
    | Content (TFn _) -> failwith "not a tag"
    | Content (TPrim _) -> failwith "not a tag"
    | Alias { real; _ } -> go all_tags real
  in
  go tags ext

type e_pat = loc * tvar * pat
(** An elaborated pattern *)

and pat = PVar of string

type pat_set = loc * tvar * e_pat list

type e_expr = loc * tvar * expr
(** An elaborated expression *)

and expr =
  | Var of string
  | Tag of string * e_expr list
  | Let of (loc * loc_tvar * string) * e_expr * e_expr  (** let x = e in b *)
  | Clos of (loc * loc_tvar * string) * e_expr
  | Call of e_expr * e_expr

(** A top-level definition *)
type def =
  | TyAlias of loc_str * loc_tvar list * loc_tvar
  | Sig of loc_str * loc_tvar
  | Def of loc_str * e_expr
  | Run of loc_str * e_expr

type e_def = loc * tvar * def
(** An elaborated definition *)

type program = e_def list
type fresh_tvar = ty -> tvar
type parse_ctx = { fresh_tvar : fresh_tvar }

(* extractions *)
let xloc (l, _, _) = l
let xty (_, t, _) = t
let xv (_, _, v) = v

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
      | ForA None | Unbd -> update hits var (fun h -> h + 1) 1
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

let pp_tvar : named_vars -> Format.formatter -> tvar -> unit =
 fun names f t ->
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
    if List.mem var visited then
      (* This is a recursive type *)
      pp_print_string f "..."
    else
      let visited = var :: visited in
      match tvar_deref t with
      | Unbd -> pp_named var '?'
      | ForA _ -> pp_named var '\''
      | Link t -> go visited parens t
      | Content TTagEmpty -> pp_print_string f "[]"
      | Content (TPrim `Str) -> pp_print_string f "Str"
      | Content (TPrim `Unit) -> pp_print_string f "{}"
      | Content (TTag { tags; ext }) ->
          let tags, ext = chase_tags tags @@ snd ext in
          fprintf f "@[<v 0>[@[<v 2>@,";
          List.iteri
            (fun i t ->
              if i > 0 then fprintf f ",@,";
              go_tag visited t)
            tags;
          fprintf f "@]@,]";
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
      | Alias { alias = head, args; real = _ } -> (
          let rec go_args = function
            | [] -> ()
            | [ (_, arg) ] -> go visited `AppHead arg
            | (_, arg) :: args ->
                go visited `AppHead arg;
                fprintf f "@ ";
                go_args args
          in
          match args with
          | [] -> fprintf f "%s" @@ snd head
          | _ ->
              let pty () =
                fprintf f "@[<hov 2>%s@ " @@ snd head;
                go_args args;
                fprintf f "@]"
              in
              with_parens (parens >> `Free) pty)
  in
  go [] `Free t

let string_of_tvar width names tvar =
  with_buffer (fun f -> pp_tvar names f tvar) width

type node_kind = [ `Def of string | `Var of string | `Generic ]
type found_node = (loc * tvar * node_kind) option

let tightest_node_at : loc -> e_expr -> found_node =
 fun loc program ->
  let or_else o f = match o with Some a -> Some a | None -> f () in
  let rec expr (l, ty, e) : found_node =
    let deeper =
      match e with
      | Var _ -> None
      | Let ((l, ty, x), e1, e2) ->
          if within loc l then Some (l, snd ty, `Def x)
          else or_else (expr e1) (fun () -> expr e2)
      | Tag (_, tags) -> List.find_map (fun tag -> expr tag) tags
      | Clos ((l, ty, x), e) ->
          if within loc l then Some (l, snd ty, `Var x) else expr e
      | Call (e1, e2) -> or_else (expr e1) (fun () -> expr e2)
    in
    or_else deeper (fun () ->
        if within loc l then
          let kind = match e with Var x -> `Var x | _ -> `Generic in
          Some (l, ty, kind)
        else None)
  in
  expr program

let type_at loc program =
  match tightest_node_at loc program with
  | Some (l, ty, _) when l = loc -> Some ty
  | _ -> None

let hover_info lineco program =
  let open Printf in
  let wrap_code code = sprintf "```easy_tags\n%s\n```" code in
  let gen_docs (range, ty, kind) =
    let names = name_vars [ ty ] in
    let ty_str = string_of_tvar default_width names ty in
    let split =
      if List.length @@ String.split_on_char '\n' ty_str > 0 then "\n" else " "
    in
    let prefix =
      match kind with
      | `Var x -> sprintf "(var) %s:%s" x split
      | `Def x -> sprintf "(def) %s:%s" x split
      | `Pat -> ""
      | `Generic -> ""
    in
    let ty_doc = prefix ^ ty_str in
    let md_docs = [ wrap_code ty_doc ] in
    { range; md_docs }
  in
  let node = tightest_node_at (lineco, lineco) program in
  Option.map gen_docs node

let with_parens f needs_parens inside =
  let open Format in
  if needs_parens then pp_print_string f "(";
  inside ();
  if needs_parens then pp_print_string f ")"

let pp_pat f (_, _, p) =
  let open Format in
  let rec go_pat (_, _, atom) = match atom with PVar x -> fprintf f "%s" x
  and go_pat_set atoms =
    fprintf f "@[<hov 2>";
    List.iteri
      (fun i atom ->
        if i > 0 then fprintf f "@ | ";
        go_pat atom)
      atoms;
    fprintf f "@]"
  in

  go_pat_set p

let pp_expr f =
  let open Format in
  let int_of_parens_ctx = function `Free -> 1 | `Apply -> 2 in
  let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2 in

  let rec go parens (_, _, e) =
    match e with
    | Var x -> pp_print_string f x
    | Tag (tag, payloads) ->
        fprintf f "@[<v 0>";
        let expr () =
          fprintf f "@[<hov 2>%s@ " tag;
          List.iteri
            (fun i p ->
              if i > 0 then fprintf f "@ ";
              go `Apply p)
            payloads;
          fprintf f "@]"
        in
        with_parens f (parens >> `Free) expr;
        fprintf f "@]"
    | Let ((_, _, x), rhs, body) ->
        fprintf f "@[<v 0>@[<hv 0>";
        let expr () =
          fprintf f "@[<hv 2>let %s =@ " x;
          go `Free rhs;
          fprintf f "@]@ in@]@,";
          go `Free body
        in
        with_parens f (parens >> `Free) expr;
        fprintf f "@]"
    | Clos ((_, _, x), e) ->
        fprintf f "@[<hov 2>\\%s ->@ " x;
        go `Apply e;
        fprintf f "@]"
    | Call (head, arg) ->
        fprintf f "@[<hov 2>";
        go `Apply head;
        fprintf f "@ ";
        go `Apply arg;
        fprintf f "@]"
  in
  go `Free

let pp_e_expr = pp_expr
let string_of_expr e = with_buffer (fun f -> pp_expr f e) default_width

let pp_def : Format.formatter -> e_def -> unit =
 fun f (_, _, def) ->
  let open Format in
  match def with
  | TyAlias ((_, x), args, (_, ty)) ->
      fprintf f "@[<hov 2>@[<hv 2>%s" x;
      let names = name_vars @@ List.map snd args @ [ ty ] in
      List.iter
        (fun (_, ty) ->
          fprintf f " ";
          pp_tvar names f ty)
        args;
      fprintf f "@]@ :@ ";
      pp_tvar names f ty;
      fprintf f "@]"
  | Sig ((_, x), ty) ->
      let names = name_vars [ snd ty ] in
      fprintf f "@[<hov 2>@[<hv 2>sig %s :@ " x;
      pp_tvar names f @@ snd ty;
      fprintf f "@]@]"
  | Def ((_, x), e) ->
      fprintf f "@[<hov 2>@[<hv 2>let %s =@ " x;
      pp_expr f e;
      fprintf f "@]@]"
  | Run ((_, x), e) ->
      fprintf f "@[<hov 2>@[<hv 2>run %s =@ " x;
      pp_expr f e;
      fprintf f "@]@]"

let pp_defs : Format.formatter -> e_def list -> unit =
 fun f defs ->
  let open Format in
  fprintf f "@[<v 0>";
  let rec go : e_def list -> unit = function
    | [] -> ()
    | [ def ] -> pp_def f def
    | ((_, _, Sig ((_, x), _)) as sig_)
      :: ((_, _, (Def ((_, y), _) | Run ((_, y), _))) :: _ as defs)
      when x = y ->
        pp_def f sig_;
        fprintf f "@,";
        go defs
    | def :: defs ->
        pp_def f def;
        fprintf f "@,@,";
        go defs
  in
  go defs;
  fprintf f "@]"

let string_of_program ?(width = default_width) (program : program) =
  with_buffer (fun f -> pp_defs f program) width
