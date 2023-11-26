open Util
open Language
open Symbol
open Type

type e_pat = loc * tvar * pat
(** An elaborated pattern *)

and pat = PTag of (loc * string) * e_pat list | PVar of loc_symbol

type kernelfn = [ `StrConcat | `Itos | `Add ]

let string_of_kernelfn : (kernelfn * string) list =
  [ (`StrConcat, "str_concat"); (`Add, "add"); (`Itos, "itos") ]

let kernelfn_of_string : (string * kernelfn) list =
  List.map (fun (a, b) -> (b, a)) string_of_kernelfn

type kernel_sig = {
  args : [ `Variadic of tvar | `List of tvar list ];
  ret : tvar;
}

let kernel_sig : kernelfn -> kernel_sig = function
  | `StrConcat -> { args = `Variadic tvar_str; ret = tvar_str }
  | `Add -> { args = `Variadic tvar_int; ret = tvar_int }
  | `Itos -> { args = `List [ tvar_int ]; ret = tvar_str }

type e_expr = loc * tvar * expr
(** An elaborated expression *)

and expr =
  | Var of symbol
  | Int of int
  | Str of string
  | Unit
  | Tag of string * e_expr list
  | Let of {
      recursive : bool ref;
      bind : loc * loc_tvar * symbol;
      expr : e_expr;
      body : e_expr;
    }
  | Clos of { arg : loc * loc_tvar * symbol; body : e_expr }
  | Call of e_expr * e_expr
  | KCall of kernelfn * e_expr list
  | When of e_expr * branch list

and branch = e_pat * e_expr

(** A top-level definition *)
type def =
  | TyAlias of loc_symbol * loc_tvar list * loc_tvar
  | Sig of loc_symbol * loc_tvar
  | Def of loc_symbol * e_expr
  | Run of loc_symbol * e_expr

type e_def = loc * tvar * def
(** An elaborated definition *)

type program = e_def list
type fresh_tvar = ty -> tvar
type parse_ctx = { fresh_tvar : fresh_tvar; symbols : Symbol.t }

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

let pp_symbol : Symbol.t -> Format.formatter -> symbol -> unit =
 fun symbols f s -> Format.pp_print_string f (Symbol.syn_of symbols s)

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
  with_buffer (fun f -> pp_tvar symbols [] names f tvar) width

type node_kind =
  [ `Def of symbol | `Var of symbol | `Alias of symbol | `Generic ]

type found_node = (loc * tvar * node_kind) option

let or_else o f = match o with Some a -> Some a | None -> f ()

let tightest_node_at_var : loc -> loc_tvar -> found_node =
 fun loc loc_ty ->
  let rec go_tag (_tag, args) : found_node = List.find_map go args
  and go (l, ty) : found_node =
    let deeper =
      match tvar_deref ty with
      | Link ty -> go (l, ty)
      | Unbd _ | ForA _ -> None
      | Content (TPrim (`Str | `Unit | `Int)) -> None
      | Content TTagEmpty -> None
      | Content (TTag { tags; ext }) ->
          let found_in_tag = List.find_map go_tag tags in
          or_else found_in_tag (fun () -> go ext)
      | Content (TFn (in', out)) -> or_else (go in') (fun () -> go out)
      | Alias { alias = (l_x, x), vars; real = _ } ->
          if within loc l_x then Some (l_x, ty, `Alias x)
          else List.find_map go vars
    in
    let surface () = if within loc l then Some (l, ty, `Generic) else None in
    or_else deeper surface
  in
  go loc_ty

let tightest_node_at_expr : loc -> e_expr -> found_node =
 fun loc program ->
  let rec pat (l, ty, p) : found_node =
    let deeper =
      match p with
      | PTag (_, args) -> List.find_map pat args
      | PVar (l, x) -> if within loc l then Some (l, ty, `Var x) else None
    in
    or_else deeper (fun () ->
        if within loc l then Some (l, ty, `Generic) else None)
  in
  let rec expr (l, ty, e) : found_node =
    let deeper =
      match e with
      | Var _ | Int _ | Str _ | Unit -> None
      | Let { recursive = _; bind = l, ty, x; expr = e1; body = e2 } ->
          if within loc l then Some (l, snd ty, `Def x)
          else or_else (expr e1) (fun () -> expr e2)
      | Tag (_, tags) -> List.find_map (fun tag -> expr tag) tags
      | Clos { arg = l, ty, x; body = e } ->
          if within loc l then Some (l, snd ty, `Var x) else expr e
      | Call (e1, e2) -> or_else (expr e1) (fun () -> expr e2)
      | KCall (_, es) -> List.find_map (fun e -> expr e) es
      | When (e, branches) ->
          let check_branch (pat', body) =
            or_else (pat pat') (fun () -> expr body)
          in
          or_else (expr e) (fun () -> List.find_map check_branch branches)
    in
    or_else deeper (fun () ->
        if within loc l then
          let kind = match e with Var x -> `Var x | _ -> `Generic in
          Some (l, ty, kind)
        else None)
  in
  expr program

let tightest_node_at_def : loc -> e_def -> found_node =
 fun loc (l, ty, def) ->
  let deeper =
    match def with
    | TyAlias ((l_x, x), vars, var) ->
        if within loc l_x then Some (l_x, ty, `Alias x)
        else
          or_else
            (List.find_map (tightest_node_at_var loc) vars)
            (fun () -> tightest_node_at_var loc var)
    | Sig ((l_x, x), var) ->
        if within loc l_x then Some (l_x, snd var, `Def x)
        else tightest_node_at_var loc var
    | Def ((l_x, x), e) | Run ((l_x, x), e) ->
        if within loc l_x then Some (l_x, ty, `Def x)
        else tightest_node_at_expr loc e
  in
  let surface () =
    if within loc l then
      let kind =
        match def with
        | TyAlias ((_, x), _, _) -> `Alias x
        | Sig ((_, x), _) | Def ((_, x), _) | Run ((_, x), _) -> `Def x
      in
      Some (l, ty, kind)
    else None
  in
  or_else deeper surface

let tightest_node_at_program : loc -> program -> found_node =
 fun loc program -> List.find_map (tightest_node_at_def loc) program

let type_at : loc -> program -> tvar option =
 fun loc program ->
  let found = tightest_node_at_program loc program in
  match found with Some (l, ty, _) when l = loc -> Some ty | _ -> None

let hover_info lineco program symbols =
  let open Printf in
  let wrap_code code = sprintf "```compose_fx\n%s\n```" code in
  let gen_docs (range, ty, kind) =
    let names = name_vars [ ty ] in
    let ty_str = string_of_tvar default_width symbols names ty in
    let split =
      if List.length @@ String.split_on_char '\n' ty_str > 0 then "\n" else " "
    in
    let prefix =
      match kind with
      | `Var x -> sprintf "(var) %s:%s" (Symbol.syn_of symbols x) split
      | `Def x -> sprintf "(def) %s:%s" (Symbol.syn_of symbols x) split
      | `Alias x -> sprintf "(alias) %s:%s" (Symbol.syn_of symbols x) split
      | `Generic -> ""
    in
    let ty_doc = prefix ^ ty_str in
    let md_docs = [ wrap_code ty_doc ] in
    { range; md_docs }
  in
  let node = tightest_node_at_program (lineco, lineco) program in
  Option.map gen_docs node

let with_parens f needs_parens inside =
  let open Format in
  if needs_parens then pp_print_string f "(";
  inside ();
  if needs_parens then pp_print_string f ")"

let pp_pat symbols f p =
  let open Format in
  let int_of_parens_ctx = function `Free -> 1 | `Apply -> 2 in
  let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2 in

  let rec go parens (_, _, atom) =
    match atom with
    | PTag ((_, t), atoms) ->
        fprintf f "@[<hov 2>";
        let printer () =
          fprintf f "%s" t;
          List.iteri
            (fun i p ->
              if i > 0 then fprintf f "@ ";
              go `Apply p)
            atoms
        in
        with_parens f (parens >> `Free) printer;
        fprintf f "@]"
    | PVar (_, x) -> pp_symbol symbols f x
  in
  go `Free p

let pp_expr symbols f =
  let open Format in
  let int_of_parens_ctx = function `Free -> 1 | `Apply -> 2 in
  let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2 in

  let rec go parens (_, _, e) =
    match e with
    | Var x -> pp_symbol symbols f x
    | Int i -> pp_print_int f i
    | Str s -> fprintf f "\"%s\"" (String.escaped s)
    | Unit -> pp_print_string f "{}"
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
    | Let { recursive = _; bind = _, _, x; expr = rhs; body } ->
        fprintf f "@[<v 0>@[<hv 0>";
        let expr () =
          fprintf f "@[<hv 2>let %a =@ " (pp_symbol symbols) x;
          go `Free rhs;
          fprintf f "@]@ in@]@,";
          go `Free body
        in
        with_parens f (parens >> `Free) expr;
        fprintf f "@]"
    | Clos { arg = _, _, x; body = e } ->
        fprintf f "@[<hov 2>\\%a ->@ " (pp_symbol symbols) x;
        go `Apply e;
        fprintf f "@]"
    | Call (head, arg) ->
        fprintf f "@[<hov 2>";
        go `Apply head;
        fprintf f "@ ";
        go `Apply arg;
        fprintf f "@]"
    | KCall (head, args) ->
        fprintf f "@[<hov 2>%s@ " (List.assoc head string_of_kernelfn);
        List.iteri
          (fun i arg ->
            if i > 0 then fprintf f "@ ";
            go `Apply arg)
          args;
        fprintf f "@]"
    | When (e, branches) ->
        fprintf f "@[<v 0>@[<hv 2>when@ ";
        go `Free e;
        fprintf f " is@]@ @[<hv 2>";
        List.iteri
          (fun i (pat, body) ->
            fprintf f "|@ %a ->@ " (pp_pat symbols) pat;
            go `Free body;
            if i < List.length branches - 1 then fprintf f "@ ")
          branches;
        fprintf f "@]@,@]"
  in
  go `Free

let pp_e_expr = pp_expr

let string_of_expr symbols e =
  with_buffer (fun f -> pp_expr symbols f e) default_width

let pp_def : Symbol.t -> Format.formatter -> e_def -> unit =
 fun symbols f (_, tvar, def) ->
  let open Format in
  match def with
  | TyAlias ((_, x), args, (_, ty)) ->
      fprintf f "@[<hov 2>@[<hv 2>%a" (pp_symbol symbols) x;
      let names = name_vars @@ List.map snd args @ [ ty ] in
      List.iter
        (fun (_, ty) ->
          fprintf f " ";
          pp_tvar symbols [] names f ty)
        args;
      fprintf f "@]@ :@ ";
      pp_tvar symbols [ tvar_v tvar ] names f ty;
      fprintf f "@]"
  | Sig ((_, x), ty) ->
      let names = name_vars [ snd ty ] in
      fprintf f "@[<hov 2>@[<hv 2>sig %a :@ " (pp_symbol symbols) x;
      pp_tvar symbols [] names f @@ snd ty;
      fprintf f "@]@]"
  | Def ((_, x), e) ->
      fprintf f "@[<hov 2>@[<hv 2>let %a =@ " (pp_symbol symbols) x;
      pp_expr symbols f e;
      fprintf f "@]@]"
  | Run ((_, x), e) ->
      fprintf f "@[<hov 2>@[<hv 2>run %a =@ " (pp_symbol symbols) x;
      pp_expr symbols f e;
      fprintf f "@]@]"

let pp_defs : Symbol.t -> Format.formatter -> e_def list -> unit =
 fun symbols f defs ->
  let open Format in
  fprintf f "@[<v 0>";
  let rec go : e_def list -> unit = function
    | [] -> ()
    | [ def ] -> pp_def symbols f def
    | ((_, _, Sig ((_, x), _)) as sig_)
      :: ((_, _, (Def ((_, y), _) | Run ((_, y), _))) :: _ as defs)
      when x = y ->
        pp_def symbols f sig_;
        fprintf f "@,";
        go defs
    | def :: defs ->
        pp_def symbols f def;
        fprintf f "@,@,";
        go defs
  in
  go defs;
  fprintf f "@]"

let string_of_program ?(width = default_width) (symbols : Symbol.t)
    (program : program) =
  with_buffer (fun f -> pp_defs symbols f program) width
