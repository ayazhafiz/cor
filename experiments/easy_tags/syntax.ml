open Util
open Language

type lineco = int * int
(** line * col *)

type loc = lineco * lineco
(** start * end *)

let noloc = ((0, 0), (0, 0))

type loc_str = loc * string

type tag = string * ty list

and ty_content =
  | TTag of { tags : tag list; ext : ty }  (** Concrete type content *)
  | TFn of ty * ty
  | TTagEmpty

and tvar =
  | Unbd of int
  | Link of ty
  | ForA of int * string option  (** generalized type *)
  | Content of ty_content  (** Link of a type *)

and ty = tvar ref [@@deriving show]
(** Mutable type cell *)

let rec unlink ty = match !ty with Link t -> unlink t | _ -> ty

let chase_tags tags ext =
  let rec go all_tags ext =
    match !(unlink ext) with
    | Link _ -> failwith "unreachable"
    | Unbd _ -> (all_tags, ext)
    | ForA _ -> (all_tags, ext)
    | Content TTagEmpty -> (all_tags, ext)
    | Content (TTag { tags; ext }) -> go (all_tags @ tags) ext
    | Content (TFn _) -> failwith "not a tag"
  in
  go tags ext

type e_pat = loc * ty * pat
(** An elaborated pattern *)

and pat = PTag of loc_str * e_pat list | PVar of string | PWild

type pat_set = loc * ty * e_pat list

type e_expr = loc * ty * expr
(** An elaborated expression *)

and expr =
  | Var of string
  | Tag of string * e_expr list
  | Let of (loc * ty * string) * e_expr * e_expr  (** let x = e in b *)
  | When of e_expr * branch list  (** when x is ... *)
  | Clos of (loc * ty * string) * e_expr
  | Call of e_expr * e_expr

and branch = pat_set * e_expr

type program = e_expr
type fresh_var = unit -> ty
type parse_ctx = { fresh_var : fresh_var }

(* extractions *)
let xloc (l, _, _) = l
let xty (_, t, _) = t
let xv (_, _, v) = v

let is_empty_tag t =
  match !(unlink t) with
  | Content (TTag { tags = []; _ }) | Content TTagEmpty -> true
  | _ -> false

(* name *)

let preprocess tys =
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
  let rec go_ty t =
    match !t with
    | ForA (i, Some name) -> replace claimed i name
    | ForA (i, None) -> update hits i (fun h -> h + 1) 1
    | Unbd _ -> ()
    | Link t -> go_ty t
    | Content TTagEmpty -> ()
    | Content (TTag { tags; ext }) ->
        List.iter (fun (_, args) -> List.iter go_ty args) tags;
        go_ty ext
    | Content (TFn (in', out')) ->
        go_ty in';
        go_ty out'
  in
  List.iter go_ty tys;
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

let name_vars tys =
  let claimed, hits = preprocess tys in
  let fresh_name = fresh_name_generator () in
  let names' =
    List.map (fun (i, name) -> (i, fresh_name (Some name))) claimed
  in
  let names'' =
    List.map
      (fun (i, hits) ->
        let name = if hits == 1 then "*" else fresh_name None in
        (i, name))
      hits
  in
  names' @ names''

(* format *)

type named_vars = (int * string) list

let pp_ty (names : named_vars) f t =
  let open Format in
  let wild t =
    match !(unlink t) with
    | ForA (i, _) -> List.assoc i names == "*"
    | _ -> false
  in
  let rec go_tag mode pol (tag_name, payloads) =
    fprintf f "%s" tag_name;
    List.iter
      (fun p ->
        fprintf f "@ ";
        go mode pol p)
      payloads
  and go mode pol t =
    match !t with
    | Unbd i -> fprintf f "<?%d>" i
    | ForA (i, _) ->
        let name =
          List.assoc_opt i names
          |> Option.value ~default:(Printf.sprintf "<'%d>" i)
        in
        pp_print_string f name
    | Link t -> go mode pol t
    | Content TTagEmpty -> fprintf f "[]"
    | Content (TTag { tags; ext }) ->
        let tags, ext = chase_tags tags ext in
        fprintf f "@[<hov 2>[";
        List.iteri
          (fun i t ->
            if i > 0 then fprintf f ",@ ";
            go_tag mode pol t)
          tags;
        fprintf f "]";
        let print_ext () = go mode pol ext in
        (if not (is_empty_tag ext) then
         match (mode, pol) with
         | `Roc, _ -> print_ext ()
         | `New, `Neg -> print_ext ()
         | `New, `Pos when not (wild ext) -> print_ext ()
         | `New, `Pos -> ());
        fprintf f "@]"
    | Content (TFn (in', out)) ->
        fprintf f "@[<hov 2>";
        go mode `Neg in';
        fprintf f "@ -> ";
        go mode `Pos out;
        fprintf f "@]"
  in
  let modes = [ `Roc; `New ] in
  let mode_pre = function `Roc -> "-" | `New -> "+" in
  fprintf f "@[<v 0>";
  List.iteri
    (fun i mode ->
      if i <> 0 then fprintf f "@,";
      fprintf f "%s " (mode_pre mode);
      go mode `Pos t)
    modes;
  fprintf f "@]"

let string_of_ty width names ty = with_buffer (fun f -> pp_ty names f ty) width

let tightest_node_at loc program =
  let or_else o f = match o with Some a -> Some a | None -> f () in
  let rec pat (l, ty, p) =
    let deeper =
      match p with
      | PWild -> None
      | PVar _ -> None
      | PTag (_, args) -> List.find_map pat args
    in
    or_else deeper (fun () -> if within loc l then Some (l, ty, `Pat) else None)
  in
  let pat_set ((l, ty, pats) : pat_set) =
    let deeper = List.find_map pat pats in
    or_else deeper (fun () -> if within loc l then Some (l, ty, `Pat) else None)
  in
  let rec expr (l, ty, e) =
    let deeper =
      match e with
      | Var _ -> None
      | Let ((l, ty, x), e1, e2) ->
          if within loc l then Some (l, ty, `Def x)
          else or_else (expr e1) (fun () -> expr e2)
      | Tag (_, tags) -> List.find_map (fun tag -> expr tag) tags
      | When (e, branches) ->
          let check_branch (pat', body) =
            or_else (pat_set pat') (fun () -> expr body)
          in
          or_else (expr e) (fun () -> List.find_map check_branch branches)
      | Clos ((l, ty, x), e) ->
          if within loc l then Some (l, ty, `Var x) else expr e
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
    let ty_str = string_of_ty default_width names ty in
    let prefix =
      match kind with
      | `Var x -> sprintf "(var) %s: " x
      | `Def x -> sprintf "(def) %s: " x
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
  let int_of_parens_ctx = function `Free -> 1 | `Apply -> 2 in
  let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2 in

  let rec go_pat parens (_, _, atom) =
    match atom with
    | PTag ((_, t), atoms) ->
        fprintf f "@[<hov 2>";
        let printer () =
          fprintf f "%s" t;
          List.iteri
            (fun i p ->
              if i > 0 then fprintf f "@ ";
              go_pat `Apply p)
            atoms
        in
        with_parens f (parens >> `Free) printer;
        fprintf f "@]"
    | PWild -> fprintf f "_"
    | PVar x -> fprintf f "%s" x
  and go_pat_set parens atoms =
    fprintf f "@[<hov 2>";
    List.iteri
      (fun i atom ->
        if i > 0 then fprintf f "@ | ";
        go_pat parens atom)
      atoms;
    fprintf f "@]"
  in

  go_pat_set `Free p

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
          fprintf f "@[<hov 2>%s" tag;
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
    | When (cond, branches) ->
        fprintf f "@[<v 2>@[<hov 2>when@ ";
        go `Free cond;
        fprintf f " is@]";
        List.iter
          (fun (pat, body) ->
            fprintf f "@,@[<hov 0>| ";
            pp_pat f pat;
            fprintf f "@ -> ";
            go `Free body;
            fprintf f "@]")
          branches;
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

let string_of_program ?(width = default_width) (program : program) =
  let open Format in
  with_buffer
    (fun f ->
      fprintf f "@[<v 0>";
      pp_expr f program;
      fprintf f "@]")
    width
