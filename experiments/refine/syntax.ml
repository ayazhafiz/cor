open Util
open Language

type lineco = int * int
(** line * col *)

type loc = lineco * lineco
(** start * end *)

let noloc = ((0, 0), (0, 0))

type loc_str = loc * string

type tag = string * ty list
and ty_content = TTag of tag list  (** Concrete type content *)

and tvar =
  | Unbd of int
  | Link of ty
  | Content of ty_content  (** Link of a type *)

and ty = tvar ref [@@deriving show]
(** Mutable type cell *)

let rec unlink ty = match !ty with Link t -> unlink t | _ -> ty

type e_pat = loc * ty * pat
(** An elaborated pattern *)

and pat =
  | PAtom of loc_pat_atom list
  | PAs of loc_pat_atom list * (loc * ty * string)  (** top-level pattern *)

and loc_pat_atom = loc * ty * pat_atom

and pat_atom =
  | PTag of loc_str * loc_pat_atom list
  | PWild  (** pattern case *)

type e_expr = loc * ty * expr
(** An elaborated expression *)

and expr =
  | Var of string
  | Tag of string * e_expr list
  | Let of (loc * ty * string) * e_expr * e_expr  (** let x = e in b *)
  | When of e_expr * branch list  (** when x is ... *)

and branch = e_pat * e_expr

type program = e_expr
type parse_ctx = { fresh_var : unit -> int }

(* extractions *)
let xloc (l, _, _) = l
let xty (_, t, _) = t

let xv (_, _, v) = v

and pp_ty f =
  let open Format in
  let rec go_tag (tag_name, payloads) =
    fprintf f "%s" tag_name;
    List.iter
      (fun p ->
        fprintf f "@ ";
        go p)
      payloads
  and go t =
    match !t with
    | Unbd i -> fprintf f "'%d" i
    | Link t -> go t
    | Content (TTag tags) ->
        fprintf f "@[<hov 2>[";
        List.iteri
          (fun i t ->
            if i > 0 then fprintf f ",@ ";
            go_tag t)
          tags;
        fprintf f "]@]"
  in
  go

let string_of_ty width ty = with_buffer (fun f -> pp_ty f ty) width

let tightest_node_at loc program =
  let or_else o f = match o with Some a -> Some a | None -> f () in
  let rec atom (l, ty, p) =
    let deeper =
      match p with PWild -> None | PTag (_, args) -> List.find_map atom args
    in
    or_else deeper (fun () -> if within loc l then Some (l, ty, `Pat) else None)
  in
  let pat (l, ty, p) =
    let deeper =
      match p with
      | PAtom atoms -> List.find_map atom atoms
      | PAs (atoms, (l, ty, x)) ->
          if within loc l then Some (l, ty, `Var x)
          else List.find_map atom atoms
    in
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

let type_at loc program =
  match tightest_node_at loc program with
  | Some (l, ty, _) when l = loc -> Some ty
  | _ -> None

let hover_info lineco program =
  let open Printf in
  let wrap_code code = sprintf "```refine\n%s\n```" code in
  let gen_docs (range, ty, kind) =
    let ty_str = string_of_ty default_width ty in
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

  let rec go_atom parens (_, _, atom) =
    match atom with
    | PTag ((_, t), atoms) ->
        fprintf f "@[<hov 2>";
        let printer () =
          fprintf f "%s" t;
          List.iteri
            (fun i p ->
              if i > 0 then fprintf f "@ ";
              go_atom `Apply p)
            atoms
        in
        with_parens f (parens >> `Free) printer;
        fprintf f "@]"
    | PWild -> fprintf f "_"
  and go_atoms parens atoms =
    fprintf f "@[<hov 2>";
    List.iteri
      (fun i atom ->
        if i > 0 then fprintf f "@ | ";
        go_atom parens atom)
      atoms;
    fprintf f "@]"
  in

  match p with
  | PAtom atoms -> go_atoms `Free atoms
  | PAs (atoms, (_, _, v)) ->
      go_atoms `Free atoms;
      fprintf f "@ as %s" v

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
