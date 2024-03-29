open Util
open Language

type lineco = int * int
(** line * col *)

type loc = lineco * lineco
(** start * end *)

let noloc = ((0, 0), (0, 0))

type loc_str = loc * string
type lambda = Lam of int

let string_of_lam (Lam n) = "`" ^ string_of_int n

type 'a uls = { region : int; ty : 'a; proto : string }
(** Unspecialized lambda set, like [~1:a:thunkDefault] *)

type loc_ty = loc * ty

and ty =
  | UVar of int  (** universally quantified type variable *)
  | TVar of tvar ref  (** non-quantified type variable *)
  | TVal of string  (** value-isomorphic type, e.g. TVal Unit for Val Unit *)
  | TLSet of lset  (** lambda set *)
  | TFn of loc_ty * ty * loc_ty  (** in, lambda set, out *)

and tvar = Unbd of int  (** unbound *) | Link of ty  (** resolved *)

and lset = {
  mutable solved : lambda list;  (** the lambda set we know *)
  mutable unspec : unspec ref list;
      (** lambda sets we're waiting to specialize *)
}

(** an unspecialized lambda set *)
and unspec =
  | Solved of lset
  | Pending of ty uls
      (** instantiated unspecialized lambda set we're waiting to solve *)

(** compacts a lambda set's specialized variable lists *)
let rec compact_lset lset =
  let rec part = function
    | [] -> ([], [])
    | unspec :: rest -> (
        let rest_extra_solved, rest_new_unspec = part rest in
        match !unspec with
        | Pending _ -> (rest_extra_solved, unspec :: rest_new_unspec)
        | Solved lset ->
            compact_lset lset;
            (lset.solved @ rest_extra_solved, lset.unspec @ rest_new_unspec))
  in
  let extra_solved, new_unspec = part lset.unspec in
  lset.solved <- List.sort_uniq compare (lset.solved @ extra_solved);
  lset.unspec <- List.sort_uniq compare new_unspec

type e_pat = loc * ty * pat
(** An elaborated pattern *)

and pat = PVar of string | PVal of string

type e_expr = loc * ty * expr
(** An elaborated expression *)

and expr =
  | Val of string
  | Var of string
  | Let of loc_str * e_expr * e_expr  (** x = e in b *)
  | Call of e_expr * e_expr  (** fn arg *)
  | Clos of e_pat * lambda * e_expr  (** arg -name-> body *)
  | Choice of e_expr list

and branch = e_pat * e_expr

and def =
  | Proto of loc_str * (int * string) * loc_ty
  | Def of loc_str * e_expr * bool (* name * body * is entry *)

type program = def list
type parse_ctx = { fresh_var : unit -> int; fresh_clos_name : unit -> int }

(* extractions *)
let xloc (l, _, _) = l
let xty (_, t, _) = t
let xv (_, _, v) = v

let pp_lambda_set f solved =
  let open Format in
  fprintf f "[%s]" (String.concat "," (List.map string_of_lam solved))

let pp_uls f print_ty p =
  let open Format in
  fprintf f "~%d:" p.region;
  print_ty p.ty;
  fprintf f ":%s" p.proto

let rec pp_unspec tctx f = function
  | Solved solved -> pp_lset tctx f solved
  | Pending lset -> pp_uls f (fun ty -> pp_ty tctx f (noloc, ty)) lset

and pp_lset tctx f lset =
  let open Format in
  compact_lset lset;
  let { solved; unspec } = lset in
  pp_lambda_set f solved;
  List.iter
    (fun unspec ->
      fprintf f " + ";
      pp_unspec tctx f !unspec)
    unspec

and pp_ty ?(print_uls = true) tctx f =
  let open Format in
  let int_of_parens_ctx = function `Free -> 1 | `FnHead -> 2 in
  let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2 in

  let with_parens needs_parens inside =
    if needs_parens then pp_print_string f "(";
    inside ();
    if needs_parens then pp_print_string f ")"
  in
  let rec go parens (_, t) =
    match t with
    | UVar n -> (
        match List.assoc_opt n tctx with
        | Some v -> pp_print_string f v
        | None -> fprintf f "*%d" n)
    | TVar v -> (
        match !v with
        | Unbd i -> fprintf f "?%d" i
        | Link t -> go parens (noloc, t))
    | TVal "Unit" -> pp_print_string f "()"
    | TVal v -> pp_print_string f v
    | TLSet lset -> pp_lset tctx f lset
    | TFn (l, set, r) ->
        fprintf f "@[<hov 2>";
        let pty () =
          go `FnHead l;
          if print_uls then (
            fprintf f " -[";
            go `Free (noloc, set);
            fprintf f "]->@ ")
          else fprintf f " ->@ ";
          go `Free r
        in
        with_parens (parens >> `Free) pty;
        fprintf f "@]"
  in
  go `Free

let string_of_ty width tctx ty =
  with_buffer (fun f -> pp_ty tctx f (noloc, ty)) width

let tightest_node_at loc program =
  let or_else o f = match o with Some a -> Some a | None -> f () in
  let pat (l, ty, _) =
    if within loc l then Some (l, [], ty, `Generic) else None
  in
  let rec expr (l, ty, e) =
    let deeper =
      match e with
      | Val _ | Var _ -> None
      | Let ((l, x), e1, e2) ->
          if within loc l then Some (l, [], xty e1, `Def x)
          else or_else (expr e1) (fun () -> expr e2)
      | Call (e1, e2) -> or_else (expr e1) (fun () -> expr e2)
      | Clos (p, _, e) -> or_else (pat p) (fun () -> expr e)
      | Choice branches ->
          List.fold_left
            (fun res e -> or_else res (fun () -> expr e))
            None branches
    in
    or_else deeper (fun () ->
        if within loc l then
          let kind = match e with Var x -> `Var x | _ -> `Generic in
          Some (l, [], ty, kind)
        else None)
  in
  let def = function
    | Proto ((l, x), arg, (_, ty)) ->
        if within loc l then Some (l, [ arg ], ty, `Proto x) else None
    | Def ((l, x), e, is_entry) ->
        if within loc l then
          let kind = if is_entry then `Entry x else `Def x in
          Some (l, [], xty e, kind)
        else expr e
  in
  List.find_map def program

let type_at loc program =
  match tightest_node_at loc program with
  | Some (l, tctx, ty, _) when l = loc -> Some (tctx, ty)
  | _ -> None

let hover_info lineco program =
  let open Printf in
  let wrap_code code = sprintf "```uls\n%s\n```" code in
  let gen_docs (range, tctx, ty, kind) =
    let ty_str = string_of_ty default_width tctx ty in
    let prefix =
      match kind with
      | `Var x -> sprintf "(var) %s: " x
      | `Def x -> sprintf "(def) %s: " x
      | `Entry x -> sprintf "(entry) %s: " x
      | `Proto x -> sprintf "(proto) %s: " x
      | `Generic -> ""
    in
    let ty_doc = prefix ^ ty_str in
    let md_docs = [ wrap_code ty_doc ] in
    { range; md_docs }
  in
  let node = tightest_node_at (lineco, lineco) program in
  Option.map gen_docs node

let string_of_lambda = function Lam n -> "`" ^ string_of_int n

let pp_pat f (_, _, p) =
  let open Format in
  match p with
  | PVar x -> pp_print_string f x
  | PVal "Unit" -> pp_print_string f "()"
  | PVal v -> pp_print_string f v

let pp_expr f =
  let open Format in
  let int_of_parens_ctx = function
    | `Free -> 1
    | `CallHead -> 2
    | `CallArg -> 3
  in
  let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2 in

  let with_parens needs_parens inside =
    if needs_parens then pp_print_string f "(";
    inside ();
    if needs_parens then pp_print_string f ")"
  in
  let rec go parens (_, _, e) =
    match e with
    | Val "Unit" -> pp_print_string f "()"
    | Val v -> pp_print_string f v
    | Var x -> pp_print_string f x
    | Let ((_, x), rhs, body) ->
        fprintf f "@[<v 0>";
        let expr () =
          fprintf f "@[<hov 2>let %s =@ " x;
          go `Free rhs;
          fprintf f "@]@,@[<hov 2>in@ ";
          go `Free body;
          fprintf f "@]"
        in
        with_parens (parens >> `Free) expr;
        fprintf f "@]"
    | Call (head, arg) ->
        fprintf f "@[<hov 2>";
        let expr () =
          go `CallHead head;
          fprintf f "@ ";
          go `CallArg arg
        in
        with_parens (parens >> `CallHead) expr;
        fprintf f "@]"
    | Clos (arg, _lam, body) ->
        fprintf f "@[<hov 2>";
        let expr () =
          fprintf f "\\";
          pp_pat f arg;
          fprintf f " ->@ ";
          go `Free body
        in
        with_parens (parens >> `Free) expr;
        fprintf f "@]"
    | Choice branches ->
        fprintf f "@[<v 2>choice {";
        List.iter
          (fun expr ->
            fprintf f "@ @[| ";
            go `Free expr;
            fprintf f "@]")
          branches;
        fprintf f " }@]"
  in
  go `Free

let string_of_expr e = with_buffer (fun f -> pp_expr f e) default_width

let pp_decl f =
  let open Format in
  function
  | Proto (name, arg, ty) ->
      fprintf f "@[<v 2>proto %s %s :@ " (snd name) (snd arg);
      pp_ty ~print_uls:false [ arg ] f ty;
      fprintf f "@]"
  | Def (name, e, entry) ->
      let prefix = if entry then "entry" else "let" in
      fprintf f "@[<v 2>%s %s =@ " prefix (snd name);
      pp_expr f e;
      fprintf f "@]"

let string_of_program ?(width = default_width) (program : program) =
  let open Format in
  with_buffer
    (fun f ->
      fprintf f "@[<v 0>";
      List.iteri
        (fun i d ->
          if i <> 0 then fprintf f "@,@,";
          pp_decl f d)
        program;
      fprintf f "@]")
    width
