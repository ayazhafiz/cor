open Util

type lineco = int * int
(** line * col *)

type loc = lineco * lineco
(** start * end *)

let noloc = ((0, 0), (0, 0))

type loc_str = loc * string

type loc_pat = loc * pat
and pat = PVar of string | PVal of string

type lambda = Lam of int

type loc_ty = loc * ty

and ty =
  | UVar of int  (** universally quantified type variable *)
  | TVar of tvar ref  (** non-quantified type variable *)
  | TVal of string  (** value-isomorphic type, e.g. TVal Unit for Val Unit *)
  | TLSet of lambda list  (** lambda set *)
  | TUls of { region : int; var : ty; proto : string }
      (** unspecialized lambda set var in a prototype
      for example,

      proto thunkDefault a : () -> () -> a

      has the ULS vars

      proto thunkDefault a : () -[ ~1:a:thunkDefault ]-> () -[ ~2:a:thunkDefault ]-> a

      during solving or mono, when a is resolved, we also decide if these
      are resolved.

      IDEAS:
      - deciding when to do the resolution seems tricky. after each
        unification?
      - maybe keep a lookaside table of unbound types "a"->ULS? when "a"
        is solved, check all reached ULS
  *)
  | TFn of loc_ty * ty * loc_ty  (** in, lambda set, out *)

and tvar = Unbd of int  (** unbound *) | Subt of ty  (** substituted *)

type loc_expr = loc * expr

and expr =
  | Val of string
  | Var of string
  | Let of loc_str * loc_expr * loc_expr  (** x = e in b *)
  | Call of loc_expr * loc_expr  (** fn arg *)
  | Clos of loc_pat * lambda * loc_expr  (** args -name-> body *)
  | Choice of branch list

and branch = loc_pat * loc_expr

and def =
  | Proto of loc_str * (int * string) * loc_ty
  | Def of loc_str * loc_expr

type program = def list
type parse_ctx = { fresh_var : unit -> int; fresh_clos_name : unit -> int }

let string_of_lambda = function Lam n -> "`F" ^ string_of_int n

let pp_pat f (_, p) =
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
  let rec go parens (_, e) =
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
    | Clos (arg, lam, body) ->
        fprintf f "@[<hov 2>";
        let expr () =
          fprintf f "\\";
          pp_pat f arg;
          fprintf f " -%s->@ " (string_of_lambda lam);
          go `Free body
        in
        with_parens (parens >> `Free) expr;
        fprintf f "@]"
    | Choice branches ->
        fprintf f "@[<v 2>choice@ ";
        List.iter
          (fun (pat, expr) ->
            fprintf f "@[<hov 2>";
            pp_pat f pat;
            fprintf f " ->@ ";
            go `Free expr;
            fprintf f "@]")
          branches;
        fprintf f "@]"
  in
  go `Free

let pp_ty tctx f =
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
        | Subt t -> go parens (noloc, t))
    | TVal "Unit" -> pp_print_string f "()"
    | TVal v -> pp_print_string f v
    | TLSet set ->
        fprintf f "[%s]"
          (String.concat ","
             (List.map (function Lam n -> "`" ^ string_of_int n) set))
    | TUls { region; var; proto } ->
        fprintf f "~%d:" region;
        go `FnHead (noloc, var);
        fprintf f ":%s" proto
    | TFn (l, set, r) ->
        fprintf f "@[<hov 2>";
        let pty () =
          go `FnHead l;
          fprintf f " -[";
          go `Free (noloc, set);
          fprintf f "]->@ ";
          go `Free r
        in
        with_parens (parens >> `Free) pty;
        fprintf f "@]"
  in
  go `Free

let pp_decl f =
  let open Format in
  function
  | Proto (name, arg, ty) ->
      fprintf f "@[<v 2>proto %s %s :@ " (snd name) (snd arg);
      pp_ty [ arg ] f ty;
      fprintf f "@]"
  | Def (name, e) ->
      fprintf f "@[<v 2>let %s =@ " (snd name);
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
