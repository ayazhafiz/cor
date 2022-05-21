open Util

type lineco = int * int
(** line * col *)

type loc = lineco * lineco
(** start * end *)

type loc_str = loc * string

type loc_expr = loc * expr

and expr =
  | Int of int
  | Var of string
  | Let of loc_str * loc_expr * loc_expr  (** x = e in b *)
  | LetRec of (loc_str * loc_expr) list * loc_expr
      (** x1 = e1 and ... and xn = en in b *)
  | Call of loc_expr * loc_expr list  (** fn args *)
  | Clos of loc_str list * loc_expr  (** args -> body *)
  | When of loc_expr * branch list

and branch = loc_expr * loc_expr

type parens_ctx = [ `Free | `CallHead | `CallArg ]

let int_of_parens_ctx = function `Free -> 1 | `CallHead -> 2 | `CallArg -> 3
let ( >> ) ctx1 ctx2 = int_of_parens_ctx ctx1 > int_of_parens_ctx ctx2

let pp_expr f =
  let open Format in
  let with_parens needs_parens inside =
    if needs_parens then pp_print_string f "(";
    inside ();
    if needs_parens then pp_print_string f ")"
  in
  let rec go parens (_, e) =
    match e with
    | Int n -> pp_print_int f n
    | Var x -> pp_print_string f x
    | Let ((_, x), rhs, body) ->
        fprintf f "@[<v 0>";
        let expr () =
          fprintf f "@[<hov 2>%s =@ " x;
          go `Free rhs;
          fprintf f "@]@,";
          go `Free body
        in
        with_parens (parens >> `Free) expr;
        fprintf f "@]"
    | LetRec (defs, body) ->
        fprintf f "@[<v 0>";
        let expr () =
          List.iteri
            (fun i ((_, x), expr) ->
              let prefix = if i > 0 then "and" else "" in
              fprintf f "@[<hov 2>%s%s =@ " prefix x;
              go `Free expr;
              fprintf f "@]@,";
              go `Free body)
            defs
        in
        with_parens (parens >> `Free) expr;
        fprintf f "@]"
    | Clos (args, body) ->
        fprintf f "@[<hov 2>\\";
        let expr () =
          List.iteri
            (fun i (_, x) ->
              let prefix = if i > 0 then ", " else "" in
              fprintf f "%s%s" prefix x)
            args;
          fprintf f "@ ->";
          go `Free body
        in
        with_parens (parens >> `Free) expr;
        fprintf f "@]"
  in
  go `Free

let string_of_expr ?(width = default_width) loc_expr =
  with_buffer (fun f -> pp_expr f loc_expr) width
