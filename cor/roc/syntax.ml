type lineco = int * int
(** line * col *)

type loc = lineco * lineco
(** start * end *)

type 't expr =
  | Int of int
  | Str of string
  | Var of string
  | Call of 't * 't * [ `Call | `DesugaredLet ]
  | Clos of (string * loc) list * 't
  | When of 't * 't branch list * [ `When | `DesugaredIf ]

and 't branch = 't expr * 't expr

type loc_expr = loc expr

let program = 
