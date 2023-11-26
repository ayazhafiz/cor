type lineco = int * int [@@deriving show]
(** line * col *)

type loc = lineco * lineco [@@deriving show]
(** start * end *)

let noloc = ((0, 0), (0, 0))
