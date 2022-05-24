type lineco = int * int
(** line * col *)

let string_of_lineco (l, c) = string_of_int l ^ ":" ^ string_of_int c

type loc = lineco * lineco
(** start * end *)

let string_of_loc (l1, l2) = string_of_lineco l1 ^ "-" ^ string_of_lineco l2
let deeper (l1, c1) (l2, c2) = l1 > l2 || (l1 = l2 && c1 >= c2)
let shallower lc1 lc2 = deeper lc2 lc1
let within (lc11, lc12) (lc21, lc22) = deeper lc11 lc21 && shallower lc12 lc22

module type LANGUAGE = sig
  val name : string

  type program

  (*** Stages ***)

  val parse : string -> (program, string) result
  val solve : program -> (program, string) result

  (*** Emit ***)
  val print : ?width:int -> program -> string
  val type_at : loc -> program -> string option
end
