module type LANGUAGE = sig
  val name : string

  type program

  (*** Stages ***)

  val parse : string -> (program, string) result

  (*** Emit ***)
  val print : ?width:int -> program -> string
end
