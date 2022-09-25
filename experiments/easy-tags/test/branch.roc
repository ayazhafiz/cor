# cor +solve -elab
let y = \x -> when x is
#   ^
  | A -> F
  | B -> G
  | C -> H

in let y = \x -> when x is
#      ^
  | A -> F
  | B -> G
  | _ -> H

in let y = \x -> when x is
#      ^
  | A -> F
  | B -> G
  | x -> x
in y
