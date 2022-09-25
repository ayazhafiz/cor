# cor +solve -elab
let x = A in
let y = when x is
#   ^        ^
  | A -> F
  | B -> G
  | C -> H

in let x = A in
let y = when x is
#   ^        ^
  | A -> F
  | B -> G
  | _ -> H

in let x = A in
let y = when x is
#   ^        ^
  | A -> F
  | B -> G
  | x -> x
in y
