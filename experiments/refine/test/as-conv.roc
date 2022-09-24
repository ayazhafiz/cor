# cor +mono -print
# cor +eval -print
let x : [B, C, D, E] = C in
when x is
  | B | C as y -> y
  | D | E -> A
