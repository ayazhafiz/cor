# cor +parse -print
# cor +parse -elab
proto thunkDefault a : () -> () -> a
#     ^^^^^^^^^^^^

let thunkDefault = \() -> \() -> T3
#   ^^^^^^^^^^^^
let thunkDefault = \() -> \() -> T2
#   ^^^^^^^^^^^^

let main =
  let useT1 = \T1 -> () in
  #   ^^^^^   ^^^^^^^^^
  useT1 (thunkDefault () ())

# cor-out +parse -print
proto thunkDefault a :
  () -[~2:a:thunkDefault]-> () -[~1:a:thunkDefault]-> a

let thunkDefault =
  \() -`F5-> \() -`F4-> T3

let thunkDefault =
  \() -`F3-> \() -`F2-> T2

let main =
  let useT1 = \T1 -`F1-> ()
  in useT1 (thunkDefault () ())

# cor-out +parse -elab
proto thunkDefault a : () -> () -> a
#     ^^^^^^^^^^^^ () -[~2:a:thunkDefault]-> () -[~1:a:thunkDefault]-> a

let thunkDefault = \() -> \() -> T3
#   ^^^^^^^^^^^^ ?11
let thunkDefault = \() -> \() -> T2
#   ^^^^^^^^^^^^ ?9

let main =
  let useT1 = \T1 -> () in
#             ^^^^^^^^^ ?6
#     ^^^^^ ?6
  useT1 (thunkDefault () ())
