# cor +parse -print
proto thunkDefault a : () -> () -> a

let thunkDefault = \() -> \() -> T1
let thunkDefault = \() -> \() -> T2

let main =
  let useT1 = \T1 -> () in
  useT1 (thunkDefault () ())

# cor-out +parse -print
proto thunkDefault a :
  () -[~2:a:thunkDefault]-> () -[~1:a:thunkDefault]-> a

let thunkDefault =
  \() -`F5-> \() -`F4-> T1

let thunkDefault =
  \() -`F3-> \() -`F2-> T2

let main =
  let useT1 = \T1 -`F1-> ()
  in useT1 (thunkDefault () ())