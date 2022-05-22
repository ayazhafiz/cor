proto thunkDefault a : () -> () -> a

let thunkDefault = \() -> \() -> T1
let thunkDefault = \() -> \() -> T2

let main =
  let useT1 = \T1 -> () in
  useT1 (thunkDefault () ())
