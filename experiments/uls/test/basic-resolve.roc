# cor +solve -elab
proto thunkDefault a : () -> () -> a
#     ^^^^^^^^^^^^

let thunkDefault = \() -> \() -> T1
#   ^^^^^^^^^^^^
let thunkDefault = \() -> \() -> T2
#   ^^^^^^^^^^^^

let test1 =
  let useT1 = \T1 -> () in
  useT1 (thunkDefault () ())
  #      ^^^^^^^^^^^^

let test2 =
  let useT2 = \T2 -> () in
  useT2 (thunkDefault () ())
  #      ^^^^^^^^^^^^

> cor-out +solve -elab
> proto thunkDefault a : () -> () -> a
> #     ^^^^^^^^^^^^ () -[~1:a:thunkDefault]-> () -[~2:a:thunkDefault]-> a
> 
> let thunkDefault = \() -> \() -> T1
> #   ^^^^^^^^^^^^ () -[[`6]]-> () -[[`5]]-> T1
> let thunkDefault = \() -> \() -> T2
> #   ^^^^^^^^^^^^ () -[[`4]]-> () -[[`3]]-> T2
> 
> let test1 =
>   let useT1 = \T1 -> () in
>   useT1 (thunkDefault () ())
> #        ^^^^^^^^^^^^ () -[[`6]]-> () -[[`5]]-> T1
> 
> let test2 =
>   let useT2 = \T2 -> () in
>   useT2 (thunkDefault () ())
> #        ^^^^^^^^^^^^ () -[[`4]]-> () -[[`3]]-> T2
> 