# cor +solve -elab
# cor +mono -print
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

> cor-out +mono -print
> let `5~1 =
>   \() -> T1
> 
> let `6(thunkDefault)~1 =
>   \() -> `5~1
> 
> let `5~2 =
>   \() -> T1
> 
> let `3~1 =
>   \() -> T2
> 
> let `4(thunkDefault)~1 =
>   \() -> `3~1
> 
> let `3~2 =
>   \() -> T2
> 
> let `5~3 =
>   \() -> T1
> 
> let `6(thunkDefault)~2 =
>   \() -> `5~3
> 
> let `2~1 =
>   \T1 -> ()
> 
> let test1~1 =
>   `2~1 (`6(thunkDefault)~2 () ())
> 
> let `2~2 =
>   \T1 -> ()
> 
> let `3~3 =
>   \() -> T2
> 
> let `4(thunkDefault)~2 =
>   \() -> `3~3
> 
> let `1~1 =
>   \T2 -> ()
> 
> let test2~1 =
>   `1~1 (`4(thunkDefault)~2 () ())
> 
> let `1~2 =
>   \T2 -> ()