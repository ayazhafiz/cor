# cor +solve -elab
proto thunkDefault a : () -> () -> a

let thunkDefault = \() -> \() -> T1
#   ^^^^^^^^^^^^

proto thunkDefault2 a : () -> () -> a

let echoT1 = \T1 -> T1

let thunkDefault2 =
#   ^^^^^^^^^^^^^
    \() -> \() ->
        echoT1 (thunkDefault () ())
        #       ^^^^^^^^^^^^

let main = echoT1 (thunkDefault2 () ())
           #       ^^^^^^^^^^^^^

> cor-out +solve -elab
> proto thunkDefault a : () -> () -> a
> 
> let thunkDefault = \() -> \() -> T1
> #   ^^^^^^^^^^^^ () -[[`5]]-> () -[[`4]]-> T1
> 
> proto thunkDefault2 a : () -> () -> a
> 
> let echoT1 = \T1 -> T1
> 
> let thunkDefault2 =
> #   ^^^^^^^^^^^^^ () -[[`2]]-> () -[[`1]]-> T1
>     \() -> \() ->
>         echoT1 (thunkDefault () ())
> #               ^^^^^^^^^^^^ () -[[`5]]-> () -[[`4]]-> T1
> 
> let main = echoT1 (thunkDefault2 () ())
> #                  ^^^^^^^^^^^^^ () -[[`2]]-> () -[[`1]]-> T1
> 