# cor +solve -elab
# cor +mono -print
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

> cor-out +mono -print
> let `4~1 =
>   \() -> T1
> 
> let `5(thunkDefault)~1 =
>   \() -> `4~1
> 
> let `4~2 =
>   \() -> T1
> 
> let `3(echoT1)~1 =
>   \T1 -> T1
> 
> let `4~3 =
>   \() -> T1
> 
> let `5(thunkDefault)~2 =
>   \() -> `4~3
> 
> let `3(echoT1)~2 =
>   \T1 -> T1
> 
> let `1~1 =
>   \() -> `3(echoT1)~2 (`5(thunkDefault)~2 () ())
> 
> let `2(thunkDefault2)~1 =
>   \() -> `1~1
> 
> let `4~4 =
>   \() -> T1
> 
> let `5(thunkDefault)~3 =
>   \() -> `4~4
> 
> let `3(echoT1)~3 =
>   \T1 -> T1
> 
> let `1~2 =
>   \() -> `3(echoT1)~3 (`5(thunkDefault)~3 () ())
> 
> let `4~5 =
>   \() -> T1
> 
> let `5(thunkDefault)~4 =
>   \() -> `4~5
> 
> let `3(echoT1)~4 =
>   \T1 -> T1
> 
> let `1~3 =
>   \() -> `3(echoT1)~4 (`5(thunkDefault)~4 () ())
> 
> let `2(thunkDefault2)~2 =
>   \() -> `1~3
> 
> let `3(echoT1)~5 =
>   \T1 -> T1
> 
> let main~1 =
>   `3(echoT1)~5 (`2(thunkDefault2)~2 () ())