# cor +solve -elab
# cor +mono -print
proto thunkDefault a : () -> () -> a
#     ^^^^^^^^^^^^

let thunkDefault = \() -> \() -> T1
#   ^^^^^^^^^^^^

let useT1 = \T1 -> ()

let test =
  let alias = thunkDefault in
  #   ^^^^^
  useT1 (alias () ())
  #      ^^^^^

let test2 =
  let alias = thunkDefault () in
  useT1 (alias ())
  #      ^^^^^

let test3 =
  let alias = thunkDefault () in
  let alias2 = alias in
  useT1 (alias2 ())
  #      ^^^^^^

> cor-out +solve -elab
> proto thunkDefault a : () -> () -> a
> #     ^^^^^^^^^^^^ () -[~1:a:thunkDefault]-> () -[~2:a:thunkDefault]-> a
> 
> let thunkDefault = \() -> \() -> T1
> #   ^^^^^^^^^^^^ () -[[`3]]-> () -[[`2]]-> T1
> 
> let useT1 = \T1 -> ()
> 
> let test =
>   let alias = thunkDefault in
> #     ^^^^^ () -[[] + ~1:?29:thunkDefault]-> () -[[] + ~2:?29:thunkDefault]-> ?29
>   useT1 (alias () ())
> #        ^^^^^ () -[[`3]]-> () -[[`2]]-> T1
> 
> let test2 =
>   let alias = thunkDefault () in
>   useT1 (alias ())
> #        ^^^^^ () -[[`2]]-> T1
> 
> let test3 =
>   let alias = thunkDefault () in
>   let alias2 = alias in
>   useT1 (alias2 ())
> #        ^^^^^^ () -[[`2]]-> T1
> 

> cor-out +mono -print
> let `2~1 =
>   \() -> T1
> 
> let `3(thunkDefault)~1 =
>   \() -> `2~1
> 
> let `2~2 =
>   \() -> T1
> 
> let `1(useT1)~1 =
>   \T1 -> ()
> 
> let `2~3 =
>   \() -> T1
> 
> let `3(thunkDefault)~2 =
>   \() -> `2~3
> 
> let `1(useT1)~2 =
>   \T1 -> ()
> 
> let test~1 =
>   `1(useT1)~2 (`3(thunkDefault)~2 () ())
> 
> let `2~4 =
>   \() -> T1
> 
> let `1(useT1)~3 =
>   \T1 -> ()
> 
> let test2~1 =
>   `1(useT1)~3 (`2~4 ())
> 
> let `2~5 =
>   \() -> T1
> 
> let `1(useT1)~4 =
>   \T1 -> ()
> 
> let test3~1 =
>   `1(useT1)~4 (`2~5 ())