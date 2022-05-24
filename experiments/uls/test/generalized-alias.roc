# cor +solve -elab
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