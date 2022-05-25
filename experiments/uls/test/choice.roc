# cor +solve -elab
proto thunkDefault a : () -> () -> a
#     ^^^^^^^^^^^^

let thunkDefault = \() -> \() -> T1
#   ^^^^^^^^^^^^

let uut1 = \() -> \() -> T1
#   ^^^^

let useT1 = \T1 -> ()

let test1 =
  let f = choice {
      | thunkDefault
      | \() -> \() -> T1
  } in
  useT1 (f () ())
  #      ^

proto thunkDefault2 a : () -> () -> a

let thunkDefault2 = \() -> \() -> T1
#   ^^^^^^^^^^^^^

let test2 =
  let f = choice {
  #   ^
      | thunkDefault
      | thunkDefault2
  } in
  useT1 (f () ())
  #      ^

let test3 =
  let f = choice {
  #   ^
      | thunkDefault ()
      | thunkDefault2 ()
  } in
  useT1 (f ())
  #      ^

> cor-out +solve -elab
> proto thunkDefault a : () -> () -> a
> #     ^^^^^^^^^^^^ () -[~1:a:thunkDefault]-> () -[~2:a:thunkDefault]-> a
> 
> let thunkDefault = \() -> \() -> T1
> #   ^^^^^^^^^^^^ () -[[`9]]-> () -[[`8]]-> T1
> 
> let uut1 = \() -> \() -> T1
> #   ^^^^ () -[[`7]]-> () -[[`6]]-> T1
> 
> let useT1 = \T1 -> ()
> 
> let test1 =
>   let f = choice {
>       | thunkDefault
>       | \() -> \() -> T1
>   } in
>   useT1 (f () ())
> #        ^ () -[[`4,`9]]-> () -[[`3,`8]]-> T1
> 
> proto thunkDefault2 a : () -> () -> a
> 
> let thunkDefault2 = \() -> \() -> T1
> #   ^^^^^^^^^^^^^ () -[[`2]]-> () -[[`1]]-> T1
> 
> let test2 =
>   let f = choice {
> #     ^ () -[[] + ~1:?51:thunkDefault2 + ~1:?51:thunkDefault]->
>   () -[[] + ~2:?51:thunkDefault2 + ~2:?51:thunkDefault]-> ?51
>       | thunkDefault
>       | thunkDefault2
>   } in
>   useT1 (f () ())
> #        ^ () -[[`2,`9]]-> () -[[`1,`8]]-> T1
> 
> let test3 =
>   let f = choice {
> #     ^ () -[[] + ~2:?65:thunkDefault2 + ~2:?65:thunkDefault]-> ?65
>       | thunkDefault ()
>       | thunkDefault2 ()
>   } in
>   useT1 (f ())
> #        ^ () -[[`1,`8]]-> T1
> 