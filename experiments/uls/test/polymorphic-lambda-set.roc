# cor +solve -elab

proto f a : a -> b -> () -> ( () -> () )
#     ^

proto g b : b -> ( () -> () )
#     ^

let f = \Fo -> \b -> \() -> g b
#   ^

let g = \Go -> \() -> ()
#   ^

entry main = f Fo Go () ()
#     ^^^^   ^

> cor-out +solve -elab
> 
> proto f a : a -> b -> () -> ( () -> () )
> #     ^ a -[[] + ~1:a:f]->
> #     ^   b -[[] + ~2:a:f]-> () -[[] + ~3:a:f]-> () -[[] + ~4:a:f]-> ()
> 
> proto g b : b -> ( () -> () )
> #     ^ b -[[] + ~1:b:g]-> () -[[] + ~2:b:g]-> ()
> 
> let f = \Fo -> \b -> \() -> g b
> #   ^ Fo -[[`5]]-> ?20 -[[`4]]-> () -[[`3]]-> () -[[] + ~2:?20:g]-> ()
> 
> let g = \Go -> \() -> ()
> #   ^ Go -[[`2]]-> () -[[`1]]-> ()
> 
> entry main = f Fo Go () ()
> #            ^ Fo -[[`5]]-> Go -[[`4]]-> () -[[`3]]-> () -[[] + ~2:*20:g]-> ()
> #     ^^^^ ()
> 