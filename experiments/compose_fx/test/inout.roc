# cor +parse -print
# Task.roc
Task v op : (v -> op) -> op

sig await : Task a op -> (a -> Task b op) -> Task b op
let await = \fromResult -> \next ->
    \continue ->
        fromResult (\result ->
            let inner = next result in
            inner continue)
;;

# StdinEffect.roc
OpIn a b : [
    StdinLine (Str -> OpIn a b),
    Done a,
]b

# Stdin.roc
sig lineIn : Task Str (OpIn * *)
let lineIn = \toNext -> StdinLine (\s -> toNext s)
;;

# StdoutEffect.roc
OpOut a b : [
    StdoutLine Str (Unit -> OpOut a b),
    Done a,
]b

# Stdout.roc
sig lineOut : Str -> Task Unit (OpOut * *)
let lineOut = \s -> (\toNext -> StdoutLine s (\x -> toNext x))
;;

# Platform
# really, we want a syntax like [Done a](OpIn a)(OpOut a) here
Op a : [
    StdinLine (Str -> Op a),
    StdoutLine Str (Unit -> Op a),
    Done a,
]

sig main : Task Unit (Op *)
run main = await lineIn (\s -> lineOut s)
;;

> cor-out +parse -print
> 
> 
> Task v op : (<'104> -> <'105>) -> <'106>
> 
> sig await :
>   (Task <'94> <'93>)
>     -> (<'96> -> Task <'98> <'97>)
>          -> Task <'101> <'100>
> 
> let await =
>   \fromResult ->
>     \next ->
>       \continue ->
>         fromResult
>           \result ->
>             (let inner = next result in
>             inner continue)
> 
> OpIn a b :
>   [
>      StdinLine Str -> OpIn <'70> <'69>,
>      Done <'67>
>   ]<'72>
> 
> sig lineIn : Task Str OpIn <'62> <'61>
> 
> let lineIn =
>   \toNext -> (StdinLine \s -> toNext s)
> 
> OpOut a b :
>   [
>      StdoutLine Str Unit -> OpOut <'47> <'46>,
>      Done <'44>
>   ]<'50>
> 
> sig lineOut : Str -> Task Unit OpOut <'39> <'38>
> 
> let lineOut =
>   \s -> \toNext -> (StdoutLine s \x -> toNext x)
> 
> Op a :
>   [
>      StdinLine Str -> Op <'22>,
>      StdoutLine Str Unit -> Op <'18>,
>      Done <'16>
>   ]
> 
> sig main : Task Unit Op <'11>
> 
> run main = await lineIn \s -> lineOut s