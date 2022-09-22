# cor +solve -elab
# cor +mono -print
let x = Add Z in
#   ^
let result = when x is
  | Add Z -> Z
in result
#  ^^^^^^

> cor-out +solve -elab
> let x = Add Z in
> #   ^ [Add [Z]]
> let result = when x is
>   | Add Z -> Z
> in result
> #  ^^^^^^ [Z]
> 

> cor-out +mono -print
> let %1 : {} = @build_struct;
> let %2 : [ `0 ] = @build_tag 0 %1;
> let %3 : { [ `0 ] } = @build_struct %2;
> let %4 : [ `0 [ `0 ] ] = @build_tag 0 %3;
> let x : [ `0 [ `0 ] ] = %4 : [ `0 [ `0 ] ];
> let %6 : int = @get_tag_id x;
> switch %6 {
>   0: {
>     let %5 : [ `0 ] = @get_field 0 x;
>     let %8 : int = @get_tag_id %5;
>     switch %8 {
>       0: {
>         let %10 : {} = @build_struct;
>         let %11 : [ `0 ] = @build_tag 0 %10;
>         feed %11
>       }
>     } in join %9 : [ `0 ]
>     feed %9
>   }
> } in join %7 : [ `0 ]
> let result : [ `0 ] = %7 : [ `0 ];
> ret result