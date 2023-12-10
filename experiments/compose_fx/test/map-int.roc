# cor +ir -print
# cor +eval -print

let map = \x ->
  let f = \y -> ~add y 1 in
  f x
;;

run main = map 1;;

> cor-out +ir -print
<<<<<<< Updated upstream
> proc f11(captures_: box<erased>, y: int): int
=======
> proc f11(captures_: [ `0 {} ], y: int): int
>>>>>>> Stashed changes
> {
>   let captures_stack: {} = @get_union_struct<captures_>;
>   let var: int = 1;
>   let var1: int = @call_kfn(add, y, var);
>   return var1;
> }
> 
> proc map2(captures_1: [ `0 {} ], x: int): int
> {
<<<<<<< Updated upstream
>   let captures_box1: box<{}> = @ptr_cast(captures_1 as box<{}>);
>   let captures_stack1: {} = @get_boxed<captures_box1>;
>   let captures_stack_1: {} = @make_struct{};
>   let captures_box_1: box<{}> = @make_box(captures_stack_1);
>   let captures_3: box<erased> = @ptr_cast(captures_box_1 as box<erased>);
>   let fn_ptr_1: *fn = @make_fn_ptr<f11>;
>   let f: { *fn, box<erased> } = @make_struct{ fn_ptr_1, captures_3 };
>   let fnptr: *fn = @get_struct_field<f, 0>;
>   let captures: box<erased> = @get_struct_field<f, 1>;
>   let var2: int = @call_indirect(fnptr, captures, x);
>   return var2;
=======
>   let captures_stack1: {} = @get_union_struct<captures_1>;
>   let struct: {} = @make_struct{};
>   let f: [ `0 {} ] = @make_union<0, struct>;
>   let cond: int = @get_union_id<f>;
>   switch cond {
>   0 -> { @call_direct(f11, f, x) }
>   } in join join;
>   return join;
>>>>>>> Stashed changes
> }
> 
> proc main_thunk(): int
> {
>   let struct1: {} = @make_struct{};
>   let var2: [ `0 {} ] = @make_union<0, struct1>;
>   let var3: int = 1;
>   let cond1: int = @get_union_id<var2>;
>   switch cond1 {
>   0 -> { @call_direct(map2, var2, var3) }
>   } in join join1;
>   return join1;
> }
> 
> global main: int = @call_direct(main_thunk);
> 
> entry main;

> cor-out +eval -print
> main = 2
>      > 2