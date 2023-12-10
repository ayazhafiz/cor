# cor +ir -print
# cor +eval -print

let poly = \x ->
  let f = \x -> x in
  f x
;;

run main =
  A (poly 1) (poly "")
;;

> cor-out +ir -print
<<<<<<< Updated upstream
> proc f11(captures_: box<erased>, x1: int): int
> {
>   let captures_box: box<{}> = @ptr_cast(captures_ as box<{}>);
>   let captures_stack: {} = @get_boxed<captures_box>;
>   return x1;
> }
> 
> proc f12(captures_3: box<erased>, x1: str): str
> {
>   let captures_box2: box<{}> = @ptr_cast(captures_3 as box<{}>);
>   let captures_stack2: {} = @get_boxed<captures_box2>;
>   return x1;
> }
> 
> proc clos_poly2(captures_1: box<erased>, x: int): int
> {
>   let captures_box1: box<{}> = @ptr_cast(captures_1 as box<{}>);
>   let captures_stack1: {} = @get_boxed<captures_box1>;
>   let captures_stack_2: {} = @make_struct{};
>   let captures_box_2: box<{}> = @make_box(captures_stack_2);
>   let captures_6: box<erased> = @ptr_cast(captures_box_2 as box<erased>);
>   let fn_ptr_2: *fn = @make_fn_ptr<f11>;
>   let f: { *fn, box<erased> } = @make_struct{ fn_ptr_2, captures_6 };
>   let fnptr: *fn = @get_struct_field<f, 0>;
>   let captures: box<erased> = @get_struct_field<f, 1>;
>   let var: int = @call_indirect(fnptr, captures, x);
>   return var;
> }
> 
> proc clos_poly3(captures_4: box<erased>, x: str): str
> {
>   let captures_box3: box<{}> = @ptr_cast(captures_4 as box<{}>);
>   let captures_stack3: {} = @get_boxed<captures_box3>;
>   let captures_stack_3: {} = @make_struct{};
>   let captures_box_3: box<{}> = @make_box(captures_stack_3);
>   let captures_7: box<erased> = @ptr_cast(captures_box_3 as box<erased>);
>   let fn_ptr_3: *fn = @make_fn_ptr<f12>;
>   let f: { *fn, box<erased> } = @make_struct{ fn_ptr_3, captures_7 };
>   let fnptr1: *fn = @get_struct_field<f, 0>;
>   let captures1: box<erased> = @get_struct_field<f, 1>;
>   let var1: str = @call_indirect(fnptr1, captures1, x);
>   return var1;
> }
=======
> proc f11(captures_: [ `0 {} ], x1: int): int
> {let captures_stack: {} = @get_union_struct<captures_>;
>  return x1;}
> 
> proc f12(captures_2: [ `0 {} ], x1: str): str
> {let captures_stack2: {} = @get_union_struct<captures_2>;
>  return x1;}
>>>>>>> Stashed changes
> 
> proc poly2(captures_1: [ `0 {} ], x: int): int
> {
>   let captures_stack1: {} = @get_union_struct<captures_1>;
>   let struct: {} = @make_struct{};
>   let f: [ `0 {} ] = @make_union<0, struct>;
>   let cond: int = @get_union_id<f>;
>   switch cond {
>   0 -> { @call_direct(f11, f, x) }
>   } in join join;
>   return join;
> }
> 
> proc poly3(captures_3: [ `0 {} ], x: str): str
> {
>   let captures_stack3: {} = @get_union_struct<captures_3>;
>   let struct1: {} = @make_struct{};
>   let f: [ `0 {} ] = @make_union<0, struct1>;
>   let cond1: int = @get_union_id<f>;
>   switch cond1 {
>   0 -> { @call_direct(f12, f, x) }
>   } in join join1;
>   return join1;
> }
> 
> proc main_thunk(): [ `0 { int, str } ]
> {
>   let struct2: {} = @make_struct{};
>   let var: [ `0 {} ] = @make_union<0, struct2>;
>   let var1: int = 1;
>   let cond2: int = @get_union_id<var>;
>   switch cond2 {
>   0 -> { @call_direct(poly2, var, var1) }
>   } in join join2;
>   let struct3: {} = @make_struct{};
>   let var2: [ `0 {} ] = @make_union<0, struct3>;
>   let var3: str = "";
>   let cond3: int = @get_union_id<var2>;
>   switch cond3 {
>   0 -> { @call_direct(poly3, var2, var3) }
>   } in join join3;
>   let struct4: { int, str } = @make_struct{ join2, join3 };
>   let var4: [ `0 { int, str } ] = @make_union<0, struct4>;
>   return var4;
> }
> 
> global main: [ `0 { int, str } ] = @call_direct(main_thunk);
> 
> entry main;

> cor-out +eval -print
> main = [0 1 []]
>      > A 1 ""