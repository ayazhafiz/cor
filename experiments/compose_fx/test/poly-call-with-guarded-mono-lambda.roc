# cor +mono -print
# cor +ir -print
# cor +eval -print

let poly = \x ->
  let f = \x -> x in
  A (f "") x
;;

run main =
  A (poly 1) (poly "")
;;

> cor-out +mono -print
> specializations:
>   let f11 = \x1 -[f11]-> x1
>   
>   let poly2 = \x -[poly2]->
>     let f = \x1 -[f11]-> x1 in
>     A (f "") x
>   
>   let poly3 = \x -[poly3]->
>     let f = \x1 -[f11]-> x1 in
>     A (f "") x
>   
>   let main = A (poly2 1) (poly3 "")
>   
>   
> entry_points:
>   main

> cor-out +ir -print
<<<<<<< Updated upstream
> proc f11(captures_: box<erased>, x1: str): str
> {
>   let captures_box: box<{}> = @ptr_cast(captures_ as box<{}>);
>   let captures_stack: {} = @get_boxed<captures_box>;
>   return x1;
> }
=======
> proc f11(captures_: [ `0 {} ], x1: str): str
> {let captures_stack: {} = @get_union_struct<captures_>;
>  return x1;}
>>>>>>> Stashed changes
> 
> proc poly3(captures_2: [ `0 {} ], x: str): [ `0 { str, str } ]
> {
<<<<<<< Updated upstream
>   let captures_box2: box<{}> = @ptr_cast(captures_3 as box<{}>);
>   let captures_stack2: {} = @get_boxed<captures_box2>;
>   let captures_stack_3: {} = @make_struct{};
>   let captures_box_3: box<{}> = @make_box(captures_stack_3);
>   let captures_6: box<erased> = @ptr_cast(captures_box_3 as box<erased>);
>   let fn_ptr_3: *fn = @make_fn_ptr<f11>;
>   let f: { *fn, box<erased> } = @make_struct{ fn_ptr_3, captures_6 };
>   let fnptr1: *fn = @get_struct_field<f, 0>;
>   let captures1: box<erased> = @get_struct_field<f, 1>;
>   let var3: str = "";
>   let var4: str = @call_indirect(fnptr1, captures1, var3);
>   let struct1: { str, str } = @make_struct{ var4, x };
>   let var5: [ `0 { str, str } ] = @make_union<0, struct1>;
>   return var5;
=======
>   let captures_stack2: {} = @get_union_struct<captures_2>;
>   let struct2: {} = @make_struct{};
>   let f: [ `0 {} ] = @make_union<0, struct2>;
>   let var2: str = "";
>   let cond1: int = @get_union_id<f>;
>   switch cond1 {
>   0 -> { @call_direct(f11, f, var2) }
>   } in join join1;
>   let struct3: { str, str } = @make_struct{ join1, x };
>   let var3: [ `0 { str, str } ] = @make_union<0, struct3>;
>   return var3;
>>>>>>> Stashed changes
> }
> 
> proc poly2(captures_1: [ `0 {} ], x: int): [ `0 { str, int } ]
> {
<<<<<<< Updated upstream
>   let captures_box1: box<{}> = @ptr_cast(captures_1 as box<{}>);
>   let captures_stack1: {} = @get_boxed<captures_box1>;
>   let captures_stack_2: {} = @make_struct{};
>   let captures_box_2: box<{}> = @make_box(captures_stack_2);
>   let captures_5: box<erased> = @ptr_cast(captures_box_2 as box<erased>);
>   let fn_ptr_2: *fn = @make_fn_ptr<f11>;
>   let f: { *fn, box<erased> } = @make_struct{ fn_ptr_2, captures_5 };
>   let fnptr: *fn = @get_struct_field<f, 0>;
>   let captures: box<erased> = @get_struct_field<f, 1>;
=======
>   let captures_stack1: {} = @get_union_struct<captures_1>;
>   let struct: {} = @make_struct{};
>   let f: [ `0 {} ] = @make_union<0, struct>;
>>>>>>> Stashed changes
>   let var: str = "";
>   let cond: int = @get_union_id<f>;
>   switch cond {
>   0 -> { @call_direct(f11, f, var) }
>   } in join join;
>   let struct1: { str, int } = @make_struct{ join, x };
>   let var1: [ `0 { str, int } ] = @make_union<0, struct1>;
>   return var1;
> }
> 
> proc main_thunk(): [ `0 { [ `0 { str, int } ], [ `0 { str, str } ] } ]
> {
>   let struct4: {} = @make_struct{};
>   let var4: [ `0 {} ] = @make_union<0, struct4>;
>   let var5: int = 1;
>   let cond2: int = @get_union_id<var4>;
>   switch cond2 {
>   0 -> { @call_direct(poly2, var4, var5) }
>   } in join join2;
>   let struct5: {} = @make_struct{};
>   let var6: [ `0 {} ] = @make_union<0, struct5>;
>   let var7: str = "";
>   let cond3: int = @get_union_id<var6>;
>   switch cond3 {
>   0 -> { @call_direct(poly3, var6, var7) }
>   } in join join3;
>   let struct6: { [ `0 { str, int } ], [ `0 { str, str } ] }
>     = @make_struct{ join2, join3 };
>   let var8: [ `0 { [ `0 { str, int } ], [ `0 { str, str } ] } ]
>     = @make_union<0, struct6>;
>   return var8;
> }
> 
> global main:
>   [ `0 { [ `0 { str, int } ], [ `0 { str, str } ] } ]
>   = @call_direct(main_thunk);
> 
> entry main;

> cor-out +eval -print
> main = [0 [0 [] 1] [0 [] []]]
>      > A (A "" 1) (A "" "")