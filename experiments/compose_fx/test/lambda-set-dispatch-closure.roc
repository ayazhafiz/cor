# cor +mono -print
# cor +ir -print
# cor +eval -print

let f = \x -> \t -> when t is
  | T1 -> \y -> ~add x y 1
  | T2 -> \y -> ~add x y 2
  | T3 -> \y -> ~add x y 3
  end
;;

run x = f 1 T2 0
;;

> cor-out +mono -print
> specializations:
>   let lam31 = \t -[lam31 x]->
>     when t is
>       | T1 -> \y -[lam4 x]-> add x y 1
>       | T2 -> \y1 -[lam11 x]-> add x y1 2
>       | T3 -> \y2 -[lam21 x]-> add x y2 3
>     end
>   
>   let lam4 = \y -[lam4 x]-> add x y 1
>   
>   let lam11 = \y1 -[lam11 x]-> add x y1 2
>   
>   let lam21 = \y2 -[lam21 x]-> add x y2 3
>   
>   let f2 = \x -[f2]->
>     \t -[lam31 x]->
>       when t is
>         | T1 -> \y -[lam4 x]-> add x y 1
>         | T2 -> \y1 -[lam11 x]-> add x y1 2
>         | T3 -> \y2 -[lam21 x]-> add x y2 3
>       end
>   
>   let x1 = ((f2 1) (T2 )) 0
>   
>   
> entry_points:
>   x1

> cor-out +ir -print
> proc lam21(captures_3: box<erased>, y2: int): int
> {
>   let captures_box3: box<{ int }> = @ptr_cast(captures_3 as box<{ int }>);
>   let captures_stack3: { int } = @get_boxed<captures_box3>;
>   let x: int = @get_struct_field<captures_stack3, 0>;
>   let var4: int = 3;
>   let var5: int = @call_kfn(add, x, y2, var4);
>   return var5;
> }
> 
> proc lam11(captures_2: box<erased>, y1: int): int
> {
>   let captures_box2: box<{ int }> = @ptr_cast(captures_2 as box<{ int }>);
>   let captures_stack2: { int } = @get_boxed<captures_box2>;
>   let x: int = @get_struct_field<captures_stack2, 0>;
>   let var2: int = 2;
>   let var3: int = @call_kfn(add, x, y1, var2);
>   return var3;
> }
> 
> proc lam4(captures_1: box<erased>, y: int): int
> {
>   let captures_box1: box<{ int }> = @ptr_cast(captures_1 as box<{ int }>);
>   let captures_stack1: { int } = @get_boxed<captures_box1>;
>   let x: int = @get_struct_field<captures_stack1, 0>;
>   let var: int = 1;
>   let var1: int = @call_kfn(add, x, y, var);
>   return var1;
> }
> 
> proc lam31(captures_: box<erased>, t: [ `0 {}, `1 {}, `2 {} ]):
>   { *fn, box<erased> }
> {
>   let captures_box: box<{ int }> = @ptr_cast(captures_ as box<{ int }>);
>   let captures_stack: { int } = @get_boxed<captures_box>;
>   let x: int = @get_struct_field<captures_stack, 0>;
>   let discr: int = @get_union_id<t>;
>   switch discr {
>   0 -> {
>     let payload: {} = @get_union_struct<t>;
>     let captures_stack_1: { int } = @make_struct{ x };
>     let captures_box_1: box<{ int }> = @make_box(captures_stack_1);
>     let captures_6: box<erased> = @ptr_cast(captures_box_1 as box<erased>);
>     let fn_ptr_1: *fn = @make_fn_ptr<lam4>;
>     @make_struct{ fn_ptr_1, captures_6 }
>   }
>   1 -> {
>     let payload1: {} = @get_union_struct<t>;
>     let captures_stack_2: { int } = @make_struct{ x };
>     let captures_box_2: box<{ int }> = @make_box(captures_stack_2);
>     let captures_7: box<erased> = @ptr_cast(captures_box_2 as box<erased>);
>     let fn_ptr_2: *fn = @make_fn_ptr<lam11>;
>     @make_struct{ fn_ptr_2, captures_7 }
>   }
>   2 -> {
>     let payload2: {} = @get_union_struct<t>;
>     let captures_stack_3: { int } = @make_struct{ x };
>     let captures_box_3: box<{ int }> = @make_box(captures_stack_3);
>     let captures_8: box<erased> = @ptr_cast(captures_box_3 as box<erased>);
>     let fn_ptr_3: *fn = @make_fn_ptr<lam21>;
>     @make_struct{ fn_ptr_3, captures_8 }
>   }
>   } in join join;
>   return join;
> }
> 
> proc clos_f2(captures_4: box<erased>, x: int): { *fn, box<erased> }
> {
>   let captures_box4: box<{}> = @ptr_cast(captures_4 as box<{}>);
>   let captures_stack4: {} = @get_boxed<captures_box4>;
>   let captures_stack_4: { int } = @make_struct{ x };
>   let captures_box_4: box<{ int }> = @make_box(captures_stack_4);
>   let captures_9: box<erased> = @ptr_cast(captures_box_4 as box<erased>);
>   let fn_ptr_4: *fn = @make_fn_ptr<lam31>;
>   let var6: { *fn, box<erased> } = @make_struct{ fn_ptr_4, captures_9 };
>   return var6;
> }
> 
> proc f2_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_: {} = @make_struct{};
>   let captures_box_: box<{}> = @make_box(captures_stack_);
>   let captures_5: box<erased> = @ptr_cast(captures_box_ as box<erased>);
>   let fn_ptr_: *fn = @make_fn_ptr<clos_f2>;
>   let f2_closure: { *fn, box<erased> } = @make_struct{ fn_ptr_, captures_5 };
>   return f2_closure;
> }
> 
> global f2: { *fn, box<erased> } = @call_direct(f2_thunk);
> 
> proc x_thunk(): int
> {
>   let fnptr: *fn = @get_struct_field<f2, 0>;
>   let captures: box<erased> = @get_struct_field<f2, 1>;
>   let var7: int = 1;
>   let var8: { *fn, box<erased> } = @call_indirect(fnptr, captures, var7);
>   let fnptr1: *fn = @get_struct_field<var8, 0>;
>   let captures1: box<erased> = @get_struct_field<var8, 1>;
>   let struct: {} = @make_struct{};
>   let var9: [ `0 {}, `1 {}, `2 {} ] = @make_union<1, struct>;
>   let var10: { *fn, box<erased> } = @call_indirect(fnptr1, captures1, var9);
>   let fnptr2: *fn = @get_struct_field<var10, 0>;
>   let captures2: box<erased> = @get_struct_field<var10, 1>;
>   let var11: int = 0;
>   let var12: int = @call_indirect(fnptr2, captures2, var11);
>   return var12;
> }
> 
> global x1: int = @call_direct(x_thunk);
> 
> entry x1;

> cor-out +eval -print
> x1 = 3
>    > 3