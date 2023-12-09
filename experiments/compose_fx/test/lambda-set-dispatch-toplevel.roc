# cor +mono -print
# cor +ir -print
# cor +eval -print

let f1 = \x -> ~add x 1;;
let f2 = \x -> ~add x 2;;
let f3 = \x -> ~add x 3;;

let f = \t -> when t is
  | T1 -> f1
  | T2 -> f2
  | T3 -> f3
  end
;;

run x = f T2 0
;;

> cor-out +mono -print
> specializations:
>   let f12 = \x -[f12]-> add x 1
>   
>   let f22 = \x1 -[f22]-> add x1 2
>   
>   let f32 = \x2 -[f32]-> add x2 3
>   
>   let f5 = \t -[f5]->
>     when t is | T1 -> f12 | T2 -> f22 | T3 -> f32
>     end
>   
>   let x3 = (f5 (T2 )) 0
>   
>   
> entry_points:
>   x3

> cor-out +ir -print
> proc clos_f22(captures_2: box<erased>, x1: int): int
> {
>   let captures_box1: box<{}> = @ptr_cast(captures_2 as box<{}>);
>   let captures_stack1: {} = @get_boxed<captures_box1>;
>   let var2: int = 2;
>   let var3: int = @call_kfn(add, x1, var2);
>   return var3;
> }
> 
> proc clos_f32(captures_4: box<erased>, x2: int): int
> {
>   let captures_box2: box<{}> = @ptr_cast(captures_4 as box<{}>);
>   let captures_stack2: {} = @get_boxed<captures_box2>;
>   let var4: int = 3;
>   let var5: int = @call_kfn(add, x2, var4);
>   return var5;
> }
> 
> proc clos_f12(captures_: box<erased>, x: int): int
> {
>   let captures_box: box<{}> = @ptr_cast(captures_ as box<{}>);
>   let captures_stack: {} = @get_boxed<captures_box>;
>   let var: int = 1;
>   let var1: int = @call_kfn(add, x, var);
>   return var1;
> }
> 
> proc f22_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_1: {} = @make_struct{};
>   let captures_box_1: box<{}> = @make_box(captures_stack_1);
>   let captures_3: box<erased> = @ptr_cast(captures_box_1 as box<erased>);
>   let fn_ptr_1: *fn = @make_fn_ptr<clos_f22>;
>   let f22_closure: { *fn, box<erased> } = @make_struct{ fn_ptr_1, captures_3 };
>   return f22_closure;
> }
> 
> proc f32_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_2: {} = @make_struct{};
>   let captures_box_2: box<{}> = @make_box(captures_stack_2);
>   let captures_5: box<erased> = @ptr_cast(captures_box_2 as box<erased>);
>   let fn_ptr_2: *fn = @make_fn_ptr<clos_f32>;
>   let f32_closure: { *fn, box<erased> } = @make_struct{ fn_ptr_2, captures_5 };
>   return f32_closure;
> }
> 
> proc f12_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_: {} = @make_struct{};
>   let captures_box_: box<{}> = @make_box(captures_stack_);
>   let captures_1: box<erased> = @ptr_cast(captures_box_ as box<erased>);
>   let fn_ptr_: *fn = @make_fn_ptr<clos_f12>;
>   let f12_closure: { *fn, box<erased> } = @make_struct{ fn_ptr_, captures_1 };
>   return f12_closure;
> }
> 
> global f22: { *fn, box<erased> } = @call_direct(f22_thunk);
> 
> global f32: { *fn, box<erased> } = @call_direct(f32_thunk);
> 
> global f12: { *fn, box<erased> } = @call_direct(f12_thunk);
> 
> proc clos_f5(captures_6: box<erased>, t: [ `0 {}, `1 {}, `2 {} ]):
>   { *fn, box<erased> }
> {
>   let captures_box3: box<{}> = @ptr_cast(captures_6 as box<{}>);
>   let captures_stack3: {} = @get_boxed<captures_box3>;
>   let discr: int = @get_union_id<t>;
>   switch discr {
>   0 -> {let payload: {} = @get_union_struct<t>;f12}
>   1 -> {let payload1: {} = @get_union_struct<t>;f22}
>   2 -> {let payload2: {} = @get_union_struct<t>;f32}
>   } in join join;
>   return join;
> }
> 
> proc f5_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_3: {} = @make_struct{};
>   let captures_box_3: box<{}> = @make_box(captures_stack_3);
>   let captures_7: box<erased> = @ptr_cast(captures_box_3 as box<erased>);
>   let fn_ptr_3: *fn = @make_fn_ptr<clos_f5>;
>   let f5_closure: { *fn, box<erased> } = @make_struct{ fn_ptr_3, captures_7 };
>   return f5_closure;
> }
> 
> global f5: { *fn, box<erased> } = @call_direct(f5_thunk);
> 
> proc x_thunk(): int
> {
>   let fnptr: *fn = @get_struct_field<f5, 0>;
>   let captures: box<erased> = @get_struct_field<f5, 1>;
>   let struct: {} = @make_struct{};
>   let var6: [ `0 {}, `1 {}, `2 {} ] = @make_union<1, struct>;
>   let var7: { *fn, box<erased> } = @call_indirect(fnptr, captures, var6);
>   let fnptr1: *fn = @get_struct_field<var7, 0>;
>   let captures1: box<erased> = @get_struct_field<var7, 1>;
>   let var8: int = 0;
>   let var9: int = @call_indirect(fnptr1, captures1, var8);
>   return var9;
> }
> 
> global x3: int = @call_direct(x_thunk);
> 
> entry x3;

> cor-out +eval -print
> x3 = 2
>    > 2