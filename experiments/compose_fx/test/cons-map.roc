# cor +solve -elab
# cor +ir -print
# cor +eval -print
List a : [ Nil, Cons a (List a) ]

sig map : (a -> b) -> List a -> List b
#   ^^^
let map = \f -> \xs ->
  let go = \xs ->
    when xs is
#        ^^
      | Nil -> Nil
      | Cons x xs -> Cons (f x) (go xs)
      #        ^^                   ^^
    end
  in go xs
#       ^^
;;

let mapper = \x -> A x;;
#   ^^^^^^

sig l : List Int
let l = Cons 1 (Cons 2 Nil);;

run main = map mapper l;;

> cor-out +solve -elab
> List a : [ Nil, Cons a (List a) ]
> 
> sig map : (a -> b) -> List a -> List b
> #   ^^^ ('a -'c-> 'b)
> #   ^^^   -[map1]-> %(List 'a1)
> #   ^^^               -[lam ('a2 -'c-> 'b2)]-> %List 'b1
> let map = \f -> \xs ->
>   let go = \xs ->
>     when xs is
> #        ^^ %List 'a
>       | Nil -> Nil
>       | Cons x xs -> Cons (f x) (go xs)
> #                                   ^^ %List 'a
> #              ^^ %List 'a
>     end
>   in go xs
> #       ^^ %List 'a
> ;;
> 
> let mapper = \x -> A x;;
> #   ^^^^^^ 'a -[mapper1]-> [A 'a]'*
> 
> sig l : List Int
> let l = Cons 1 (Cons 2 Nil);;
> 
> run main = map mapper l;;
> 

> cor-out +ir -print
> proc go2(
>   captures_go: box<erased>,
>    xs1: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>):
>   box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
> {
>   let captures_box1: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_go as box<{ { *fn, box<erased> } }>);
>   let captures_stack1: { { *fn, box<erased> } } = @get_boxed<captures_box1>;
>   let f: { *fn, box<erased> } = @get_struct_field<captures_stack1, 0>;
>   let rec_fn_ptr_go: *fn = @make_fn_ptr<go2>;
>   let go2: { *fn, box<erased> } = @make_struct{ rec_fn_ptr_go, captures_go };
>   let inner:
>         [ `0 { int, box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]> }, `1 {}
>         ]
>     = @get_boxed<xs1>;
>   let discr: int = @get_union_id<inner>;
>   switch discr {
>   0 -> {
>     let payload1: { int, box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]> }
>       = @get_union_struct<inner>;
>     let x: int = @get_struct_field<payload1, 0>;
>     let xs2: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>
>       = @get_struct_field<payload1, 1>;
>     let fnptr1: *fn = @get_struct_field<f, 0>;
>     let captures1: box<erased> = @get_struct_field<f, 1>;
>     let var1: [ `0 { int } ] = @call_indirect(fnptr1, captures1, x);
>     let fnptr2: *fn = @get_struct_field<go, 0>;
>     let captures2: box<erased> = @get_struct_field<go, 1>;
>     let var2: box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
>       = @call_indirect(fnptr2, captures2, xs2);
>     let struct1:
>           {
>            [ `0 { int } ],
>             box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
>            ,
>           }
>       = @make_struct{ var1, var2 };
>     let unboxed1:
>           [
>              `0 {
>                  [ `0 { int } ],
>                   box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
>                  ,
>                 },
>              `1 {}
>           ]
>       = @make_union<0, struct1>;
>     @make_box(unboxed1)
>   }
>   1 -> {
>     let payload: {} = @get_union_struct<inner>;
>     let struct: {} = @make_struct{};
>     let unboxed:
>           [
>              `0 {
>                  [ `0 { int } ],
>                   box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
>                  ,
>                 },
>              `1 {}
>           ]
>       = @make_union<1, struct>;
>     @make_box(unboxed)
>   }
>   } in join join;
>   return join;
> }
> 
> proc clos_mapper2(captures_3: box<erased>, x1: int): [ `0 { int } ]
> {
>   let captures_box3: box<{}> = @ptr_cast(captures_3 as box<{}>);
>   let captures_stack3: {} = @get_boxed<captures_box3>;
>   let struct2: { int } = @make_struct{ x1 };
>   let var4: [ `0 { int } ] = @make_union<0, struct2>;
>   return var4;
> }
> 
> proc l_thunk(): box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]>
> {
>   let var5: int = 1;
>   let var6: int = 2;
>   let struct3: {} = @make_struct{};
>   let unboxed2:
>         [ `0 { int, box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<1, struct3>;
>   let var7: box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]>
>     = @make_box(unboxed2);
>   let struct4: { int, box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]> }
>     = @make_struct{ var6, var7 };
>   let unboxed3:
>         [ `0 { int, box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<0, struct4>;
>   let var8: box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]>
>     = @make_box(unboxed3);
>   let struct5: { int, box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]> }
>     = @make_struct{ var5, var8 };
>   let unboxed4:
>         [ `0 { int, box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<0, struct5>;
>   let var9: box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]>
>     = @make_box(unboxed4);
>   return var9;
> }
> 
> proc lam1(
>   captures_: box<erased>,
>    xs: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>):
>   box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
> {
>   let captures_box: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_ as box<{ { *fn, box<erased> } }>);
>   let captures_stack: { { *fn, box<erased> } } = @get_boxed<captures_box>;
>   let f: { *fn, box<erased> } = @get_struct_field<captures_stack, 0>;
>   let captures_stack_2: { { *fn, box<erased> } } = @make_struct{ f };
>   let captures_box_2: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_2);
>   let captures_5: box<erased> = @ptr_cast(captures_box_2 as box<erased>);
>   let fn_ptr_2: *fn = @make_fn_ptr<go2>;
>   let go: { *fn, box<erased> } = @make_struct{ fn_ptr_2, captures_5 };
>   let fnptr: *fn = @get_struct_field<go, 0>;
>   let captures: box<erased> = @get_struct_field<go, 1>;
>   let var: box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
>     = @call_indirect(fnptr, captures, xs);
>   return var;
> }
> 
> proc mapper2_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_1: {} = @make_struct{};
>   let captures_box_1: box<{}> = @make_box(captures_stack_1);
>   let captures_4: box<erased> = @ptr_cast(captures_box_1 as box<erased>);
>   let fn_ptr_1: *fn = @make_fn_ptr<clos_mapper2>;
>   let mapper2_closure: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_1, captures_4 };
>   return mapper2_closure;
> }
> 
> global l1:
>   box<%type_6 = [ `0 { int, box<%type_6> }, `1 {} ]>
>   = @call_direct(l_thunk);
> 
> proc clos_map2(captures_1: box<erased>, f: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box2: box<{}> = @ptr_cast(captures_1 as box<{}>);
>   let captures_stack2: {} = @get_boxed<captures_box2>;
>   let captures_stack_3: { { *fn, box<erased> } } = @make_struct{ f };
>   let captures_box_3: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_3);
>   let captures_6: box<erased> = @ptr_cast(captures_box_3 as box<erased>);
>   let fn_ptr_3: *fn = @make_fn_ptr<lam1>;
>   let var3: { *fn, box<erased> } = @make_struct{ fn_ptr_3, captures_6 };
>   return var3;
> }
> 
> global mapper2: { *fn, box<erased> } = @call_direct(mapper2_thunk);
> 
> proc map2_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_: {} = @make_struct{};
>   let captures_box_: box<{}> = @make_box(captures_stack_);
>   let captures_2: box<erased> = @ptr_cast(captures_box_ as box<erased>);
>   let fn_ptr_: *fn = @make_fn_ptr<clos_map2>;
>   let map2_closure: { *fn, box<erased> } = @make_struct{ fn_ptr_, captures_2 };
>   return map2_closure;
> }
> 
> global map2: { *fn, box<erased> } = @call_direct(map2_thunk);
> 
> proc main_thunk():
>   box<%type_9 = [ `0 { [ `0 { int } ], box<%type_9> }, `1 {} ]>
> {
>   let fnptr3: *fn = @get_struct_field<map2, 0>;
>   let captures3: box<erased> = @get_struct_field<map2, 1>;
>   let var10: { *fn, box<erased> } = @call_indirect(fnptr3, captures3, mapper2);
>   let fnptr4: *fn = @get_struct_field<var10, 0>;
>   let captures4: box<erased> = @get_struct_field<var10, 1>;
>   let var11: box<%type_9 = [ `0 { [ `0 { int } ], box<%type_9> }, `1 {} ]>
>     = @call_indirect(fnptr4, captures4, l1);
>   return var11;
> }
> 
> global main:
>   box<%type_7 = [ `0 { [ `0 { int } ], box<%type_7> }, `1 {} ]>
>   = @call_direct(main_thunk);
> 
> entry main;

> cor-out +eval -print
> main = [0 [0 1] [0 [0 2] [1]]]
>      > Cons (A 1) (Cons (A 2) (Nil ))