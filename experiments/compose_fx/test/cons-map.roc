# cor +solve -elab
# cor +mono -print
# cor +ir -print
# cor +eval -print
List a : [ Nil, Cons a (List a) ]

sig map : (a -> b) -> List a -> List b
#   ^^^
let map = \f -> \xs ->
  let go = \xs ->
  #   ^^
    when xs is
#        ^^
      | Nil -> Nil
      | Cons x xs -> Cons (f x) (go xs)
      #        ^^                   ^^
    end
  in go xs
#    ^^ ^^
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
> #   ^^^   -[map]-> %(List 'a1)
> #   ^^^              -[lam ('a2 -'c-> 'b2)]-> %List 'b1
> let map = \f -> \xs ->
>   let go = \xs ->
> #     ^^ %(List 'a) -[go1 ('a -'*-> 'b)]-> %List 'b
>     when xs is
> #        ^^ %List 'a
>       | Nil -> Nil
>       | Cons x xs -> Cons (f x) (go xs)
> #                                   ^^ %List 'a
> #              ^^ %List 'a
>     end
>   in go xs
> #       ^^ %List 'a
> #    ^^ %(List 'a) -[go1 ('a -'*-> 'b)]-> %List 'b
> ;;
> 
> let mapper = \x -> A x;;
> #   ^^^^^^ 'a -[mapper]-> [A 'a]'*
> 
> sig l : List Int
> let l = Cons 1 (Cons 2 Nil);;
> 
> run main = map mapper l;;
> 

> cor-out +mono -print
> specializations:
>   let lam1 = \xs -[lam1 f]->
>     let go =
>       \xs1 -[go11 f]->
>         when xs1 is
>           | Nil -> Nil 
>           | Consx xs2 -> Cons (f x) (go xs2)
>         end
>     in
>     go xs
>   
>   let go11 = \xs1 -[go11 f]->
>     when xs1 is
>       | Nil -> Nil 
>       | Consx xs2 -> Cons (f x) (go xs2)
>     end
>   
>   let map2 = \f -[map2]->
>     \xs -[lam1 f]->
>       let go =
>         \xs1 -[go11 f]->
>           when xs1 is
>             | Nil -> Nil 
>             | Consx xs2 -> Cons (f x) (go xs2)
>           end
>       in
>       go xs
>   
>   let mapper2 = \x1 -[mapper2]-> A x1
>   
>   let l1 = Cons 1 (Cons 2 (Nil ))
>   
>   let main = (map2 mapper2) l1
>   
>   
> entry_points:
>   main

> cor-out +ir -print
<<<<<<< Updated upstream
> proc clos_mapper2(captures_3: box<erased>, x1: int): [ `0 { int } ]
> {
>   let captures_box3: box<{}> = @ptr_cast(captures_3 as box<{}>);
>   let captures_stack3: {} = @get_boxed<captures_box3>;
>   let struct2: { int } = @make_struct{ x1 };
>   let var4: [ `0 { int } ] = @make_union<0, struct2>;
>   return var4;
> }
> 
> proc l_thunk(): box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>
> {
>   let var5: int = 1;
>   let var6: int = 2;
>   let struct3: {} = @make_struct{};
>   let unboxed2:
>         [ `0 { int, box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<1, struct3>;
>   let var7: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>
>     = @make_box(unboxed2);
>   let struct4: { int, box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]> }
>     = @make_struct{ var6, var7 };
>   let unboxed3:
>         [ `0 { int, box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<0, struct4>;
>   let var8: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>
>     = @make_box(unboxed3);
>   let struct5: { int, box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]> }
>     = @make_struct{ var5, var8 };
>   let unboxed4:
>         [ `0 { int, box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<0, struct5>;
>   let var9: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>
>     = @make_box(unboxed4);
>   return var9;
> }
> 
> proc go11(
>   captures_go: box<erased>,
>    xs1: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>):
>   box<%type_4 = [ `0 { [ `0 { int } ], box<%type_4> }, `1 {} ]>
> {
>   let captures_box1: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_go as box<{ { *fn, box<erased> } }>);
>   let captures_stack1: { { *fn, box<erased> } } = @get_boxed<captures_box1>;
>   let f: { *fn, box<erased> } = @get_struct_field<captures_stack1, 0>;
>   let rec_fn_ptr_go: *fn = @make_fn_ptr<go11>;
>   let go: { *fn, box<erased> } = @make_struct{ rec_fn_ptr_go, captures_go };
=======
> proc mapper2(captures_2: [ `0 {} ], x1: int): [ `0 { int } ]
> {
>   let captures_stack3: {} = @get_union_struct<captures_2>;
>   let struct5: { int } = @make_struct{ x1 };
>   let var1: [ `0 { int } ] = @make_union<0, struct5>;
>   return var1;
> }
> 
> proc map2(captures_1: [ `0 {} ], f: [ `0 {} ]): [ `0 { [ `0 {} ] } ]
> {
>   let captures_stack2: {} = @get_union_struct<captures_1>;
>   let struct4: { [ `0 {} ] } = @make_struct{ f };
>   let var: [ `0 { [ `0 {} ] } ] = @make_union<0, struct4>;
>   return var;
> }
> 
> proc l_thunk(): box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]>
> {
>   let var2: int = 1;
>   let var3: int = 2;
>   let struct6: {} = @make_struct{};
>   let unboxed2:
>         [ `0 { int, box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<1, struct6>;
>   let var4: box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]>
>     = @make_box(unboxed2);
>   let struct7: { int, box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]> }
>     = @make_struct{ var3, var4 };
>   let unboxed3:
>         [ `0 { int, box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<0, struct7>;
>   let var5: box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]>
>     = @make_box(unboxed3);
>   let struct8: { int, box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]> }
>     = @make_struct{ var2, var5 };
>   let unboxed4:
>         [ `0 { int, box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]> }, `1 {}
>         ]
>     = @make_union<0, struct8>;
>   let var6: box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]>
>     = @make_box(unboxed4);
>   return var6;
> }
> 
> proc go11(
>   captures_go: [ `0 { [ `0 {} ] } ],
>    xs1: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>):
>   box<%type_6 = [ `0 { [ `0 { int } ], box<%type_6> }, `1 {} ]>
> {
>   let captures_stack1: { [ `0 {} ] } = @get_union_struct<captures_go>;
>   let f: [ `0 {} ] = @get_struct_field<captures_stack1, 0>;
>   let rec_fn_ptr_go: *fn = @make_fn_ptr<go11>;
>   let struct1: { [ `0 {} ] } = @make_struct{ f };
>   let go: [ `0 { [ `0 {} ] } ] = @make_union<0, struct1>;
>>>>>>> Stashed changes
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
<<<<<<< Updated upstream
>     let fnptr1: *fn = @get_struct_field<f, 0>;
>     let captures1: box<erased> = @get_struct_field<f, 1>;
>     let var1: [ `0 { int } ] = @call_indirect(fnptr1, captures1, x);
>     let fnptr2: *fn = @get_struct_field<go, 0>;
>     let captures2: box<erased> = @get_struct_field<go, 1>;
>     let var2: box<%type_4 = [ `0 { [ `0 { int } ], box<%type_4> }, `1 {} ]>
>       = @call_indirect(fnptr2, captures2, xs2);
>     let struct1:
>           {
>            [ `0 { int } ],
>             box<%type_4 = [ `0 { [ `0 { int } ], box<%type_4> }, `1 {} ]>
=======
>     let cond1: int = @get_union_id<f>;
>     switch cond1 {
>     0 -> { @call_direct(mapper2, f, x) }
>     } in join join1;
>     let cond2: int = @get_union_id<go>;
>     switch cond2 {
>     0 -> { @call_direct(go11, go, xs2) }
>     } in join join2;
>     let struct3:
>           {
>            [ `0 { int } ],
>             box<%type_6 = [ `0 { [ `0 { int } ], box<%type_6> }, `1 {} ]>
>>>>>>> Stashed changes
>            ,
>           }
>       = @make_struct{ join1, join2 };
>     let unboxed1:
>           [
>              `0 {
>                  [ `0 { int } ],
<<<<<<< Updated upstream
>                   box<%type_4 = [ `0 { [ `0 { int } ], box<%type_4> }, `1 {} ]>
=======
>                   box<%type_6 = [ `0 { [ `0 { int } ], box<%type_6> }, `1 {} ]>
>>>>>>> Stashed changes
>                  ,
>                 },
>              `1 {}
>           ]
>       = @make_union<0, struct3>;
>     @make_box(unboxed1)
>   }
>   1 -> {
>     let payload: {} = @get_union_struct<inner>;
>     let struct2: {} = @make_struct{};
>     let unboxed:
>           [
>              `0 {
>                  [ `0 { int } ],
<<<<<<< Updated upstream
>                   box<%type_4 = [ `0 { [ `0 { int } ], box<%type_4> }, `1 {} ]>
=======
>                   box<%type_6 = [ `0 { [ `0 { int } ], box<%type_6> }, `1 {} ]>
>>>>>>> Stashed changes
>                  ,
>                 },
>              `1 {}
>           ]
>       = @make_union<1, struct2>;
>     @make_box(unboxed)
>   }
<<<<<<< Updated upstream
>   } in join join;
>   return join;
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
>   box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>
>   = @call_direct(l_thunk);
> 
> proc lam1(
>   captures_: box<erased>,
>    xs: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>):
>   box<%type_4 = [ `0 { [ `0 { int } ], box<%type_4> }, `1 {} ]>
> {
>   let captures_box: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_ as box<{ { *fn, box<erased> } }>);
>   let captures_stack: { { *fn, box<erased> } } = @get_boxed<captures_box>;
>   let f: { *fn, box<erased> } = @get_struct_field<captures_stack, 0>;
>   let captures_stack_2: { { *fn, box<erased> } } = @make_struct{ f };
>   let captures_box_2: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_2);
>   let captures_5: box<erased> = @ptr_cast(captures_box_2 as box<erased>);
>   let fn_ptr_2: *fn = @make_fn_ptr<go11>;
>   let go: { *fn, box<erased> } = @make_struct{ fn_ptr_2, captures_5 };
>   let fnptr: *fn = @get_struct_field<go, 0>;
>   let captures: box<erased> = @get_struct_field<go, 1>;
>   let var: box<%type_4 = [ `0 { [ `0 { int } ], box<%type_4> }, `1 {} ]>
>     = @call_indirect(fnptr, captures, xs);
>   return var;
> }
> 
> global mapper2: { *fn, box<erased> } = @call_direct(mapper2_thunk);
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
> proc map2_thunk(): { *fn, box<erased> }
=======
>   } in join join3;
>   return join3;
> }
> 
> global l1:
>   box<%type_7 = [ `0 { int, box<%type_7> }, `1 {} ]>
>   = @call_direct(l_thunk);
> 
> proc lam1(
>   captures_: [ `0 { [ `0 {} ] } ],
>    xs: box<%type_5 = [ `0 { int, box<%type_5> }, `1 {} ]>):
>   box<%type_6 = [ `0 { [ `0 { int } ], box<%type_6> }, `1 {} ]>
>>>>>>> Stashed changes
> {
>   let captures_stack: { [ `0 {} ] } = @get_union_struct<captures_>;
>   let f: [ `0 {} ] = @get_struct_field<captures_stack, 0>;
>   let struct: { [ `0 {} ] } = @make_struct{ f };
>   let go: [ `0 { [ `0 {} ] } ] = @make_union<0, struct>;
>   let cond: int = @get_union_id<go>;
>   switch cond {
>   0 -> { @call_direct(go11, go, xs) }
>   } in join join;
>   return join;
> }
> 
> proc main_thunk():
>   box<%type_7 = [ `0 { [ `0 { int } ], box<%type_7> }, `1 {} ]>
> {
<<<<<<< Updated upstream
>   let fnptr3: *fn = @get_struct_field<map2, 0>;
>   let captures3: box<erased> = @get_struct_field<map2, 1>;
>   let var10: { *fn, box<erased> } = @call_indirect(fnptr3, captures3, mapper2);
>   let fnptr4: *fn = @get_struct_field<var10, 0>;
>   let captures4: box<erased> = @get_struct_field<var10, 1>;
>   let var11: box<%type_7 = [ `0 { [ `0 { int } ], box<%type_7> }, `1 {} ]>
>     = @call_indirect(fnptr4, captures4, l1);
>   return var11;
> }
> 
> global main:
>   box<%type_6 = [ `0 { [ `0 { int } ], box<%type_6> }, `1 {} ]>
=======
>   let struct9: {} = @make_struct{};
>   let var7: [ `0 {} ] = @make_union<0, struct9>;
>   let struct10: {} = @make_struct{};
>   let var8: [ `0 {} ] = @make_union<0, struct10>;
>   let cond3: int = @get_union_id<var7>;
>   switch cond3 {
>   0 -> { @call_direct(map2, var7, var8) }
>   } in join join4;
>   let cond4: int = @get_union_id<join4>;
>   switch cond4 {
>   0 -> { @call_direct(lam1, join4, l1) }
>   } in join join5;
>   return join5;
> }
> 
> global main:
>   box<%type_8 = [ `0 { [ `0 { int } ], box<%type_8> }, `1 {} ]>
>>>>>>> Stashed changes
>   = @call_direct(main_thunk);
> 
> entry main;

> cor-out +eval -print
> main = [0 [0 1] [0 [0 2] [1]]]
>      > Cons (A 1) (Cons (A 2) (Nil ))