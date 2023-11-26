# cor +solve -elab
# cor +ir -print
# cor +eval -print

let succeed = \ok -> \toNext -> toNext (Ok ok);;

let fail = \err-> \toNext -> toNext (Err err);;

let await = \fromResult -> \next ->
    \continue -> fromResult (\result ->
        let inner = when result is
            | Ok v -> next v
            | Err e -> fail e
        end
        in
        inner continue)
;;


let outLine = \s -> (\toNext -> StdoutLine s (\x -> toNext (Ok x)));;

let inLine = \toNext -> StdinLine (\s -> toNext (Ok s));;

let main =
    await (outLine "What's your first name?")
        (\x -> await (inLine)
            (\firstName -> await (outLine "What's your last name?")
                (\y -> await (inLine)
                    (\lastName -> outLine (~str_concat "Hello " firstName " " lastName "!")))))
;;

run main_handler =
#   ^^^^^^^^^^^^
    let op = main (\x -> Done x) in
#       ^^
    let handle = \op -> \i -> \t -> when op is
#       ^^^^^^
        | StdinLine f -> handle (f (~str_concat "stdin" (~itos i))) (~add i 1) (Stdin t)
        | StdoutLine s f -> handle (f {}) (~add i 1) (Stdout s t)
        | Done x -> Done x t
    end
    in
    handle op 0 EntryPoint
;;

> cor-out +solve -elab
> 
> let succeed = \ok -> \toNext -> toNext (Ok ok);;
> 
> let fail = \err-> \toNext -> toNext (Err err);;
> 
> let await = \fromResult -> \next ->
>     \continue -> fromResult (\result ->
>         let inner = when result is
>             | Ok v -> next v
>             | Err e -> fail e
>         end
>         in
>         inner continue)
> ;;
> 
> 
> let outLine = \s -> (\toNext -> StdoutLine s (\x -> toNext (Ok x)));;
> 
> let inLine = \toNext -> StdinLine (\s -> toNext (Ok s));;
> 
> let main =
>     await (outLine "What's your first name?")
>         (\x -> await (inLine)
>             (\firstName -> await (outLine "What's your last name?")
>                 (\y -> await (inLine)
>                     (\lastName -> outLine (~str_concat "Hello " firstName " " lastName "!")))))
> ;;
> 
> run main_handler =
> #   ^^^^^^^^^^^^ [
> #   ^^^^^^^^^^^^   Done [Err ?*, Ok {}]?*
> #   ^^^^^^^^^^^^     [
> #   ^^^^^^^^^^^^       EntryPoint,
> #   ^^^^^^^^^^^^       Stdin
> #   ^^^^^^^^^^^^         <..[EntryPoint, Stdin .., Stdout .. ..]?*>,
> #   ^^^^^^^^^^^^       Stdout Str
> #   ^^^^^^^^^^^^         <..[EntryPoint, Stdin .., Stdout .. ..]?*>
> #   ^^^^^^^^^^^^       ]?*
> #   ^^^^^^^^^^^^   ]?*
>     let op = main (\x -> Done x) in
> #       ^^ %[
> #       ^^    Done [Err ?*, Ok {}]?*,
> #       ^^    StdinLine
> #       ^^      (Str
> #       ^^        -> %<..[
> #       ^^                 Done ..,
> #       ^^                 StdinLine ..,
> #       ^^                 StdoutLine .. ..
> #       ^^                 ]<?2099>>),
> #       ^^    StdoutLine Str
> #       ^^      ({}
> #       ^^        -> %<..[
> #       ^^                 Done ..,
> #       ^^                 StdinLine ..,
> #       ^^                 StdoutLine .. ..
> #       ^^                 ]<?2099>>)
> #       ^^    ]?*
>     let handle = \op -> \i -> \t -> when op is
> #       ^^^^^^ %[
> #       ^^^^^^    Done [Err ?a, Ok {}]?b,
> #       ^^^^^^    StdinLine
> #       ^^^^^^      (Str
> #       ^^^^^^        -> %<..[
> #       ^^^^^^                 Done ..,
> #       ^^^^^^                 StdinLine ..,
> #       ^^^^^^                 StdoutLine .. ..
> #       ^^^^^^                 ]<?2099>>),
> #       ^^^^^^    StdoutLine Str
> #       ^^^^^^      ({}
> #       ^^^^^^        -> %<..[
> #       ^^^^^^                 Done ..,
> #       ^^^^^^                 StdinLine ..,
> #       ^^^^^^                 StdoutLine .. ..
> #       ^^^^^^                 ]<?2099>>)
> #       ^^^^^^    ]?*
> #       ^^^^^^   -> Int
> #       ^^^^^^        -> [
> #       ^^^^^^             EntryPoint,
> #       ^^^^^^             Stdin
> #       ^^^^^^               <..[
> #       ^^^^^^                    EntryPoint,
> #       ^^^^^^                    Stdin ..,
> #       ^^^^^^                    Stdout .. ..
> #       ^^^^^^                    ]?c>,
> #       ^^^^^^             Stdout Str
> #       ^^^^^^               <..[
> #       ^^^^^^                    EntryPoint,
> #       ^^^^^^                    Stdin ..,
> #       ^^^^^^                    Stdout .. ..
> #       ^^^^^^                    ]?c>
> #       ^^^^^^             ]?c
> #       ^^^^^^             -> [
> #       ^^^^^^                  Done [Err ?a, Ok {}]?b
> #       ^^^^^^                    [
> #       ^^^^^^                      EntryPoint,
> #       ^^^^^^                      Stdin
> #       ^^^^^^                        <..[
> #       ^^^^^^                             EntryPoint,
> #       ^^^^^^                             Stdin ..,
> #       ^^^^^^                             Stdout .. ..
> #       ^^^^^^                             ]?c>,
> #       ^^^^^^                      Stdout Str
> #       ^^^^^^                        <..[
> #       ^^^^^^                             EntryPoint,
> #       ^^^^^^                             Stdin ..,
> #       ^^^^^^                             Stdout .. ..
> #       ^^^^^^                             ]?c>
> #       ^^^^^^                      ]?c
> #       ^^^^^^                  ]?*
>         | StdinLine f -> handle (f (~str_concat "stdin" (~itos i))) (~add i 1) (Stdin t)
>         | StdoutLine s f -> handle (f {}) (~add i 1) (Stdout s t)
>         | Done x -> Done x t
>     end
>     in
>     handle op 0 EntryPoint
> ;;
> 

> cor-out +ir -print
> global fail1: { *fn, box<erased> } = @call_direct(fail_thunk);
> 
> proc fail_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_: {} = @make_struct{};
>   let captures_box_: box<{}> = @make_box(captures_stack_);
>   let captures_: box<erased> = @ptr_cast(captures_box_ as box<erased>);
>   let fn_ptr_: *fn = @make_fn_ptr<clos_>;
>   let fail_closure: { *fn, box<erased> } = @make_struct{ fn_ptr_, captures_ };
>   return fail_closure;
> }
> 
> proc clos_54(captures_109: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box1: box<{ [] }> = @ptr_cast(captures_109 as box<{ [] }>);
>   let captures_stack1: { [] } = @get_boxed<captures_box1>;
>   let err: [] = @get_struct_field<captures_stack1, 0>;
>   let fnptr: *fn = @get_struct_field<toNext1, 0>;
>   let captures: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct: { [] } = @make_struct{ err };
>   let var1: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct>;
>   let var2:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr, captures, var1);
>   return var2;
> }
> 
> proc clos_(captures_1: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box: box<{}> = @ptr_cast(captures_1 as box<{}>);
>   let captures_stack: {} = @get_boxed<captures_box>;
>   let captures_stack_54: { [] } = @make_struct{ err };
>   let captures_box_54: box<{ [] }> = @make_box(captures_stack_54);
>   let captures_108: box<erased> = @ptr_cast(captures_box_54 as box<erased>);
>   let fn_ptr_54: *fn = @make_fn_ptr<clos_54>;
>   let var: { *fn, box<erased> } = @make_struct{ fn_ptr_54, captures_108 };
>   return var;
> }
> 
> global fail2: { *fn, box<erased> } = @call_direct(fail_thunk1);
> 
> proc fail_thunk1(): { *fn, box<erased> }
> {
>   let captures_stack_1: {} = @make_struct{};
>   let captures_box_1: box<{}> = @make_box(captures_stack_1);
>   let captures_2: box<erased> = @ptr_cast(captures_box_1 as box<erased>);
>   let fn_ptr_1: *fn = @make_fn_ptr<clos_1>;
>   let fail_closure1: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_1, captures_2 };
>   return fail_closure1;
> }
> 
> proc clos_55(captures_111: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box3: box<{ [] }> = @ptr_cast(captures_111 as box<{ [] }>);
>   let captures_stack3: { [] } = @get_boxed<captures_box3>;
>   let err: [] = @get_struct_field<captures_stack3, 0>;
>   let fnptr1: *fn = @get_struct_field<toNext1, 0>;
>   let captures1: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct1: { [] } = @make_struct{ err };
>   let var4: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct1>;
>   let var5:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr1, captures1, var4);
>   return var5;
> }
> 
> proc clos_1(captures_3: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box2: box<{}> = @ptr_cast(captures_3 as box<{}>);
>   let captures_stack2: {} = @get_boxed<captures_box2>;
>   let captures_stack_55: { [] } = @make_struct{ err };
>   let captures_box_55: box<{ [] }> = @make_box(captures_stack_55);
>   let captures_110: box<erased> = @ptr_cast(captures_box_55 as box<erased>);
>   let fn_ptr_55: *fn = @make_fn_ptr<clos_55>;
>   let var3: { *fn, box<erased> } = @make_struct{ fn_ptr_55, captures_110 };
>   return var3;
> }
> 
> global fail3: { *fn, box<erased> } = @call_direct(fail_thunk2);
> 
> proc fail_thunk2(): { *fn, box<erased> }
> {
>   let captures_stack_2: {} = @make_struct{};
>   let captures_box_2: box<{}> = @make_box(captures_stack_2);
>   let captures_4: box<erased> = @ptr_cast(captures_box_2 as box<erased>);
>   let fn_ptr_2: *fn = @make_fn_ptr<clos_2>;
>   let fail_closure2: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_2, captures_4 };
>   return fail_closure2;
> }
> 
> proc clos_56(captures_113: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box5: box<{ [] }> = @ptr_cast(captures_113 as box<{ [] }>);
>   let captures_stack5: { [] } = @get_boxed<captures_box5>;
>   let err: [] = @get_struct_field<captures_stack5, 0>;
>   let fnptr2: *fn = @get_struct_field<toNext1, 0>;
>   let captures2: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct2: { [] } = @make_struct{ err };
>   let var7: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct2>;
>   let var8:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr2, captures2, var7);
>   return var8;
> }
> 
> proc clos_2(captures_5: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box4: box<{}> = @ptr_cast(captures_5 as box<{}>);
>   let captures_stack4: {} = @get_boxed<captures_box4>;
>   let captures_stack_56: { [] } = @make_struct{ err };
>   let captures_box_56: box<{ [] }> = @make_box(captures_stack_56);
>   let captures_112: box<erased> = @ptr_cast(captures_box_56 as box<erased>);
>   let fn_ptr_56: *fn = @make_fn_ptr<clos_56>;
>   let var6: { *fn, box<erased> } = @make_struct{ fn_ptr_56, captures_112 };
>   return var6;
> }
> 
> global fail4: { *fn, box<erased> } = @call_direct(fail_thunk3);
> 
> proc fail_thunk3(): { *fn, box<erased> }
> {
>   let captures_stack_3: {} = @make_struct{};
>   let captures_box_3: box<{}> = @make_box(captures_stack_3);
>   let captures_6: box<erased> = @ptr_cast(captures_box_3 as box<erased>);
>   let fn_ptr_3: *fn = @make_fn_ptr<clos_3>;
>   let fail_closure3: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_3, captures_6 };
>   return fail_closure3;
> }
> 
> proc clos_57(captures_115: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box7: box<{ [] }> = @ptr_cast(captures_115 as box<{ [] }>);
>   let captures_stack7: { [] } = @get_boxed<captures_box7>;
>   let err: [] = @get_struct_field<captures_stack7, 0>;
>   let fnptr3: *fn = @get_struct_field<toNext1, 0>;
>   let captures3: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct3: { [] } = @make_struct{ err };
>   let var10: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct3>;
>   let var11:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr3, captures3, var10);
>   return var11;
> }
> 
> proc clos_3(captures_7: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box6: box<{}> = @ptr_cast(captures_7 as box<{}>);
>   let captures_stack6: {} = @get_boxed<captures_box6>;
>   let captures_stack_57: { [] } = @make_struct{ err };
>   let captures_box_57: box<{ [] }> = @make_box(captures_stack_57);
>   let captures_114: box<erased> = @ptr_cast(captures_box_57 as box<erased>);
>   let fn_ptr_57: *fn = @make_fn_ptr<clos_57>;
>   let var9: { *fn, box<erased> } = @make_struct{ fn_ptr_57, captures_114 };
>   return var9;
> }
> 
> global fail5: { *fn, box<erased> } = @call_direct(fail_thunk4);
> 
> proc fail_thunk4(): { *fn, box<erased> }
> {
>   let captures_stack_4: {} = @make_struct{};
>   let captures_box_4: box<{}> = @make_box(captures_stack_4);
>   let captures_8: box<erased> = @ptr_cast(captures_box_4 as box<erased>);
>   let fn_ptr_4: *fn = @make_fn_ptr<clos_4>;
>   let fail_closure4: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_4, captures_8 };
>   return fail_closure4;
> }
> 
> proc clos_58(captures_117: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box9: box<{ [] }> = @ptr_cast(captures_117 as box<{ [] }>);
>   let captures_stack9: { [] } = @get_boxed<captures_box9>;
>   let err: [] = @get_struct_field<captures_stack9, 0>;
>   let fnptr4: *fn = @get_struct_field<toNext1, 0>;
>   let captures4: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct4: { [] } = @make_struct{ err };
>   let var13: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct4>;
>   let var14:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr4, captures4, var13);
>   return var14;
> }
> 
> proc clos_4(captures_9: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box8: box<{}> = @ptr_cast(captures_9 as box<{}>);
>   let captures_stack8: {} = @get_boxed<captures_box8>;
>   let captures_stack_58: { [] } = @make_struct{ err };
>   let captures_box_58: box<{ [] }> = @make_box(captures_stack_58);
>   let captures_116: box<erased> = @ptr_cast(captures_box_58 as box<erased>);
>   let fn_ptr_58: *fn = @make_fn_ptr<clos_58>;
>   let var12: { *fn, box<erased> } = @make_struct{ fn_ptr_58, captures_116 };
>   return var12;
> }
> 
> global await1: { *fn, box<erased> } = @call_direct(await_thunk);
> 
> proc await_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_5: { { *fn, box<erased> } } = @make_struct{ fail5 };
>   let captures_box_5: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_5);
>   let captures_10: box<erased> = @ptr_cast(captures_box_5 as box<erased>);
>   let fn_ptr_5: *fn = @make_fn_ptr<clos_5>;
>   let await_closure: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_5, captures_10 };
>   return await_closure;
> }
> 
> proc clos_61(captures_123: box<erased>, result: [ `0 { [] }, `1 { {} } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box13:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_123 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack13:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box13>;
>   let continue: { *fn, box<erased> } = @get_struct_field<captures_stack13, 0>;
>   let fail2: { *fn, box<erased> } = @get_struct_field<captures_stack13, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack13, 2>;
>   let discr: int = @get_union_id<result>;
>   switch discr {
>   0 -> {
>     let payload1: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload1, 0>;
>     let fnptr7: *fn = @get_struct_field<fail1, 0>;
>     let captures7: box<erased> = @get_struct_field<fail1, 1>;
>     @call_indirect(fnptr7, captures7, e)
>   }
>   1 -> {
>     let payload: { {} } = @get_union_struct<result>;
>     let v: {} = @get_struct_field<payload, 0>;
>     let fnptr6: *fn = @get_struct_field<next, 0>;
>     let captures6: box<erased> = @get_struct_field<next, 1>;
>     @call_indirect(fnptr6, captures6, v)
>   }
>   } in join join;
>   let inner: { *fn, box<erased> } = join;
>   let fnptr8: *fn = @get_struct_field<inner, 0>;
>   let captures8: box<erased> = @get_struct_field<inner, 1>;
>   let var19:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr8, captures8, continue);
>   return var19;
> }
> 
> proc clos_60(captures_121: box<erased>, continue: { *fn, box<erased> }):
>   box<
>     %type_3 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box12:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_121 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack12:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box12>;
>   let fail3: { *fn, box<erased> } = @get_struct_field<captures_stack12, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack12, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack12, 2>;
>   let fnptr5: *fn = @get_struct_field<fromResult, 0>;
>   let captures5: box<erased> = @get_struct_field<fromResult, 1>;
>   let captures_stack_61:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ continue, fail2, next };
>   let captures_box_61:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_61);
>   let captures_122: box<erased> = @ptr_cast(captures_box_61 as box<erased>);
>   let fn_ptr_61: *fn = @make_fn_ptr<clos_61>;
>   let var17: { *fn, box<erased> } = @make_struct{ fn_ptr_61, captures_122 };
>   let var18:
>         box<
>           %type_3 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr5, captures5, var17);
>   return var18;
> }
> 
> proc clos_59(captures_119: box<erased>, next: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box11: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_119 as
>         box<{ { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack11: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box11>;
>   let fail4: { *fn, box<erased> } = @get_struct_field<captures_stack11, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack11, 1>;
>   let captures_stack_60:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail3, fromResult, next };
>   let captures_box_60:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_60);
>   let captures_120: box<erased> = @ptr_cast(captures_box_60 as box<erased>);
>   let fn_ptr_60: *fn = @make_fn_ptr<clos_60>;
>   let var16: { *fn, box<erased> } = @make_struct{ fn_ptr_60, captures_120 };
>   return var16;
> }
> 
> proc clos_5(captures_11: box<erased>, fromResult: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box10: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_11 as box<{ { *fn, box<erased> } }>);
>   let captures_stack10: { { *fn, box<erased> } } = @get_boxed<captures_box10>;
>   let fail5: { *fn, box<erased> } = @get_struct_field<captures_stack10, 0>;
>   let captures_stack_59: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail4, fromResult };
>   let captures_box_59: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_59);
>   let captures_118: box<erased> = @ptr_cast(captures_box_59 as box<erased>);
>   let fn_ptr_59: *fn = @make_fn_ptr<clos_59>;
>   let var15: { *fn, box<erased> } = @make_struct{ fn_ptr_59, captures_118 };
>   return var15;
> }
> 
> global outLine1: { *fn, box<erased> } = @call_direct(outLine_thunk);
> 
> proc outLine_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_6: {} = @make_struct{};
>   let captures_box_6: box<{}> = @make_box(captures_stack_6);
>   let captures_12: box<erased> = @ptr_cast(captures_box_6 as box<erased>);
>   let fn_ptr_6: *fn = @make_fn_ptr<clos_6>;
>   let outLine_closure: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_6, captures_12 };
>   return outLine_closure;
> }
> 
> proc clos_63(captures_127: box<erased>, x: {}):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box16: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_127 as box<{ { *fn, box<erased> } }>);
>   let captures_stack16: { { *fn, box<erased> } } = @get_boxed<captures_box16>;
>   let toNext2: { *fn, box<erased> } = @get_struct_field<captures_stack16, 0>;
>   let fnptr9: *fn = @get_struct_field<toNext2, 0>;
>   let captures9: box<erased> = @get_struct_field<toNext2, 1>;
>   let struct6: { {} } = @make_struct{ x };
>   let var23: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct6>;
>   let var24:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr9, captures9, var23);
>   return var24;
> }
> 
> proc clos_62(captures_125: box<erased>, toNext2: { *fn, box<erased> }):
>   box<
>     %type_3 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box15: box<{ str }> = @ptr_cast(captures_125 as box<{ str }>);
>   let captures_stack15: { str } = @get_boxed<captures_box15>;
>   let s: str = @get_struct_field<captures_stack15, 0>;
>   let captures_stack_63: { { *fn, box<erased> } } = @make_struct{ toNext2 };
>   let captures_box_63: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_63);
>   let captures_126: box<erased> = @ptr_cast(captures_box_63 as box<erased>);
>   let fn_ptr_63: *fn = @make_fn_ptr<clos_63>;
>   let unboxed: { *fn, box<erased> } = @make_struct{ fn_ptr_63, captures_126 };
>   let var21: box<%type_1 = { *fn, box<erased> }> = @make_box(unboxed);
>   let struct5: { str, box<%type_1 = { *fn, box<erased> }> }
>     = @make_struct{ s, var21 };
>   let unboxed1:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<2, struct5>;
>   let var22:
>         box<
>           %type_3 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed1);
>   return var22;
> }
> 
> proc clos_6(captures_13: box<erased>, s: str): { *fn, box<erased> }
> {
>   let captures_box14: box<{}> = @ptr_cast(captures_13 as box<{}>);
>   let captures_stack14: {} = @get_boxed<captures_box14>;
>   let captures_stack_62: { str } = @make_struct{ s };
>   let captures_box_62: box<{ str }> = @make_box(captures_stack_62);
>   let captures_124: box<erased> = @ptr_cast(captures_box_62 as box<erased>);
>   let fn_ptr_62: *fn = @make_fn_ptr<clos_62>;
>   let var20: { *fn, box<erased> } = @make_struct{ fn_ptr_62, captures_124 };
>   return var20;
> }
> 
> global fail6: { *fn, box<erased> } = @call_direct(fail_thunk5);
> 
> proc fail_thunk5(): { *fn, box<erased> }
> {
>   let captures_stack_7: {} = @make_struct{};
>   let captures_box_7: box<{}> = @make_box(captures_stack_7);
>   let captures_14: box<erased> = @ptr_cast(captures_box_7 as box<erased>);
>   let fn_ptr_7: *fn = @make_fn_ptr<clos_7>;
>   let fail_closure5: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_7, captures_14 };
>   return fail_closure5;
> }
> 
> proc clos_64(captures_129: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box18: box<{ [] }> = @ptr_cast(captures_129 as box<{ [] }>);
>   let captures_stack18: { [] } = @get_boxed<captures_box18>;
>   let err: [] = @get_struct_field<captures_stack18, 0>;
>   let fnptr10: *fn = @get_struct_field<toNext1, 0>;
>   let captures10: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct7: { [] } = @make_struct{ err };
>   let var26: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct7>;
>   let var27:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr10, captures10, var26);
>   return var27;
> }
> 
> proc clos_7(captures_15: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box17: box<{}> = @ptr_cast(captures_15 as box<{}>);
>   let captures_stack17: {} = @get_boxed<captures_box17>;
>   let captures_stack_64: { [] } = @make_struct{ err };
>   let captures_box_64: box<{ [] }> = @make_box(captures_stack_64);
>   let captures_128: box<erased> = @ptr_cast(captures_box_64 as box<erased>);
>   let fn_ptr_64: *fn = @make_fn_ptr<clos_64>;
>   let var25: { *fn, box<erased> } = @make_struct{ fn_ptr_64, captures_128 };
>   return var25;
> }
> 
> global fail7: { *fn, box<erased> } = @call_direct(fail_thunk6);
> 
> proc fail_thunk6(): { *fn, box<erased> }
> {
>   let captures_stack_8: {} = @make_struct{};
>   let captures_box_8: box<{}> = @make_box(captures_stack_8);
>   let captures_16: box<erased> = @ptr_cast(captures_box_8 as box<erased>);
>   let fn_ptr_8: *fn = @make_fn_ptr<clos_8>;
>   let fail_closure6: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_8, captures_16 };
>   return fail_closure6;
> }
> 
> proc clos_65(captures_131: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box20: box<{ [] }> = @ptr_cast(captures_131 as box<{ [] }>);
>   let captures_stack20: { [] } = @get_boxed<captures_box20>;
>   let err: [] = @get_struct_field<captures_stack20, 0>;
>   let fnptr11: *fn = @get_struct_field<toNext1, 0>;
>   let captures11: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct8: { [] } = @make_struct{ err };
>   let var29: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct8>;
>   let var30:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr11, captures11, var29);
>   return var30;
> }
> 
> proc clos_8(captures_17: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box19: box<{}> = @ptr_cast(captures_17 as box<{}>);
>   let captures_stack19: {} = @get_boxed<captures_box19>;
>   let captures_stack_65: { [] } = @make_struct{ err };
>   let captures_box_65: box<{ [] }> = @make_box(captures_stack_65);
>   let captures_130: box<erased> = @ptr_cast(captures_box_65 as box<erased>);
>   let fn_ptr_65: *fn = @make_fn_ptr<clos_65>;
>   let var28: { *fn, box<erased> } = @make_struct{ fn_ptr_65, captures_130 };
>   return var28;
> }
> 
> global fail8: { *fn, box<erased> } = @call_direct(fail_thunk7);
> 
> proc fail_thunk7(): { *fn, box<erased> }
> {
>   let captures_stack_9: {} = @make_struct{};
>   let captures_box_9: box<{}> = @make_box(captures_stack_9);
>   let captures_18: box<erased> = @ptr_cast(captures_box_9 as box<erased>);
>   let fn_ptr_9: *fn = @make_fn_ptr<clos_9>;
>   let fail_closure7: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_9, captures_18 };
>   return fail_closure7;
> }
> 
> proc clos_66(captures_133: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box22: box<{ [] }> = @ptr_cast(captures_133 as box<{ [] }>);
>   let captures_stack22: { [] } = @get_boxed<captures_box22>;
>   let err: [] = @get_struct_field<captures_stack22, 0>;
>   let fnptr12: *fn = @get_struct_field<toNext1, 0>;
>   let captures12: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct9: { [] } = @make_struct{ err };
>   let var32: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct9>;
>   let var33:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr12, captures12, var32);
>   return var33;
> }
> 
> proc clos_9(captures_19: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box21: box<{}> = @ptr_cast(captures_19 as box<{}>);
>   let captures_stack21: {} = @get_boxed<captures_box21>;
>   let captures_stack_66: { [] } = @make_struct{ err };
>   let captures_box_66: box<{ [] }> = @make_box(captures_stack_66);
>   let captures_132: box<erased> = @ptr_cast(captures_box_66 as box<erased>);
>   let fn_ptr_66: *fn = @make_fn_ptr<clos_66>;
>   let var31: { *fn, box<erased> } = @make_struct{ fn_ptr_66, captures_132 };
>   return var31;
> }
> 
> global fail9: { *fn, box<erased> } = @call_direct(fail_thunk8);
> 
> proc fail_thunk8(): { *fn, box<erased> }
> {
>   let captures_stack_10: {} = @make_struct{};
>   let captures_box_10: box<{}> = @make_box(captures_stack_10);
>   let captures_20: box<erased> = @ptr_cast(captures_box_10 as box<erased>);
>   let fn_ptr_10: *fn = @make_fn_ptr<clos_10>;
>   let fail_closure8: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_10, captures_20 };
>   return fail_closure8;
> }
> 
> proc clos_67(captures_135: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box24: box<{ [] }> = @ptr_cast(captures_135 as box<{ [] }>);
>   let captures_stack24: { [] } = @get_boxed<captures_box24>;
>   let err: [] = @get_struct_field<captures_stack24, 0>;
>   let fnptr13: *fn = @get_struct_field<toNext1, 0>;
>   let captures13: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct10: { [] } = @make_struct{ err };
>   let var35: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct10>;
>   let var36:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr13, captures13, var35);
>   return var36;
> }
> 
> proc clos_10(captures_21: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box23: box<{}> = @ptr_cast(captures_21 as box<{}>);
>   let captures_stack23: {} = @get_boxed<captures_box23>;
>   let captures_stack_67: { [] } = @make_struct{ err };
>   let captures_box_67: box<{ [] }> = @make_box(captures_stack_67);
>   let captures_134: box<erased> = @ptr_cast(captures_box_67 as box<erased>);
>   let fn_ptr_67: *fn = @make_fn_ptr<clos_67>;
>   let var34: { *fn, box<erased> } = @make_struct{ fn_ptr_67, captures_134 };
>   return var34;
> }
> 
> global fail10: { *fn, box<erased> } = @call_direct(fail_thunk9);
> 
> proc fail_thunk9(): { *fn, box<erased> }
> {
>   let captures_stack_11: {} = @make_struct{};
>   let captures_box_11: box<{}> = @make_box(captures_stack_11);
>   let captures_22: box<erased> = @ptr_cast(captures_box_11 as box<erased>);
>   let fn_ptr_11: *fn = @make_fn_ptr<clos_11>;
>   let fail_closure9: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_11, captures_22 };
>   return fail_closure9;
> }
> 
> proc clos_68(captures_137: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box26: box<{ [] }> = @ptr_cast(captures_137 as box<{ [] }>);
>   let captures_stack26: { [] } = @get_boxed<captures_box26>;
>   let err: [] = @get_struct_field<captures_stack26, 0>;
>   let fnptr14: *fn = @get_struct_field<toNext1, 0>;
>   let captures14: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct11: { [] } = @make_struct{ err };
>   let var38: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct11>;
>   let var39:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr14, captures14, var38);
>   return var39;
> }
> 
> proc clos_11(captures_23: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box25: box<{}> = @ptr_cast(captures_23 as box<{}>);
>   let captures_stack25: {} = @get_boxed<captures_box25>;
>   let captures_stack_68: { [] } = @make_struct{ err };
>   let captures_box_68: box<{ [] }> = @make_box(captures_stack_68);
>   let captures_136: box<erased> = @ptr_cast(captures_box_68 as box<erased>);
>   let fn_ptr_68: *fn = @make_fn_ptr<clos_68>;
>   let var37: { *fn, box<erased> } = @make_struct{ fn_ptr_68, captures_136 };
>   return var37;
> }
> 
> global await2: { *fn, box<erased> } = @call_direct(await_thunk1);
> 
> proc await_thunk1(): { *fn, box<erased> }
> {
>   let captures_stack_12: { { *fn, box<erased> } } = @make_struct{ fail10 };
>   let captures_box_12: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_12);
>   let captures_24: box<erased> = @ptr_cast(captures_box_12 as box<erased>);
>   let fn_ptr_12: *fn = @make_fn_ptr<clos_12>;
>   let await_closure1: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_12, captures_24 };
>   return await_closure1;
> }
> 
> proc clos_71(captures_143: box<erased>, result: [ `0 { [] }, `1 { str } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box30:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_143 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack30:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box30>;
>   let continue: { *fn, box<erased> } = @get_struct_field<captures_stack30, 0>;
>   let fail7: { *fn, box<erased> } = @get_struct_field<captures_stack30, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack30, 2>;
>   let discr1: int = @get_union_id<result>;
>   switch discr1 {
>   0 -> {
>     let payload3: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload3, 0>;
>     let fnptr17: *fn = @get_struct_field<fail6, 0>;
>     let captures17: box<erased> = @get_struct_field<fail6, 1>;
>     @call_indirect(fnptr17, captures17, e)
>   }
>   1 -> {
>     let payload2: { str } = @get_union_struct<result>;
>     let v: str = @get_struct_field<payload2, 0>;
>     let fnptr16: *fn = @get_struct_field<next, 0>;
>     let captures16: box<erased> = @get_struct_field<next, 1>;
>     @call_indirect(fnptr16, captures16, v)
>   }
>   } in join join1;
>   let inner: { *fn, box<erased> } = join1;
>   let fnptr18: *fn = @get_struct_field<inner, 0>;
>   let captures18: box<erased> = @get_struct_field<inner, 1>;
>   let var44:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr18, captures18, continue);
>   return var44;
> }
> 
> proc clos_70(captures_141: box<erased>, continue: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box29:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_141 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack29:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box29>;
>   let fail8: { *fn, box<erased> } = @get_struct_field<captures_stack29, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack29, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack29, 2>;
>   let fnptr15: *fn = @get_struct_field<fromResult, 0>;
>   let captures15: box<erased> = @get_struct_field<fromResult, 1>;
>   let captures_stack_71:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ continue, fail7, next };
>   let captures_box_71:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_71);
>   let captures_142: box<erased> = @ptr_cast(captures_box_71 as box<erased>);
>   let fn_ptr_71: *fn = @make_fn_ptr<clos_71>;
>   let var42: { *fn, box<erased> } = @make_struct{ fn_ptr_71, captures_142 };
>   let var43:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr15, captures15, var42);
>   return var43;
> }
> 
> proc clos_69(captures_139: box<erased>, next: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box28: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_139 as
>         box<{ { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack28: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box28>;
>   let fail9: { *fn, box<erased> } = @get_struct_field<captures_stack28, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack28, 1>;
>   let captures_stack_70:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail8, fromResult, next };
>   let captures_box_70:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_70);
>   let captures_140: box<erased> = @ptr_cast(captures_box_70 as box<erased>);
>   let fn_ptr_70: *fn = @make_fn_ptr<clos_70>;
>   let var41: { *fn, box<erased> } = @make_struct{ fn_ptr_70, captures_140 };
>   return var41;
> }
> 
> proc clos_12(captures_25: box<erased>, fromResult: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box27: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_25 as box<{ { *fn, box<erased> } }>);
>   let captures_stack27: { { *fn, box<erased> } } = @get_boxed<captures_box27>;
>   let fail10: { *fn, box<erased> } = @get_struct_field<captures_stack27, 0>;
>   let captures_stack_69: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail9, fromResult };
>   let captures_box_69: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_69);
>   let captures_138: box<erased> = @ptr_cast(captures_box_69 as box<erased>);
>   let fn_ptr_69: *fn = @make_fn_ptr<clos_69>;
>   let var40: { *fn, box<erased> } = @make_struct{ fn_ptr_69, captures_138 };
>   return var40;
> }
> 
> global inLine1: { *fn, box<erased> } = @call_direct(inLine_thunk);
> 
> proc inLine_thunk(): { *fn, box<erased> }
> {
>   let captures_stack_13: {} = @make_struct{};
>   let captures_box_13: box<{}> = @make_box(captures_stack_13);
>   let captures_26: box<erased> = @ptr_cast(captures_box_13 as box<erased>);
>   let fn_ptr_13: *fn = @make_fn_ptr<clos_13>;
>   let inLine_closure: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_13, captures_26 };
>   return inLine_closure;
> }
> 
> proc clos_72(captures_145: box<erased>, s1: str):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box32: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_145 as box<{ { *fn, box<erased> } }>);
>   let captures_stack32: { { *fn, box<erased> } } = @get_boxed<captures_box32>;
>   let toNext3: { *fn, box<erased> } = @get_struct_field<captures_stack32, 0>;
>   let fnptr19: *fn = @get_struct_field<toNext3, 0>;
>   let captures19: box<erased> = @get_struct_field<toNext3, 1>;
>   let struct13: { str } = @make_struct{ s1 };
>   let var47: [ `0 { [] }, `1 { str } ] = @make_union<1, struct13>;
>   let var48:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr19, captures19, var47);
>   return var48;
> }
> 
> proc clos_13(captures_27: box<erased>, toNext3: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box31: box<{}> = @ptr_cast(captures_27 as box<{}>);
>   let captures_stack31: {} = @get_boxed<captures_box31>;
>   let captures_stack_72: { { *fn, box<erased> } } = @make_struct{ toNext3 };
>   let captures_box_72: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_72);
>   let captures_144: box<erased> = @ptr_cast(captures_box_72 as box<erased>);
>   let fn_ptr_72: *fn = @make_fn_ptr<clos_72>;
>   let var45: { *fn, box<erased> } = @make_struct{ fn_ptr_72, captures_144 };
>   let struct12: { { *fn, box<erased> } } = @make_struct{ var45 };
>   let unboxed2:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<1, struct12>;
>   let var46:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed2);
>   return var46;
> }
> 
> global fail11: { *fn, box<erased> } = @call_direct(fail_thunk10);
> 
> proc fail_thunk10(): { *fn, box<erased> }
> {
>   let captures_stack_14: {} = @make_struct{};
>   let captures_box_14: box<{}> = @make_box(captures_stack_14);
>   let captures_28: box<erased> = @ptr_cast(captures_box_14 as box<erased>);
>   let fn_ptr_14: *fn = @make_fn_ptr<clos_14>;
>   let fail_closure10: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_14, captures_28 };
>   return fail_closure10;
> }
> 
> proc clos_73(captures_147: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box34: box<{ [] }> = @ptr_cast(captures_147 as box<{ [] }>);
>   let captures_stack34: { [] } = @get_boxed<captures_box34>;
>   let err: [] = @get_struct_field<captures_stack34, 0>;
>   let fnptr20: *fn = @get_struct_field<toNext1, 0>;
>   let captures20: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct14: { [] } = @make_struct{ err };
>   let var50: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct14>;
>   let var51:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr20, captures20, var50);
>   return var51;
> }
> 
> proc clos_14(captures_29: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box33: box<{}> = @ptr_cast(captures_29 as box<{}>);
>   let captures_stack33: {} = @get_boxed<captures_box33>;
>   let captures_stack_73: { [] } = @make_struct{ err };
>   let captures_box_73: box<{ [] }> = @make_box(captures_stack_73);
>   let captures_146: box<erased> = @ptr_cast(captures_box_73 as box<erased>);
>   let fn_ptr_73: *fn = @make_fn_ptr<clos_73>;
>   let var49: { *fn, box<erased> } = @make_struct{ fn_ptr_73, captures_146 };
>   return var49;
> }
> 
> global fail12: { *fn, box<erased> } = @call_direct(fail_thunk11);
> 
> proc fail_thunk11(): { *fn, box<erased> }
> {
>   let captures_stack_15: {} = @make_struct{};
>   let captures_box_15: box<{}> = @make_box(captures_stack_15);
>   let captures_30: box<erased> = @ptr_cast(captures_box_15 as box<erased>);
>   let fn_ptr_15: *fn = @make_fn_ptr<clos_15>;
>   let fail_closure11: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_15, captures_30 };
>   return fail_closure11;
> }
> 
> proc clos_74(captures_149: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box36: box<{ [] }> = @ptr_cast(captures_149 as box<{ [] }>);
>   let captures_stack36: { [] } = @get_boxed<captures_box36>;
>   let err: [] = @get_struct_field<captures_stack36, 0>;
>   let fnptr21: *fn = @get_struct_field<toNext1, 0>;
>   let captures21: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct15: { [] } = @make_struct{ err };
>   let var53: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct15>;
>   let var54:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr21, captures21, var53);
>   return var54;
> }
> 
> proc clos_15(captures_31: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box35: box<{}> = @ptr_cast(captures_31 as box<{}>);
>   let captures_stack35: {} = @get_boxed<captures_box35>;
>   let captures_stack_74: { [] } = @make_struct{ err };
>   let captures_box_74: box<{ [] }> = @make_box(captures_stack_74);
>   let captures_148: box<erased> = @ptr_cast(captures_box_74 as box<erased>);
>   let fn_ptr_74: *fn = @make_fn_ptr<clos_74>;
>   let var52: { *fn, box<erased> } = @make_struct{ fn_ptr_74, captures_148 };
>   return var52;
> }
> 
> global fail13: { *fn, box<erased> } = @call_direct(fail_thunk12);
> 
> proc fail_thunk12(): { *fn, box<erased> }
> {
>   let captures_stack_16: {} = @make_struct{};
>   let captures_box_16: box<{}> = @make_box(captures_stack_16);
>   let captures_32: box<erased> = @ptr_cast(captures_box_16 as box<erased>);
>   let fn_ptr_16: *fn = @make_fn_ptr<clos_16>;
>   let fail_closure12: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_16, captures_32 };
>   return fail_closure12;
> }
> 
> proc clos_75(captures_151: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box38: box<{ [] }> = @ptr_cast(captures_151 as box<{ [] }>);
>   let captures_stack38: { [] } = @get_boxed<captures_box38>;
>   let err: [] = @get_struct_field<captures_stack38, 0>;
>   let fnptr22: *fn = @get_struct_field<toNext1, 0>;
>   let captures22: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct16: { [] } = @make_struct{ err };
>   let var56: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct16>;
>   let var57:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr22, captures22, var56);
>   return var57;
> }
> 
> proc clos_16(captures_33: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box37: box<{}> = @ptr_cast(captures_33 as box<{}>);
>   let captures_stack37: {} = @get_boxed<captures_box37>;
>   let captures_stack_75: { [] } = @make_struct{ err };
>   let captures_box_75: box<{ [] }> = @make_box(captures_stack_75);
>   let captures_150: box<erased> = @ptr_cast(captures_box_75 as box<erased>);
>   let fn_ptr_75: *fn = @make_fn_ptr<clos_75>;
>   let var55: { *fn, box<erased> } = @make_struct{ fn_ptr_75, captures_150 };
>   return var55;
> }
> 
> global fail14: { *fn, box<erased> } = @call_direct(fail_thunk13);
> 
> proc fail_thunk13(): { *fn, box<erased> }
> {
>   let captures_stack_17: {} = @make_struct{};
>   let captures_box_17: box<{}> = @make_box(captures_stack_17);
>   let captures_34: box<erased> = @ptr_cast(captures_box_17 as box<erased>);
>   let fn_ptr_17: *fn = @make_fn_ptr<clos_17>;
>   let fail_closure13: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_17, captures_34 };
>   return fail_closure13;
> }
> 
> proc clos_76(captures_153: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box40: box<{ [] }> = @ptr_cast(captures_153 as box<{ [] }>);
>   let captures_stack40: { [] } = @get_boxed<captures_box40>;
>   let err: [] = @get_struct_field<captures_stack40, 0>;
>   let fnptr23: *fn = @get_struct_field<toNext1, 0>;
>   let captures23: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct17: { [] } = @make_struct{ err };
>   let var59: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct17>;
>   let var60:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr23, captures23, var59);
>   return var60;
> }
> 
> proc clos_17(captures_35: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box39: box<{}> = @ptr_cast(captures_35 as box<{}>);
>   let captures_stack39: {} = @get_boxed<captures_box39>;
>   let captures_stack_76: { [] } = @make_struct{ err };
>   let captures_box_76: box<{ [] }> = @make_box(captures_stack_76);
>   let captures_152: box<erased> = @ptr_cast(captures_box_76 as box<erased>);
>   let fn_ptr_76: *fn = @make_fn_ptr<clos_76>;
>   let var58: { *fn, box<erased> } = @make_struct{ fn_ptr_76, captures_152 };
>   return var58;
> }
> 
> global fail15: { *fn, box<erased> } = @call_direct(fail_thunk14);
> 
> proc fail_thunk14(): { *fn, box<erased> }
> {
>   let captures_stack_18: {} = @make_struct{};
>   let captures_box_18: box<{}> = @make_box(captures_stack_18);
>   let captures_36: box<erased> = @ptr_cast(captures_box_18 as box<erased>);
>   let fn_ptr_18: *fn = @make_fn_ptr<clos_18>;
>   let fail_closure14: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_18, captures_36 };
>   return fail_closure14;
> }
> 
> proc clos_77(captures_155: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box42: box<{ [] }> = @ptr_cast(captures_155 as box<{ [] }>);
>   let captures_stack42: { [] } = @get_boxed<captures_box42>;
>   let err: [] = @get_struct_field<captures_stack42, 0>;
>   let fnptr24: *fn = @get_struct_field<toNext1, 0>;
>   let captures24: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct18: { [] } = @make_struct{ err };
>   let var62: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct18>;
>   let var63:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr24, captures24, var62);
>   return var63;
> }
> 
> proc clos_18(captures_37: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box41: box<{}> = @ptr_cast(captures_37 as box<{}>);
>   let captures_stack41: {} = @get_boxed<captures_box41>;
>   let captures_stack_77: { [] } = @make_struct{ err };
>   let captures_box_77: box<{ [] }> = @make_box(captures_stack_77);
>   let captures_154: box<erased> = @ptr_cast(captures_box_77 as box<erased>);
>   let fn_ptr_77: *fn = @make_fn_ptr<clos_77>;
>   let var61: { *fn, box<erased> } = @make_struct{ fn_ptr_77, captures_154 };
>   return var61;
> }
> 
> global await3: { *fn, box<erased> } = @call_direct(await_thunk2);
> 
> proc await_thunk2(): { *fn, box<erased> }
> {
>   let captures_stack_19: { { *fn, box<erased> } } = @make_struct{ fail15 };
>   let captures_box_19: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_19);
>   let captures_38: box<erased> = @ptr_cast(captures_box_19 as box<erased>);
>   let fn_ptr_19: *fn = @make_fn_ptr<clos_19>;
>   let await_closure2: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_19, captures_38 };
>   return await_closure2;
> }
> 
> proc clos_80(captures_161: box<erased>, result: [ `0 { [] }, `1 { {} } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box46:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_161 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack46:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box46>;
>   let continue: { *fn, box<erased> } = @get_struct_field<captures_stack46, 0>;
>   let fail12: { *fn, box<erased> } = @get_struct_field<captures_stack46, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack46, 2>;
>   let discr2: int = @get_union_id<result>;
>   switch discr2 {
>   0 -> {
>     let payload5: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload5, 0>;
>     let fnptr27: *fn = @get_struct_field<fail11, 0>;
>     let captures27: box<erased> = @get_struct_field<fail11, 1>;
>     @call_indirect(fnptr27, captures27, e)
>   }
>   1 -> {
>     let payload4: { {} } = @get_union_struct<result>;
>     let v: {} = @get_struct_field<payload4, 0>;
>     let fnptr26: *fn = @get_struct_field<next, 0>;
>     let captures26: box<erased> = @get_struct_field<next, 1>;
>     @call_indirect(fnptr26, captures26, v)
>   }
>   } in join join2;
>   let inner: { *fn, box<erased> } = join2;
>   let fnptr28: *fn = @get_struct_field<inner, 0>;
>   let captures28: box<erased> = @get_struct_field<inner, 1>;
>   let var68:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr28, captures28, continue);
>   return var68;
> }
> 
> proc clos_79(captures_159: box<erased>, continue: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box45:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_159 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack45:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box45>;
>   let fail13: { *fn, box<erased> } = @get_struct_field<captures_stack45, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack45, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack45, 2>;
>   let fnptr25: *fn = @get_struct_field<fromResult, 0>;
>   let captures25: box<erased> = @get_struct_field<fromResult, 1>;
>   let captures_stack_80:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ continue, fail12, next };
>   let captures_box_80:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_80);
>   let captures_160: box<erased> = @ptr_cast(captures_box_80 as box<erased>);
>   let fn_ptr_80: *fn = @make_fn_ptr<clos_80>;
>   let var66: { *fn, box<erased> } = @make_struct{ fn_ptr_80, captures_160 };
>   let var67:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr25, captures25, var66);
>   return var67;
> }
> 
> proc clos_78(captures_157: box<erased>, next: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box44: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_157 as
>         box<{ { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack44: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box44>;
>   let fail14: { *fn, box<erased> } = @get_struct_field<captures_stack44, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack44, 1>;
>   let captures_stack_79:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail13, fromResult, next };
>   let captures_box_79:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_79);
>   let captures_158: box<erased> = @ptr_cast(captures_box_79 as box<erased>);
>   let fn_ptr_79: *fn = @make_fn_ptr<clos_79>;
>   let var65: { *fn, box<erased> } = @make_struct{ fn_ptr_79, captures_158 };
>   return var65;
> }
> 
> proc clos_19(captures_39: box<erased>, fromResult: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box43: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_39 as box<{ { *fn, box<erased> } }>);
>   let captures_stack43: { { *fn, box<erased> } } = @get_boxed<captures_box43>;
>   let fail15: { *fn, box<erased> } = @get_struct_field<captures_stack43, 0>;
>   let captures_stack_78: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail14, fromResult };
>   let captures_box_78: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_78);
>   let captures_156: box<erased> = @ptr_cast(captures_box_78 as box<erased>);
>   let fn_ptr_78: *fn = @make_fn_ptr<clos_78>;
>   let var64: { *fn, box<erased> } = @make_struct{ fn_ptr_78, captures_156 };
>   return var64;
> }
> 
> global outLine2: { *fn, box<erased> } = @call_direct(outLine_thunk1);
> 
> proc outLine_thunk1(): { *fn, box<erased> }
> {
>   let captures_stack_20: {} = @make_struct{};
>   let captures_box_20: box<{}> = @make_box(captures_stack_20);
>   let captures_40: box<erased> = @ptr_cast(captures_box_20 as box<erased>);
>   let fn_ptr_20: *fn = @make_fn_ptr<clos_20>;
>   let outLine_closure1: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_20, captures_40 };
>   return outLine_closure1;
> }
> 
> proc clos_82(captures_165: box<erased>, x: {}):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box49: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_165 as box<{ { *fn, box<erased> } }>);
>   let captures_stack49: { { *fn, box<erased> } } = @get_boxed<captures_box49>;
>   let toNext2: { *fn, box<erased> } = @get_struct_field<captures_stack49, 0>;
>   let fnptr29: *fn = @get_struct_field<toNext2, 0>;
>   let captures29: box<erased> = @get_struct_field<toNext2, 1>;
>   let struct20: { {} } = @make_struct{ x };
>   let var72: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct20>;
>   let var73:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr29, captures29, var72);
>   return var73;
> }
> 
> proc clos_81(captures_163: box<erased>, toNext2: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box48: box<{ str }> = @ptr_cast(captures_163 as box<{ str }>);
>   let captures_stack48: { str } = @get_boxed<captures_box48>;
>   let s: str = @get_struct_field<captures_stack48, 0>;
>   let captures_stack_82: { { *fn, box<erased> } } = @make_struct{ toNext2 };
>   let captures_box_82: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_82);
>   let captures_164: box<erased> = @ptr_cast(captures_box_82 as box<erased>);
>   let fn_ptr_82: *fn = @make_fn_ptr<clos_82>;
>   let unboxed3: { *fn, box<erased> } = @make_struct{ fn_ptr_82, captures_164 };
>   let var70: box<%type_1 = { *fn, box<erased> }> = @make_box(unboxed3);
>   let struct19: { str, box<%type_1 = { *fn, box<erased> }> }
>     = @make_struct{ s, var70 };
>   let unboxed4:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<2, struct19>;
>   let var71:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed4);
>   return var71;
> }
> 
> proc clos_20(captures_41: box<erased>, s: str): { *fn, box<erased> }
> {
>   let captures_box47: box<{}> = @ptr_cast(captures_41 as box<{}>);
>   let captures_stack47: {} = @get_boxed<captures_box47>;
>   let captures_stack_81: { str } = @make_struct{ s };
>   let captures_box_81: box<{ str }> = @make_box(captures_stack_81);
>   let captures_162: box<erased> = @ptr_cast(captures_box_81 as box<erased>);
>   let fn_ptr_81: *fn = @make_fn_ptr<clos_81>;
>   let var69: { *fn, box<erased> } = @make_struct{ fn_ptr_81, captures_162 };
>   return var69;
> }
> 
> global fail16: { *fn, box<erased> } = @call_direct(fail_thunk15);
> 
> proc fail_thunk15(): { *fn, box<erased> }
> {
>   let captures_stack_21: {} = @make_struct{};
>   let captures_box_21: box<{}> = @make_box(captures_stack_21);
>   let captures_42: box<erased> = @ptr_cast(captures_box_21 as box<erased>);
>   let fn_ptr_21: *fn = @make_fn_ptr<clos_21>;
>   let fail_closure15: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_21, captures_42 };
>   return fail_closure15;
> }
> 
> proc clos_83(captures_167: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box51: box<{ [] }> = @ptr_cast(captures_167 as box<{ [] }>);
>   let captures_stack51: { [] } = @get_boxed<captures_box51>;
>   let err: [] = @get_struct_field<captures_stack51, 0>;
>   let fnptr30: *fn = @get_struct_field<toNext1, 0>;
>   let captures30: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct21: { [] } = @make_struct{ err };
>   let var75: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct21>;
>   let var76:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr30, captures30, var75);
>   return var76;
> }
> 
> proc clos_21(captures_43: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box50: box<{}> = @ptr_cast(captures_43 as box<{}>);
>   let captures_stack50: {} = @get_boxed<captures_box50>;
>   let captures_stack_83: { [] } = @make_struct{ err };
>   let captures_box_83: box<{ [] }> = @make_box(captures_stack_83);
>   let captures_166: box<erased> = @ptr_cast(captures_box_83 as box<erased>);
>   let fn_ptr_83: *fn = @make_fn_ptr<clos_83>;
>   let var74: { *fn, box<erased> } = @make_struct{ fn_ptr_83, captures_166 };
>   return var74;
> }
> 
> global fail17: { *fn, box<erased> } = @call_direct(fail_thunk16);
> 
> proc fail_thunk16(): { *fn, box<erased> }
> {
>   let captures_stack_22: {} = @make_struct{};
>   let captures_box_22: box<{}> = @make_box(captures_stack_22);
>   let captures_44: box<erased> = @ptr_cast(captures_box_22 as box<erased>);
>   let fn_ptr_22: *fn = @make_fn_ptr<clos_22>;
>   let fail_closure16: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_22, captures_44 };
>   return fail_closure16;
> }
> 
> proc clos_84(captures_169: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box53: box<{ [] }> = @ptr_cast(captures_169 as box<{ [] }>);
>   let captures_stack53: { [] } = @get_boxed<captures_box53>;
>   let err: [] = @get_struct_field<captures_stack53, 0>;
>   let fnptr31: *fn = @get_struct_field<toNext1, 0>;
>   let captures31: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct22: { [] } = @make_struct{ err };
>   let var78: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct22>;
>   let var79:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr31, captures31, var78);
>   return var79;
> }
> 
> proc clos_22(captures_45: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box52: box<{}> = @ptr_cast(captures_45 as box<{}>);
>   let captures_stack52: {} = @get_boxed<captures_box52>;
>   let captures_stack_84: { [] } = @make_struct{ err };
>   let captures_box_84: box<{ [] }> = @make_box(captures_stack_84);
>   let captures_168: box<erased> = @ptr_cast(captures_box_84 as box<erased>);
>   let fn_ptr_84: *fn = @make_fn_ptr<clos_84>;
>   let var77: { *fn, box<erased> } = @make_struct{ fn_ptr_84, captures_168 };
>   return var77;
> }
> 
> global fail18: { *fn, box<erased> } = @call_direct(fail_thunk17);
> 
> proc fail_thunk17(): { *fn, box<erased> }
> {
>   let captures_stack_23: {} = @make_struct{};
>   let captures_box_23: box<{}> = @make_box(captures_stack_23);
>   let captures_46: box<erased> = @ptr_cast(captures_box_23 as box<erased>);
>   let fn_ptr_23: *fn = @make_fn_ptr<clos_23>;
>   let fail_closure17: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_23, captures_46 };
>   return fail_closure17;
> }
> 
> proc clos_85(captures_171: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box55: box<{ [] }> = @ptr_cast(captures_171 as box<{ [] }>);
>   let captures_stack55: { [] } = @get_boxed<captures_box55>;
>   let err: [] = @get_struct_field<captures_stack55, 0>;
>   let fnptr32: *fn = @get_struct_field<toNext1, 0>;
>   let captures32: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct23: { [] } = @make_struct{ err };
>   let var81: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct23>;
>   let var82:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr32, captures32, var81);
>   return var82;
> }
> 
> proc clos_23(captures_47: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box54: box<{}> = @ptr_cast(captures_47 as box<{}>);
>   let captures_stack54: {} = @get_boxed<captures_box54>;
>   let captures_stack_85: { [] } = @make_struct{ err };
>   let captures_box_85: box<{ [] }> = @make_box(captures_stack_85);
>   let captures_170: box<erased> = @ptr_cast(captures_box_85 as box<erased>);
>   let fn_ptr_85: *fn = @make_fn_ptr<clos_85>;
>   let var80: { *fn, box<erased> } = @make_struct{ fn_ptr_85, captures_170 };
>   return var80;
> }
> 
> global fail19: { *fn, box<erased> } = @call_direct(fail_thunk18);
> 
> proc fail_thunk18(): { *fn, box<erased> }
> {
>   let captures_stack_24: {} = @make_struct{};
>   let captures_box_24: box<{}> = @make_box(captures_stack_24);
>   let captures_48: box<erased> = @ptr_cast(captures_box_24 as box<erased>);
>   let fn_ptr_24: *fn = @make_fn_ptr<clos_24>;
>   let fail_closure18: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_24, captures_48 };
>   return fail_closure18;
> }
> 
> proc clos_86(captures_173: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box57: box<{ [] }> = @ptr_cast(captures_173 as box<{ [] }>);
>   let captures_stack57: { [] } = @get_boxed<captures_box57>;
>   let err: [] = @get_struct_field<captures_stack57, 0>;
>   let fnptr33: *fn = @get_struct_field<toNext1, 0>;
>   let captures33: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct24: { [] } = @make_struct{ err };
>   let var84: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct24>;
>   let var85:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr33, captures33, var84);
>   return var85;
> }
> 
> proc clos_24(captures_49: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box56: box<{}> = @ptr_cast(captures_49 as box<{}>);
>   let captures_stack56: {} = @get_boxed<captures_box56>;
>   let captures_stack_86: { [] } = @make_struct{ err };
>   let captures_box_86: box<{ [] }> = @make_box(captures_stack_86);
>   let captures_172: box<erased> = @ptr_cast(captures_box_86 as box<erased>);
>   let fn_ptr_86: *fn = @make_fn_ptr<clos_86>;
>   let var83: { *fn, box<erased> } = @make_struct{ fn_ptr_86, captures_172 };
>   return var83;
> }
> 
> global fail20: { *fn, box<erased> } = @call_direct(fail_thunk19);
> 
> proc fail_thunk19(): { *fn, box<erased> }
> {
>   let captures_stack_25: {} = @make_struct{};
>   let captures_box_25: box<{}> = @make_box(captures_stack_25);
>   let captures_50: box<erased> = @ptr_cast(captures_box_25 as box<erased>);
>   let fn_ptr_25: *fn = @make_fn_ptr<clos_25>;
>   let fail_closure19: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_25, captures_50 };
>   return fail_closure19;
> }
> 
> proc clos_87(captures_175: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box59: box<{ [] }> = @ptr_cast(captures_175 as box<{ [] }>);
>   let captures_stack59: { [] } = @get_boxed<captures_box59>;
>   let err: [] = @get_struct_field<captures_stack59, 0>;
>   let fnptr34: *fn = @get_struct_field<toNext1, 0>;
>   let captures34: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct25: { [] } = @make_struct{ err };
>   let var87: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct25>;
>   let var88:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr34, captures34, var87);
>   return var88;
> }
> 
> proc clos_25(captures_51: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box58: box<{}> = @ptr_cast(captures_51 as box<{}>);
>   let captures_stack58: {} = @get_boxed<captures_box58>;
>   let captures_stack_87: { [] } = @make_struct{ err };
>   let captures_box_87: box<{ [] }> = @make_box(captures_stack_87);
>   let captures_174: box<erased> = @ptr_cast(captures_box_87 as box<erased>);
>   let fn_ptr_87: *fn = @make_fn_ptr<clos_87>;
>   let var86: { *fn, box<erased> } = @make_struct{ fn_ptr_87, captures_174 };
>   return var86;
> }
> 
> global await4: { *fn, box<erased> } = @call_direct(await_thunk3);
> 
> proc await_thunk3(): { *fn, box<erased> }
> {
>   let captures_stack_26: { { *fn, box<erased> } } = @make_struct{ fail20 };
>   let captures_box_26: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_26);
>   let captures_52: box<erased> = @ptr_cast(captures_box_26 as box<erased>);
>   let fn_ptr_26: *fn = @make_fn_ptr<clos_26>;
>   let await_closure3: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_26, captures_52 };
>   return await_closure3;
> }
> 
> proc clos_90(captures_181: box<erased>, result: [ `0 { [] }, `1 { str } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box63:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_181 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack63:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box63>;
>   let continue: { *fn, box<erased> } = @get_struct_field<captures_stack63, 0>;
>   let fail17: { *fn, box<erased> } = @get_struct_field<captures_stack63, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack63, 2>;
>   let discr3: int = @get_union_id<result>;
>   switch discr3 {
>   0 -> {
>     let payload7: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload7, 0>;
>     let fnptr37: *fn = @get_struct_field<fail16, 0>;
>     let captures37: box<erased> = @get_struct_field<fail16, 1>;
>     @call_indirect(fnptr37, captures37, e)
>   }
>   1 -> {
>     let payload6: { str } = @get_union_struct<result>;
>     let v: str = @get_struct_field<payload6, 0>;
>     let fnptr36: *fn = @get_struct_field<next, 0>;
>     let captures36: box<erased> = @get_struct_field<next, 1>;
>     @call_indirect(fnptr36, captures36, v)
>   }
>   } in join join3;
>   let inner: { *fn, box<erased> } = join3;
>   let fnptr38: *fn = @get_struct_field<inner, 0>;
>   let captures38: box<erased> = @get_struct_field<inner, 1>;
>   let var93:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr38, captures38, continue);
>   return var93;
> }
> 
> proc clos_89(captures_179: box<erased>, continue: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box62:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_179 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack62:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box62>;
>   let fail18: { *fn, box<erased> } = @get_struct_field<captures_stack62, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack62, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack62, 2>;
>   let fnptr35: *fn = @get_struct_field<fromResult, 0>;
>   let captures35: box<erased> = @get_struct_field<fromResult, 1>;
>   let captures_stack_90:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ continue, fail17, next };
>   let captures_box_90:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_90);
>   let captures_180: box<erased> = @ptr_cast(captures_box_90 as box<erased>);
>   let fn_ptr_90: *fn = @make_fn_ptr<clos_90>;
>   let var91: { *fn, box<erased> } = @make_struct{ fn_ptr_90, captures_180 };
>   let var92:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr35, captures35, var91);
>   return var92;
> }
> 
> proc clos_88(captures_177: box<erased>, next: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box61: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_177 as
>         box<{ { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack61: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box61>;
>   let fail19: { *fn, box<erased> } = @get_struct_field<captures_stack61, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack61, 1>;
>   let captures_stack_89:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail18, fromResult, next };
>   let captures_box_89:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_89);
>   let captures_178: box<erased> = @ptr_cast(captures_box_89 as box<erased>);
>   let fn_ptr_89: *fn = @make_fn_ptr<clos_89>;
>   let var90: { *fn, box<erased> } = @make_struct{ fn_ptr_89, captures_178 };
>   return var90;
> }
> 
> proc clos_26(captures_53: box<erased>, fromResult: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box60: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_53 as box<{ { *fn, box<erased> } }>);
>   let captures_stack60: { { *fn, box<erased> } } = @get_boxed<captures_box60>;
>   let fail20: { *fn, box<erased> } = @get_struct_field<captures_stack60, 0>;
>   let captures_stack_88: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail19, fromResult };
>   let captures_box_88: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_88);
>   let captures_176: box<erased> = @ptr_cast(captures_box_88 as box<erased>);
>   let fn_ptr_88: *fn = @make_fn_ptr<clos_88>;
>   let var89: { *fn, box<erased> } = @make_struct{ fn_ptr_88, captures_176 };
>   return var89;
> }
> 
> global inLine2: { *fn, box<erased> } = @call_direct(inLine_thunk1);
> 
> proc inLine_thunk1(): { *fn, box<erased> }
> {
>   let captures_stack_27: {} = @make_struct{};
>   let captures_box_27: box<{}> = @make_box(captures_stack_27);
>   let captures_54: box<erased> = @ptr_cast(captures_box_27 as box<erased>);
>   let fn_ptr_27: *fn = @make_fn_ptr<clos_27>;
>   let inLine_closure1: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_27, captures_54 };
>   return inLine_closure1;
> }
> 
> proc clos_91(captures_183: box<erased>, s1: str):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box65: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_183 as box<{ { *fn, box<erased> } }>);
>   let captures_stack65: { { *fn, box<erased> } } = @get_boxed<captures_box65>;
>   let toNext3: { *fn, box<erased> } = @get_struct_field<captures_stack65, 0>;
>   let fnptr39: *fn = @get_struct_field<toNext3, 0>;
>   let captures39: box<erased> = @get_struct_field<toNext3, 1>;
>   let struct27: { str } = @make_struct{ s1 };
>   let var96: [ `0 { [] }, `1 { str } ] = @make_union<1, struct27>;
>   let var97:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr39, captures39, var96);
>   return var97;
> }
> 
> proc clos_27(captures_55: box<erased>, toNext3: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box64: box<{}> = @ptr_cast(captures_55 as box<{}>);
>   let captures_stack64: {} = @get_boxed<captures_box64>;
>   let captures_stack_91: { { *fn, box<erased> } } = @make_struct{ toNext3 };
>   let captures_box_91: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_91);
>   let captures_182: box<erased> = @ptr_cast(captures_box_91 as box<erased>);
>   let fn_ptr_91: *fn = @make_fn_ptr<clos_91>;
>   let var94: { *fn, box<erased> } = @make_struct{ fn_ptr_91, captures_182 };
>   let struct26: { { *fn, box<erased> } } = @make_struct{ var94 };
>   let unboxed5:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<1, struct26>;
>   let var95:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed5);
>   return var95;
> }
> 
> global outLine3: { *fn, box<erased> } = @call_direct(outLine_thunk2);
> 
> proc outLine_thunk2(): { *fn, box<erased> }
> {
>   let captures_stack_28: {} = @make_struct{};
>   let captures_box_28: box<{}> = @make_box(captures_stack_28);
>   let captures_56: box<erased> = @ptr_cast(captures_box_28 as box<erased>);
>   let fn_ptr_28: *fn = @make_fn_ptr<clos_28>;
>   let outLine_closure2: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_28, captures_56 };
>   return outLine_closure2;
> }
> 
> proc clos_93(captures_187: box<erased>, x: {}):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box68: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_187 as box<{ { *fn, box<erased> } }>);
>   let captures_stack68: { { *fn, box<erased> } } = @get_boxed<captures_box68>;
>   let toNext2: { *fn, box<erased> } = @get_struct_field<captures_stack68, 0>;
>   let fnptr40: *fn = @get_struct_field<toNext2, 0>;
>   let captures40: box<erased> = @get_struct_field<toNext2, 1>;
>   let struct29: { {} } = @make_struct{ x };
>   let var101: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct29>;
>   let var102:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr40, captures40, var101);
>   return var102;
> }
> 
> proc clos_92(captures_185: box<erased>, toNext2: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box67: box<{ str }> = @ptr_cast(captures_185 as box<{ str }>);
>   let captures_stack67: { str } = @get_boxed<captures_box67>;
>   let s: str = @get_struct_field<captures_stack67, 0>;
>   let captures_stack_93: { { *fn, box<erased> } } = @make_struct{ toNext2 };
>   let captures_box_93: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_93);
>   let captures_186: box<erased> = @ptr_cast(captures_box_93 as box<erased>);
>   let fn_ptr_93: *fn = @make_fn_ptr<clos_93>;
>   let unboxed6: { *fn, box<erased> } = @make_struct{ fn_ptr_93, captures_186 };
>   let var99: box<%type_1 = { *fn, box<erased> }> = @make_box(unboxed6);
>   let struct28: { str, box<%type_1 = { *fn, box<erased> }> }
>     = @make_struct{ s, var99 };
>   let unboxed7:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<2, struct28>;
>   let var100:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed7);
>   return var100;
> }
> 
> proc clos_28(captures_57: box<erased>, s: str): { *fn, box<erased> }
> {
>   let captures_box66: box<{}> = @ptr_cast(captures_57 as box<{}>);
>   let captures_stack66: {} = @get_boxed<captures_box66>;
>   let captures_stack_92: { str } = @make_struct{ s };
>   let captures_box_92: box<{ str }> = @make_box(captures_stack_92);
>   let captures_184: box<erased> = @ptr_cast(captures_box_92 as box<erased>);
>   let fn_ptr_92: *fn = @make_fn_ptr<clos_92>;
>   let var98: { *fn, box<erased> } = @make_struct{ fn_ptr_92, captures_184 };
>   return var98;
> }
> 
> global outLine4: { *fn, box<erased> } = @call_direct(outLine_thunk3);
> 
> proc outLine_thunk3(): { *fn, box<erased> }
> {
>   let captures_stack_29: {} = @make_struct{};
>   let captures_box_29: box<{}> = @make_box(captures_stack_29);
>   let captures_58: box<erased> = @ptr_cast(captures_box_29 as box<erased>);
>   let fn_ptr_29: *fn = @make_fn_ptr<clos_29>;
>   let outLine_closure3: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_29, captures_58 };
>   return outLine_closure3;
> }
> 
> proc clos_95(captures_191: box<erased>, x: {}):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box71: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_191 as box<{ { *fn, box<erased> } }>);
>   let captures_stack71: { { *fn, box<erased> } } = @get_boxed<captures_box71>;
>   let toNext2: { *fn, box<erased> } = @get_struct_field<captures_stack71, 0>;
>   let fnptr41: *fn = @get_struct_field<toNext2, 0>;
>   let captures41: box<erased> = @get_struct_field<toNext2, 1>;
>   let struct31: { {} } = @make_struct{ x };
>   let var106: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct31>;
>   let var107:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr41, captures41, var106);
>   return var107;
> }
> 
> proc clos_94(captures_189: box<erased>, toNext2: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box70: box<{ str }> = @ptr_cast(captures_189 as box<{ str }>);
>   let captures_stack70: { str } = @get_boxed<captures_box70>;
>   let s: str = @get_struct_field<captures_stack70, 0>;
>   let captures_stack_95: { { *fn, box<erased> } } = @make_struct{ toNext2 };
>   let captures_box_95: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_95);
>   let captures_190: box<erased> = @ptr_cast(captures_box_95 as box<erased>);
>   let fn_ptr_95: *fn = @make_fn_ptr<clos_95>;
>   let unboxed8: { *fn, box<erased> } = @make_struct{ fn_ptr_95, captures_190 };
>   let var104: box<%type_1 = { *fn, box<erased> }> = @make_box(unboxed8);
>   let struct30: { str, box<%type_1 = { *fn, box<erased> }> }
>     = @make_struct{ s, var104 };
>   let unboxed9:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<2, struct30>;
>   let var105:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed9);
>   return var105;
> }
> 
> proc clos_29(captures_59: box<erased>, s: str): { *fn, box<erased> }
> {
>   let captures_box69: box<{}> = @ptr_cast(captures_59 as box<{}>);
>   let captures_stack69: {} = @get_boxed<captures_box69>;
>   let captures_stack_94: { str } = @make_struct{ s };
>   let captures_box_94: box<{ str }> = @make_box(captures_stack_94);
>   let captures_188: box<erased> = @ptr_cast(captures_box_94 as box<erased>);
>   let fn_ptr_94: *fn = @make_fn_ptr<clos_94>;
>   let var103: { *fn, box<erased> } = @make_struct{ fn_ptr_94, captures_188 };
>   return var103;
> }
> 
> global fail21: { *fn, box<erased> } = @call_direct(fail_thunk20);
> 
> proc fail_thunk20(): { *fn, box<erased> }
> {
>   let captures_stack_30: {} = @make_struct{};
>   let captures_box_30: box<{}> = @make_box(captures_stack_30);
>   let captures_60: box<erased> = @ptr_cast(captures_box_30 as box<erased>);
>   let fn_ptr_30: *fn = @make_fn_ptr<clos_30>;
>   let fail_closure20: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_30, captures_60 };
>   return fail_closure20;
> }
> 
> proc clos_96(captures_193: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box73: box<{ [] }> = @ptr_cast(captures_193 as box<{ [] }>);
>   let captures_stack73: { [] } = @get_boxed<captures_box73>;
>   let err: [] = @get_struct_field<captures_stack73, 0>;
>   let fnptr42: *fn = @get_struct_field<toNext1, 0>;
>   let captures42: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct32: { [] } = @make_struct{ err };
>   let var109: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct32>;
>   let var110:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr42, captures42, var109);
>   return var110;
> }
> 
> proc clos_30(captures_61: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box72: box<{}> = @ptr_cast(captures_61 as box<{}>);
>   let captures_stack72: {} = @get_boxed<captures_box72>;
>   let captures_stack_96: { [] } = @make_struct{ err };
>   let captures_box_96: box<{ [] }> = @make_box(captures_stack_96);
>   let captures_192: box<erased> = @ptr_cast(captures_box_96 as box<erased>);
>   let fn_ptr_96: *fn = @make_fn_ptr<clos_96>;
>   let var108: { *fn, box<erased> } = @make_struct{ fn_ptr_96, captures_192 };
>   return var108;
> }
> 
> global fail22: { *fn, box<erased> } = @call_direct(fail_thunk21);
> 
> proc fail_thunk21(): { *fn, box<erased> }
> {
>   let captures_stack_31: {} = @make_struct{};
>   let captures_box_31: box<{}> = @make_box(captures_stack_31);
>   let captures_62: box<erased> = @ptr_cast(captures_box_31 as box<erased>);
>   let fn_ptr_31: *fn = @make_fn_ptr<clos_31>;
>   let fail_closure21: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_31, captures_62 };
>   return fail_closure21;
> }
> 
> proc clos_97(captures_195: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box75: box<{ [] }> = @ptr_cast(captures_195 as box<{ [] }>);
>   let captures_stack75: { [] } = @get_boxed<captures_box75>;
>   let err: [] = @get_struct_field<captures_stack75, 0>;
>   let fnptr43: *fn = @get_struct_field<toNext1, 0>;
>   let captures43: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct33: { [] } = @make_struct{ err };
>   let var112: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct33>;
>   let var113:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr43, captures43, var112);
>   return var113;
> }
> 
> proc clos_31(captures_63: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box74: box<{}> = @ptr_cast(captures_63 as box<{}>);
>   let captures_stack74: {} = @get_boxed<captures_box74>;
>   let captures_stack_97: { [] } = @make_struct{ err };
>   let captures_box_97: box<{ [] }> = @make_box(captures_stack_97);
>   let captures_194: box<erased> = @ptr_cast(captures_box_97 as box<erased>);
>   let fn_ptr_97: *fn = @make_fn_ptr<clos_97>;
>   let var111: { *fn, box<erased> } = @make_struct{ fn_ptr_97, captures_194 };
>   return var111;
> }
> 
> global fail23: { *fn, box<erased> } = @call_direct(fail_thunk22);
> 
> proc fail_thunk22(): { *fn, box<erased> }
> {
>   let captures_stack_32: {} = @make_struct{};
>   let captures_box_32: box<{}> = @make_box(captures_stack_32);
>   let captures_64: box<erased> = @ptr_cast(captures_box_32 as box<erased>);
>   let fn_ptr_32: *fn = @make_fn_ptr<clos_32>;
>   let fail_closure22: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_32, captures_64 };
>   return fail_closure22;
> }
> 
> proc clos_98(captures_197: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box77: box<{ [] }> = @ptr_cast(captures_197 as box<{ [] }>);
>   let captures_stack77: { [] } = @get_boxed<captures_box77>;
>   let err: [] = @get_struct_field<captures_stack77, 0>;
>   let fnptr44: *fn = @get_struct_field<toNext1, 0>;
>   let captures44: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct34: { [] } = @make_struct{ err };
>   let var115: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct34>;
>   let var116:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr44, captures44, var115);
>   return var116;
> }
> 
> proc clos_32(captures_65: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box76: box<{}> = @ptr_cast(captures_65 as box<{}>);
>   let captures_stack76: {} = @get_boxed<captures_box76>;
>   let captures_stack_98: { [] } = @make_struct{ err };
>   let captures_box_98: box<{ [] }> = @make_box(captures_stack_98);
>   let captures_196: box<erased> = @ptr_cast(captures_box_98 as box<erased>);
>   let fn_ptr_98: *fn = @make_fn_ptr<clos_98>;
>   let var114: { *fn, box<erased> } = @make_struct{ fn_ptr_98, captures_196 };
>   return var114;
> }
> 
> global fail24: { *fn, box<erased> } = @call_direct(fail_thunk23);
> 
> proc fail_thunk23(): { *fn, box<erased> }
> {
>   let captures_stack_33: {} = @make_struct{};
>   let captures_box_33: box<{}> = @make_box(captures_stack_33);
>   let captures_66: box<erased> = @ptr_cast(captures_box_33 as box<erased>);
>   let fn_ptr_33: *fn = @make_fn_ptr<clos_33>;
>   let fail_closure23: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_33, captures_66 };
>   return fail_closure23;
> }
> 
> proc clos_99(captures_199: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box79: box<{ [] }> = @ptr_cast(captures_199 as box<{ [] }>);
>   let captures_stack79: { [] } = @get_boxed<captures_box79>;
>   let err: [] = @get_struct_field<captures_stack79, 0>;
>   let fnptr45: *fn = @get_struct_field<toNext1, 0>;
>   let captures45: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct35: { [] } = @make_struct{ err };
>   let var118: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct35>;
>   let var119:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr45, captures45, var118);
>   return var119;
> }
> 
> proc clos_33(captures_67: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box78: box<{}> = @ptr_cast(captures_67 as box<{}>);
>   let captures_stack78: {} = @get_boxed<captures_box78>;
>   let captures_stack_99: { [] } = @make_struct{ err };
>   let captures_box_99: box<{ [] }> = @make_box(captures_stack_99);
>   let captures_198: box<erased> = @ptr_cast(captures_box_99 as box<erased>);
>   let fn_ptr_99: *fn = @make_fn_ptr<clos_99>;
>   let var117: { *fn, box<erased> } = @make_struct{ fn_ptr_99, captures_198 };
>   return var117;
> }
> 
> global fail25: { *fn, box<erased> } = @call_direct(fail_thunk24);
> 
> proc fail_thunk24(): { *fn, box<erased> }
> {
>   let captures_stack_34: {} = @make_struct{};
>   let captures_box_34: box<{}> = @make_box(captures_stack_34);
>   let captures_68: box<erased> = @ptr_cast(captures_box_34 as box<erased>);
>   let fn_ptr_34: *fn = @make_fn_ptr<clos_34>;
>   let fail_closure24: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_34, captures_68 };
>   return fail_closure24;
> }
> 
> proc clos_100(captures_201: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box81: box<{ [] }> = @ptr_cast(captures_201 as box<{ [] }>);
>   let captures_stack81: { [] } = @get_boxed<captures_box81>;
>   let err: [] = @get_struct_field<captures_stack81, 0>;
>   let fnptr46: *fn = @get_struct_field<toNext1, 0>;
>   let captures46: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct36: { [] } = @make_struct{ err };
>   let var121: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct36>;
>   let var122:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr46, captures46, var121);
>   return var122;
> }
> 
> proc clos_34(captures_69: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box80: box<{}> = @ptr_cast(captures_69 as box<{}>);
>   let captures_stack80: {} = @get_boxed<captures_box80>;
>   let captures_stack_100: { [] } = @make_struct{ err };
>   let captures_box_100: box<{ [] }> = @make_box(captures_stack_100);
>   let captures_200: box<erased> = @ptr_cast(captures_box_100 as box<erased>);
>   let fn_ptr_100: *fn = @make_fn_ptr<clos_100>;
>   let var120: { *fn, box<erased> } = @make_struct{ fn_ptr_100, captures_200 };
>   return var120;
> }
> 
> global await5: { *fn, box<erased> } = @call_direct(await_thunk4);
> 
> proc await_thunk4(): { *fn, box<erased> }
> {
>   let captures_stack_35: { { *fn, box<erased> } } = @make_struct{ fail25 };
>   let captures_box_35: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_35);
>   let captures_70: box<erased> = @ptr_cast(captures_box_35 as box<erased>);
>   let fn_ptr_35: *fn = @make_fn_ptr<clos_35>;
>   let await_closure4: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_35, captures_70 };
>   return await_closure4;
> }
> 
> proc clos_103(captures_207: box<erased>, result: [ `0 { [] }, `1 { str } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box85:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_207 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack85:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box85>;
>   let continue: { *fn, box<erased> } = @get_struct_field<captures_stack85, 0>;
>   let fail22: { *fn, box<erased> } = @get_struct_field<captures_stack85, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack85, 2>;
>   let discr4: int = @get_union_id<result>;
>   switch discr4 {
>   0 -> {
>     let payload9: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload9, 0>;
>     let fnptr49: *fn = @get_struct_field<fail21, 0>;
>     let captures49: box<erased> = @get_struct_field<fail21, 1>;
>     @call_indirect(fnptr49, captures49, e)
>   }
>   1 -> {
>     let payload8: { str } = @get_union_struct<result>;
>     let v: str = @get_struct_field<payload8, 0>;
>     let fnptr48: *fn = @get_struct_field<next, 0>;
>     let captures48: box<erased> = @get_struct_field<next, 1>;
>     @call_indirect(fnptr48, captures48, v)
>   }
>   } in join join4;
>   let inner: { *fn, box<erased> } = join4;
>   let fnptr50: *fn = @get_struct_field<inner, 0>;
>   let captures50: box<erased> = @get_struct_field<inner, 1>;
>   let var127:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr50, captures50, continue);
>   return var127;
> }
> 
> proc clos_102(captures_205: box<erased>, continue: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box84:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_205 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack84:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box84>;
>   let fail23: { *fn, box<erased> } = @get_struct_field<captures_stack84, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack84, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack84, 2>;
>   let fnptr47: *fn = @get_struct_field<fromResult, 0>;
>   let captures47: box<erased> = @get_struct_field<fromResult, 1>;
>   let captures_stack_103:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ continue, fail22, next };
>   let captures_box_103:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_103);
>   let captures_206: box<erased> = @ptr_cast(captures_box_103 as box<erased>);
>   let fn_ptr_103: *fn = @make_fn_ptr<clos_103>;
>   let var125: { *fn, box<erased> } = @make_struct{ fn_ptr_103, captures_206 };
>   let var126:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr47, captures47, var125);
>   return var126;
> }
> 
> proc clos_101(captures_203: box<erased>, next: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box83: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_203 as
>         box<{ { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack83: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box83>;
>   let fail24: { *fn, box<erased> } = @get_struct_field<captures_stack83, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack83, 1>;
>   let captures_stack_102:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail23, fromResult, next };
>   let captures_box_102:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_102);
>   let captures_204: box<erased> = @ptr_cast(captures_box_102 as box<erased>);
>   let fn_ptr_102: *fn = @make_fn_ptr<clos_102>;
>   let var124: { *fn, box<erased> } = @make_struct{ fn_ptr_102, captures_204 };
>   return var124;
> }
> 
> proc clos_35(captures_71: box<erased>, fromResult: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box82: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_71 as box<{ { *fn, box<erased> } }>);
>   let captures_stack82: { { *fn, box<erased> } } = @get_boxed<captures_box82>;
>   let fail25: { *fn, box<erased> } = @get_struct_field<captures_stack82, 0>;
>   let captures_stack_101: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail24, fromResult };
>   let captures_box_101: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_101);
>   let captures_202: box<erased> = @ptr_cast(captures_box_101 as box<erased>);
>   let fn_ptr_101: *fn = @make_fn_ptr<clos_101>;
>   let var123: { *fn, box<erased> } = @make_struct{ fn_ptr_101, captures_202 };
>   return var123;
> }
> 
> global inLine3: { *fn, box<erased> } = @call_direct(inLine_thunk2);
> 
> proc inLine_thunk2(): { *fn, box<erased> }
> {
>   let captures_stack_36: {} = @make_struct{};
>   let captures_box_36: box<{}> = @make_box(captures_stack_36);
>   let captures_72: box<erased> = @ptr_cast(captures_box_36 as box<erased>);
>   let fn_ptr_36: *fn = @make_fn_ptr<clos_36>;
>   let inLine_closure2: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_36, captures_72 };
>   return inLine_closure2;
> }
> 
> proc clos_104(captures_209: box<erased>, s1: str):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box87: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_209 as box<{ { *fn, box<erased> } }>);
>   let captures_stack87: { { *fn, box<erased> } } = @get_boxed<captures_box87>;
>   let toNext3: { *fn, box<erased> } = @get_struct_field<captures_stack87, 0>;
>   let fnptr51: *fn = @get_struct_field<toNext3, 0>;
>   let captures51: box<erased> = @get_struct_field<toNext3, 1>;
>   let struct38: { str } = @make_struct{ s1 };
>   let var130: [ `0 { [] }, `1 { str } ] = @make_union<1, struct38>;
>   let var131:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr51, captures51, var130);
>   return var131;
> }
> 
> proc clos_36(captures_73: box<erased>, toNext3: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box86: box<{}> = @ptr_cast(captures_73 as box<{}>);
>   let captures_stack86: {} = @get_boxed<captures_box86>;
>   let captures_stack_104: { { *fn, box<erased> } } = @make_struct{ toNext3 };
>   let captures_box_104: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_104);
>   let captures_208: box<erased> = @ptr_cast(captures_box_104 as box<erased>);
>   let fn_ptr_104: *fn = @make_fn_ptr<clos_104>;
>   let var128: { *fn, box<erased> } = @make_struct{ fn_ptr_104, captures_208 };
>   let struct37: { { *fn, box<erased> } } = @make_struct{ var128 };
>   let unboxed10:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<1, struct37>;
>   let var129:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed10);
>   return var129;
> }
> 
> global outLine5: { *fn, box<erased> } = @call_direct(outLine_thunk4);
> 
> proc outLine_thunk4(): { *fn, box<erased> }
> {
>   let captures_stack_37: {} = @make_struct{};
>   let captures_box_37: box<{}> = @make_box(captures_stack_37);
>   let captures_74: box<erased> = @ptr_cast(captures_box_37 as box<erased>);
>   let fn_ptr_37: *fn = @make_fn_ptr<clos_37>;
>   let outLine_closure4: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_37, captures_74 };
>   return outLine_closure4;
> }
> 
> proc clos_106(captures_213: box<erased>, x: {}):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box90: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_213 as box<{ { *fn, box<erased> } }>);
>   let captures_stack90: { { *fn, box<erased> } } = @get_boxed<captures_box90>;
>   let toNext2: { *fn, box<erased> } = @get_struct_field<captures_stack90, 0>;
>   let fnptr52: *fn = @get_struct_field<toNext2, 0>;
>   let captures52: box<erased> = @get_struct_field<toNext2, 1>;
>   let struct40: { {} } = @make_struct{ x };
>   let var135: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct40>;
>   let var136:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr52, captures52, var135);
>   return var136;
> }
> 
> proc clos_105(captures_211: box<erased>, toNext2: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box89: box<{ str }> = @ptr_cast(captures_211 as box<{ str }>);
>   let captures_stack89: { str } = @get_boxed<captures_box89>;
>   let s: str = @get_struct_field<captures_stack89, 0>;
>   let captures_stack_106: { { *fn, box<erased> } } = @make_struct{ toNext2 };
>   let captures_box_106: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_106);
>   let captures_212: box<erased> = @ptr_cast(captures_box_106 as box<erased>);
>   let fn_ptr_106: *fn = @make_fn_ptr<clos_106>;
>   let unboxed11: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_106, captures_212 };
>   let var133: box<%type_1 = { *fn, box<erased> }> = @make_box(unboxed11);
>   let struct39: { str, box<%type_1 = { *fn, box<erased> }> }
>     = @make_struct{ s, var133 };
>   let unboxed12:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<2, struct39>;
>   let var134:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed12);
>   return var134;
> }
> 
> proc clos_37(captures_75: box<erased>, s: str): { *fn, box<erased> }
> {
>   let captures_box88: box<{}> = @ptr_cast(captures_75 as box<{}>);
>   let captures_stack88: {} = @get_boxed<captures_box88>;
>   let captures_stack_105: { str } = @make_struct{ s };
>   let captures_box_105: box<{ str }> = @make_box(captures_stack_105);
>   let captures_210: box<erased> = @ptr_cast(captures_box_105 as box<erased>);
>   let fn_ptr_105: *fn = @make_fn_ptr<clos_105>;
>   let var132: { *fn, box<erased> } = @make_struct{ fn_ptr_105, captures_210 };
>   return var132;
> }
> 
> global fail26: { *fn, box<erased> } = @call_direct(fail_thunk25);
> 
> proc fail_thunk25(): { *fn, box<erased> }
> {
>   let captures_stack_38: {} = @make_struct{};
>   let captures_box_38: box<{}> = @make_box(captures_stack_38);
>   let captures_76: box<erased> = @ptr_cast(captures_box_38 as box<erased>);
>   let fn_ptr_38: *fn = @make_fn_ptr<clos_38>;
>   let fail_closure25: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_38, captures_76 };
>   return fail_closure25;
> }
> 
> proc clos_107(captures_215: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box92: box<{ [] }> = @ptr_cast(captures_215 as box<{ [] }>);
>   let captures_stack92: { [] } = @get_boxed<captures_box92>;
>   let err: [] = @get_struct_field<captures_stack92, 0>;
>   let fnptr53: *fn = @get_struct_field<toNext1, 0>;
>   let captures53: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct41: { [] } = @make_struct{ err };
>   let var138: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct41>;
>   let var139:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr53, captures53, var138);
>   return var139;
> }
> 
> proc clos_38(captures_77: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box91: box<{}> = @ptr_cast(captures_77 as box<{}>);
>   let captures_stack91: {} = @get_boxed<captures_box91>;
>   let captures_stack_107: { [] } = @make_struct{ err };
>   let captures_box_107: box<{ [] }> = @make_box(captures_stack_107);
>   let captures_214: box<erased> = @ptr_cast(captures_box_107 as box<erased>);
>   let fn_ptr_107: *fn = @make_fn_ptr<clos_107>;
>   let var137: { *fn, box<erased> } = @make_struct{ fn_ptr_107, captures_214 };
>   return var137;
> }
> 
> global fail27: { *fn, box<erased> } = @call_direct(fail_thunk26);
> 
> proc fail_thunk26(): { *fn, box<erased> }
> {
>   let captures_stack_39: {} = @make_struct{};
>   let captures_box_39: box<{}> = @make_box(captures_stack_39);
>   let captures_78: box<erased> = @ptr_cast(captures_box_39 as box<erased>);
>   let fn_ptr_39: *fn = @make_fn_ptr<clos_39>;
>   let fail_closure26: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_39, captures_78 };
>   return fail_closure26;
> }
> 
> proc clos_108(captures_217: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box94: box<{ [] }> = @ptr_cast(captures_217 as box<{ [] }>);
>   let captures_stack94: { [] } = @get_boxed<captures_box94>;
>   let err: [] = @get_struct_field<captures_stack94, 0>;
>   let fnptr54: *fn = @get_struct_field<toNext1, 0>;
>   let captures54: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct42: { [] } = @make_struct{ err };
>   let var141: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct42>;
>   let var142:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr54, captures54, var141);
>   return var142;
> }
> 
> proc clos_39(captures_79: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box93: box<{}> = @ptr_cast(captures_79 as box<{}>);
>   let captures_stack93: {} = @get_boxed<captures_box93>;
>   let captures_stack_108: { [] } = @make_struct{ err };
>   let captures_box_108: box<{ [] }> = @make_box(captures_stack_108);
>   let captures_216: box<erased> = @ptr_cast(captures_box_108 as box<erased>);
>   let fn_ptr_108: *fn = @make_fn_ptr<clos_108>;
>   let var140: { *fn, box<erased> } = @make_struct{ fn_ptr_108, captures_216 };
>   return var140;
> }
> 
> global fail28: { *fn, box<erased> } = @call_direct(fail_thunk27);
> 
> proc fail_thunk27(): { *fn, box<erased> }
> {
>   let captures_stack_40: {} = @make_struct{};
>   let captures_box_40: box<{}> = @make_box(captures_stack_40);
>   let captures_80: box<erased> = @ptr_cast(captures_box_40 as box<erased>);
>   let fn_ptr_40: *fn = @make_fn_ptr<clos_40>;
>   let fail_closure27: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_40, captures_80 };
>   return fail_closure27;
> }
> 
> proc clos_109(captures_219: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box96: box<{ [] }> = @ptr_cast(captures_219 as box<{ [] }>);
>   let captures_stack96: { [] } = @get_boxed<captures_box96>;
>   let err: [] = @get_struct_field<captures_stack96, 0>;
>   let fnptr55: *fn = @get_struct_field<toNext1, 0>;
>   let captures55: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct43: { [] } = @make_struct{ err };
>   let var144: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct43>;
>   let var145:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr55, captures55, var144);
>   return var145;
> }
> 
> proc clos_40(captures_81: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box95: box<{}> = @ptr_cast(captures_81 as box<{}>);
>   let captures_stack95: {} = @get_boxed<captures_box95>;
>   let captures_stack_109: { [] } = @make_struct{ err };
>   let captures_box_109: box<{ [] }> = @make_box(captures_stack_109);
>   let captures_218: box<erased> = @ptr_cast(captures_box_109 as box<erased>);
>   let fn_ptr_109: *fn = @make_fn_ptr<clos_109>;
>   let var143: { *fn, box<erased> } = @make_struct{ fn_ptr_109, captures_218 };
>   return var143;
> }
> 
> global fail29: { *fn, box<erased> } = @call_direct(fail_thunk28);
> 
> proc fail_thunk28(): { *fn, box<erased> }
> {
>   let captures_stack_41: {} = @make_struct{};
>   let captures_box_41: box<{}> = @make_box(captures_stack_41);
>   let captures_82: box<erased> = @ptr_cast(captures_box_41 as box<erased>);
>   let fn_ptr_41: *fn = @make_fn_ptr<clos_41>;
>   let fail_closure28: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_41, captures_82 };
>   return fail_closure28;
> }
> 
> proc clos_110(captures_221: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box98: box<{ [] }> = @ptr_cast(captures_221 as box<{ [] }>);
>   let captures_stack98: { [] } = @get_boxed<captures_box98>;
>   let err: [] = @get_struct_field<captures_stack98, 0>;
>   let fnptr56: *fn = @get_struct_field<toNext1, 0>;
>   let captures56: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct44: { [] } = @make_struct{ err };
>   let var147: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct44>;
>   let var148:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr56, captures56, var147);
>   return var148;
> }
> 
> proc clos_41(captures_83: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box97: box<{}> = @ptr_cast(captures_83 as box<{}>);
>   let captures_stack97: {} = @get_boxed<captures_box97>;
>   let captures_stack_110: { [] } = @make_struct{ err };
>   let captures_box_110: box<{ [] }> = @make_box(captures_stack_110);
>   let captures_220: box<erased> = @ptr_cast(captures_box_110 as box<erased>);
>   let fn_ptr_110: *fn = @make_fn_ptr<clos_110>;
>   let var146: { *fn, box<erased> } = @make_struct{ fn_ptr_110, captures_220 };
>   return var146;
> }
> 
> global fail30: { *fn, box<erased> } = @call_direct(fail_thunk29);
> 
> proc fail_thunk29(): { *fn, box<erased> }
> {
>   let captures_stack_42: {} = @make_struct{};
>   let captures_box_42: box<{}> = @make_box(captures_stack_42);
>   let captures_84: box<erased> = @ptr_cast(captures_box_42 as box<erased>);
>   let fn_ptr_42: *fn = @make_fn_ptr<clos_42>;
>   let fail_closure29: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_42, captures_84 };
>   return fail_closure29;
> }
> 
> proc clos_111(captures_223: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box100: box<{ [] }> = @ptr_cast(captures_223 as box<{ [] }>);
>   let captures_stack100: { [] } = @get_boxed<captures_box100>;
>   let err: [] = @get_struct_field<captures_stack100, 0>;
>   let fnptr57: *fn = @get_struct_field<toNext1, 0>;
>   let captures57: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct45: { [] } = @make_struct{ err };
>   let var150: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct45>;
>   let var151:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr57, captures57, var150);
>   return var151;
> }
> 
> proc clos_42(captures_85: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box99: box<{}> = @ptr_cast(captures_85 as box<{}>);
>   let captures_stack99: {} = @get_boxed<captures_box99>;
>   let captures_stack_111: { [] } = @make_struct{ err };
>   let captures_box_111: box<{ [] }> = @make_box(captures_stack_111);
>   let captures_222: box<erased> = @ptr_cast(captures_box_111 as box<erased>);
>   let fn_ptr_111: *fn = @make_fn_ptr<clos_111>;
>   let var149: { *fn, box<erased> } = @make_struct{ fn_ptr_111, captures_222 };
>   return var149;
> }
> 
> global await6: { *fn, box<erased> } = @call_direct(await_thunk5);
> 
> proc await_thunk5(): { *fn, box<erased> }
> {
>   let captures_stack_43: { { *fn, box<erased> } } = @make_struct{ fail30 };
>   let captures_box_43: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_43);
>   let captures_86: box<erased> = @ptr_cast(captures_box_43 as box<erased>);
>   let fn_ptr_43: *fn = @make_fn_ptr<clos_43>;
>   let await_closure5: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_43, captures_86 };
>   return await_closure5;
> }
> 
> proc clos_114(captures_229: box<erased>, result: [ `0 { [] }, `1 { {} } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box104:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_229 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack104:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box104>;
>   let continue: { *fn, box<erased> } = @get_struct_field<captures_stack104, 0>;
>   let fail27: { *fn, box<erased> } = @get_struct_field<captures_stack104, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack104, 2>;
>   let discr5: int = @get_union_id<result>;
>   switch discr5 {
>   0 -> {
>     let payload11: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload11, 0>;
>     let fnptr60: *fn = @get_struct_field<fail26, 0>;
>     let captures60: box<erased> = @get_struct_field<fail26, 1>;
>     @call_indirect(fnptr60, captures60, e)
>   }
>   1 -> {
>     let payload10: { {} } = @get_union_struct<result>;
>     let v: {} = @get_struct_field<payload10, 0>;
>     let fnptr59: *fn = @get_struct_field<next, 0>;
>     let captures59: box<erased> = @get_struct_field<next, 1>;
>     @call_indirect(fnptr59, captures59, v)
>   }
>   } in join join5;
>   let inner: { *fn, box<erased> } = join5;
>   let fnptr61: *fn = @get_struct_field<inner, 0>;
>   let captures61: box<erased> = @get_struct_field<inner, 1>;
>   let var156:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr61, captures61, continue);
>   return var156;
> }
> 
> proc clos_113(captures_227: box<erased>, continue: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box103:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_227 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack103:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box103>;
>   let fail28: { *fn, box<erased> } = @get_struct_field<captures_stack103, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack103, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack103, 2>;
>   let fnptr58: *fn = @get_struct_field<fromResult, 0>;
>   let captures58: box<erased> = @get_struct_field<fromResult, 1>;
>   let captures_stack_114:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ continue, fail27, next };
>   let captures_box_114:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_114);
>   let captures_228: box<erased> = @ptr_cast(captures_box_114 as box<erased>);
>   let fn_ptr_114: *fn = @make_fn_ptr<clos_114>;
>   let var154: { *fn, box<erased> } = @make_struct{ fn_ptr_114, captures_228 };
>   let var155:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr58, captures58, var154);
>   return var155;
> }
> 
> proc clos_112(captures_225: box<erased>, next: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box102: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_225 as
>         box<{ { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack102: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box102>;
>   let fail29: { *fn, box<erased> } = @get_struct_field<captures_stack102, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack102, 1>;
>   let captures_stack_113:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail28, fromResult, next };
>   let captures_box_113:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_113);
>   let captures_226: box<erased> = @ptr_cast(captures_box_113 as box<erased>);
>   let fn_ptr_113: *fn = @make_fn_ptr<clos_113>;
>   let var153: { *fn, box<erased> } = @make_struct{ fn_ptr_113, captures_226 };
>   return var153;
> }
> 
> proc clos_43(captures_87: box<erased>, fromResult: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box101: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_87 as box<{ { *fn, box<erased> } }>);
>   let captures_stack101: { { *fn, box<erased> } }
>     = @get_boxed<captures_box101>;
>   let fail30: { *fn, box<erased> } = @get_struct_field<captures_stack101, 0>;
>   let captures_stack_112: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail29, fromResult };
>   let captures_box_112: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_112);
>   let captures_224: box<erased> = @ptr_cast(captures_box_112 as box<erased>);
>   let fn_ptr_112: *fn = @make_fn_ptr<clos_112>;
>   let var152: { *fn, box<erased> } = @make_struct{ fn_ptr_112, captures_224 };
>   return var152;
> }
> 
> global inLine4: { *fn, box<erased> } = @call_direct(inLine_thunk3);
> 
> proc inLine_thunk3(): { *fn, box<erased> }
> {
>   let captures_stack_44: {} = @make_struct{};
>   let captures_box_44: box<{}> = @make_box(captures_stack_44);
>   let captures_88: box<erased> = @ptr_cast(captures_box_44 as box<erased>);
>   let fn_ptr_44: *fn = @make_fn_ptr<clos_44>;
>   let inLine_closure3: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_44, captures_88 };
>   return inLine_closure3;
> }
> 
> proc clos_115(captures_231: box<erased>, s1: str):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box106: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_231 as box<{ { *fn, box<erased> } }>);
>   let captures_stack106: { { *fn, box<erased> } }
>     = @get_boxed<captures_box106>;
>   let toNext3: { *fn, box<erased> } = @get_struct_field<captures_stack106, 0>;
>   let fnptr62: *fn = @get_struct_field<toNext3, 0>;
>   let captures62: box<erased> = @get_struct_field<toNext3, 1>;
>   let struct47: { str } = @make_struct{ s1 };
>   let var159: [ `0 { [] }, `1 { str } ] = @make_union<1, struct47>;
>   let var160:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr62, captures62, var159);
>   return var160;
> }
> 
> proc clos_44(captures_89: box<erased>, toNext3: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box105: box<{}> = @ptr_cast(captures_89 as box<{}>);
>   let captures_stack105: {} = @get_boxed<captures_box105>;
>   let captures_stack_115: { { *fn, box<erased> } } = @make_struct{ toNext3 };
>   let captures_box_115: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_115);
>   let captures_230: box<erased> = @ptr_cast(captures_box_115 as box<erased>);
>   let fn_ptr_115: *fn = @make_fn_ptr<clos_115>;
>   let var157: { *fn, box<erased> } = @make_struct{ fn_ptr_115, captures_230 };
>   let struct46: { { *fn, box<erased> } } = @make_struct{ var157 };
>   let unboxed13:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<1, struct46>;
>   let var158:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed13);
>   return var158;
> }
> 
> global outLine6: { *fn, box<erased> } = @call_direct(outLine_thunk5);
> 
> proc outLine_thunk5(): { *fn, box<erased> }
> {
>   let captures_stack_45: {} = @make_struct{};
>   let captures_box_45: box<{}> = @make_box(captures_stack_45);
>   let captures_90: box<erased> = @ptr_cast(captures_box_45 as box<erased>);
>   let fn_ptr_45: *fn = @make_fn_ptr<clos_45>;
>   let outLine_closure5: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_45, captures_90 };
>   return outLine_closure5;
> }
> 
> proc clos_117(captures_235: box<erased>, x: {}):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box109: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_235 as box<{ { *fn, box<erased> } }>);
>   let captures_stack109: { { *fn, box<erased> } }
>     = @get_boxed<captures_box109>;
>   let toNext2: { *fn, box<erased> } = @get_struct_field<captures_stack109, 0>;
>   let fnptr63: *fn = @get_struct_field<toNext2, 0>;
>   let captures63: box<erased> = @get_struct_field<toNext2, 1>;
>   let struct49: { {} } = @make_struct{ x };
>   let var164: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct49>;
>   let var165:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr63, captures63, var164);
>   return var165;
> }
> 
> proc clos_116(captures_233: box<erased>, toNext2: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box108: box<{ str }> = @ptr_cast(captures_233 as box<{ str }>);
>   let captures_stack108: { str } = @get_boxed<captures_box108>;
>   let s: str = @get_struct_field<captures_stack108, 0>;
>   let captures_stack_117: { { *fn, box<erased> } } = @make_struct{ toNext2 };
>   let captures_box_117: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_117);
>   let captures_234: box<erased> = @ptr_cast(captures_box_117 as box<erased>);
>   let fn_ptr_117: *fn = @make_fn_ptr<clos_117>;
>   let unboxed14: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_117, captures_234 };
>   let var162: box<%type_1 = { *fn, box<erased> }> = @make_box(unboxed14);
>   let struct48: { str, box<%type_1 = { *fn, box<erased> }> }
>     = @make_struct{ s, var162 };
>   let unboxed15:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<2, struct48>;
>   let var163:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed15);
>   return var163;
> }
> 
> proc clos_45(captures_91: box<erased>, s: str): { *fn, box<erased> }
> {
>   let captures_box107: box<{}> = @ptr_cast(captures_91 as box<{}>);
>   let captures_stack107: {} = @get_boxed<captures_box107>;
>   let captures_stack_116: { str } = @make_struct{ s };
>   let captures_box_116: box<{ str }> = @make_box(captures_stack_116);
>   let captures_232: box<erased> = @ptr_cast(captures_box_116 as box<erased>);
>   let fn_ptr_116: *fn = @make_fn_ptr<clos_116>;
>   let var161: { *fn, box<erased> } = @make_struct{ fn_ptr_116, captures_232 };
>   return var161;
> }
> 
> global fail31: { *fn, box<erased> } = @call_direct(fail_thunk30);
> 
> proc fail_thunk30(): { *fn, box<erased> }
> {
>   let captures_stack_46: {} = @make_struct{};
>   let captures_box_46: box<{}> = @make_box(captures_stack_46);
>   let captures_92: box<erased> = @ptr_cast(captures_box_46 as box<erased>);
>   let fn_ptr_46: *fn = @make_fn_ptr<clos_46>;
>   let fail_closure30: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_46, captures_92 };
>   return fail_closure30;
> }
> 
> proc clos_118(captures_237: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box111: box<{ [] }> = @ptr_cast(captures_237 as box<{ [] }>);
>   let captures_stack111: { [] } = @get_boxed<captures_box111>;
>   let err: [] = @get_struct_field<captures_stack111, 0>;
>   let fnptr64: *fn = @get_struct_field<toNext1, 0>;
>   let captures64: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct50: { [] } = @make_struct{ err };
>   let var167: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct50>;
>   let var168:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr64, captures64, var167);
>   return var168;
> }
> 
> proc clos_46(captures_93: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box110: box<{}> = @ptr_cast(captures_93 as box<{}>);
>   let captures_stack110: {} = @get_boxed<captures_box110>;
>   let captures_stack_118: { [] } = @make_struct{ err };
>   let captures_box_118: box<{ [] }> = @make_box(captures_stack_118);
>   let captures_236: box<erased> = @ptr_cast(captures_box_118 as box<erased>);
>   let fn_ptr_118: *fn = @make_fn_ptr<clos_118>;
>   let var166: { *fn, box<erased> } = @make_struct{ fn_ptr_118, captures_236 };
>   return var166;
> }
> 
> global fail32: { *fn, box<erased> } = @call_direct(fail_thunk31);
> 
> proc fail_thunk31(): { *fn, box<erased> }
> {
>   let captures_stack_47: {} = @make_struct{};
>   let captures_box_47: box<{}> = @make_box(captures_stack_47);
>   let captures_94: box<erased> = @ptr_cast(captures_box_47 as box<erased>);
>   let fn_ptr_47: *fn = @make_fn_ptr<clos_47>;
>   let fail_closure31: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_47, captures_94 };
>   return fail_closure31;
> }
> 
> proc clos_119(captures_239: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box113: box<{ [] }> = @ptr_cast(captures_239 as box<{ [] }>);
>   let captures_stack113: { [] } = @get_boxed<captures_box113>;
>   let err: [] = @get_struct_field<captures_stack113, 0>;
>   let fnptr65: *fn = @get_struct_field<toNext1, 0>;
>   let captures65: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct51: { [] } = @make_struct{ err };
>   let var170: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct51>;
>   let var171:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr65, captures65, var170);
>   return var171;
> }
> 
> proc clos_47(captures_95: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box112: box<{}> = @ptr_cast(captures_95 as box<{}>);
>   let captures_stack112: {} = @get_boxed<captures_box112>;
>   let captures_stack_119: { [] } = @make_struct{ err };
>   let captures_box_119: box<{ [] }> = @make_box(captures_stack_119);
>   let captures_238: box<erased> = @ptr_cast(captures_box_119 as box<erased>);
>   let fn_ptr_119: *fn = @make_fn_ptr<clos_119>;
>   let var169: { *fn, box<erased> } = @make_struct{ fn_ptr_119, captures_238 };
>   return var169;
> }
> 
> global fail33: { *fn, box<erased> } = @call_direct(fail_thunk32);
> 
> proc fail_thunk32(): { *fn, box<erased> }
> {
>   let captures_stack_48: {} = @make_struct{};
>   let captures_box_48: box<{}> = @make_box(captures_stack_48);
>   let captures_96: box<erased> = @ptr_cast(captures_box_48 as box<erased>);
>   let fn_ptr_48: *fn = @make_fn_ptr<clos_48>;
>   let fail_closure32: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_48, captures_96 };
>   return fail_closure32;
> }
> 
> proc clos_120(captures_241: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box115: box<{ [] }> = @ptr_cast(captures_241 as box<{ [] }>);
>   let captures_stack115: { [] } = @get_boxed<captures_box115>;
>   let err: [] = @get_struct_field<captures_stack115, 0>;
>   let fnptr66: *fn = @get_struct_field<toNext1, 0>;
>   let captures66: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct52: { [] } = @make_struct{ err };
>   let var173: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct52>;
>   let var174:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr66, captures66, var173);
>   return var174;
> }
> 
> proc clos_48(captures_97: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box114: box<{}> = @ptr_cast(captures_97 as box<{}>);
>   let captures_stack114: {} = @get_boxed<captures_box114>;
>   let captures_stack_120: { [] } = @make_struct{ err };
>   let captures_box_120: box<{ [] }> = @make_box(captures_stack_120);
>   let captures_240: box<erased> = @ptr_cast(captures_box_120 as box<erased>);
>   let fn_ptr_120: *fn = @make_fn_ptr<clos_120>;
>   let var172: { *fn, box<erased> } = @make_struct{ fn_ptr_120, captures_240 };
>   return var172;
> }
> 
> global fail34: { *fn, box<erased> } = @call_direct(fail_thunk33);
> 
> proc fail_thunk33(): { *fn, box<erased> }
> {
>   let captures_stack_49: {} = @make_struct{};
>   let captures_box_49: box<{}> = @make_box(captures_stack_49);
>   let captures_98: box<erased> = @ptr_cast(captures_box_49 as box<erased>);
>   let fn_ptr_49: *fn = @make_fn_ptr<clos_49>;
>   let fail_closure33: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_49, captures_98 };
>   return fail_closure33;
> }
> 
> proc clos_121(captures_243: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box117: box<{ [] }> = @ptr_cast(captures_243 as box<{ [] }>);
>   let captures_stack117: { [] } = @get_boxed<captures_box117>;
>   let err: [] = @get_struct_field<captures_stack117, 0>;
>   let fnptr67: *fn = @get_struct_field<toNext1, 0>;
>   let captures67: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct53: { [] } = @make_struct{ err };
>   let var176: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct53>;
>   let var177:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr67, captures67, var176);
>   return var177;
> }
> 
> proc clos_49(captures_99: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box116: box<{}> = @ptr_cast(captures_99 as box<{}>);
>   let captures_stack116: {} = @get_boxed<captures_box116>;
>   let captures_stack_121: { [] } = @make_struct{ err };
>   let captures_box_121: box<{ [] }> = @make_box(captures_stack_121);
>   let captures_242: box<erased> = @ptr_cast(captures_box_121 as box<erased>);
>   let fn_ptr_121: *fn = @make_fn_ptr<clos_121>;
>   let var175: { *fn, box<erased> } = @make_struct{ fn_ptr_121, captures_242 };
>   return var175;
> }
> 
> global fail35: { *fn, box<erased> } = @call_direct(fail_thunk34);
> 
> proc fail_thunk34(): { *fn, box<erased> }
> {
>   let captures_stack_50: {} = @make_struct{};
>   let captures_box_50: box<{}> = @make_box(captures_stack_50);
>   let captures_100: box<erased> = @ptr_cast(captures_box_50 as box<erased>);
>   let fn_ptr_50: *fn = @make_fn_ptr<clos_50>;
>   let fail_closure34: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_50, captures_100 };
>   return fail_closure34;
> }
> 
> proc clos_122(captures_245: box<erased>, toNext1: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box119: box<{ [] }> = @ptr_cast(captures_245 as box<{ [] }>);
>   let captures_stack119: { [] } = @get_boxed<captures_box119>;
>   let err: [] = @get_struct_field<captures_stack119, 0>;
>   let fnptr68: *fn = @get_struct_field<toNext1, 0>;
>   let captures68: box<erased> = @get_struct_field<toNext1, 1>;
>   let struct54: { [] } = @make_struct{ err };
>   let var179: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct54>;
>   let var180:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr68, captures68, var179);
>   return var180;
> }
> 
> proc clos_50(captures_101: box<erased>, err: []): { *fn, box<erased> }
> {
>   let captures_box118: box<{}> = @ptr_cast(captures_101 as box<{}>);
>   let captures_stack118: {} = @get_boxed<captures_box118>;
>   let captures_stack_122: { [] } = @make_struct{ err };
>   let captures_box_122: box<{ [] }> = @make_box(captures_stack_122);
>   let captures_244: box<erased> = @ptr_cast(captures_box_122 as box<erased>);
>   let fn_ptr_122: *fn = @make_fn_ptr<clos_122>;
>   let var178: { *fn, box<erased> } = @make_struct{ fn_ptr_122, captures_244 };
>   return var178;
> }
> 
> global await7: { *fn, box<erased> } = @call_direct(await_thunk6);
> 
> proc await_thunk6(): { *fn, box<erased> }
> {
>   let captures_stack_51: { { *fn, box<erased> } } = @make_struct{ fail35 };
>   let captures_box_51: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_51);
>   let captures_102: box<erased> = @ptr_cast(captures_box_51 as box<erased>);
>   let fn_ptr_51: *fn = @make_fn_ptr<clos_51>;
>   let await_closure6: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_51, captures_102 };
>   return await_closure6;
> }
> 
> proc clos_125(captures_251: box<erased>, result: [ `0 { [] }, `1 { str } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box123:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_251 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack123:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box123>;
>   let continue: { *fn, box<erased> } = @get_struct_field<captures_stack123, 0>;
>   let fail32: { *fn, box<erased> } = @get_struct_field<captures_stack123, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack123, 2>;
>   let discr6: int = @get_union_id<result>;
>   switch discr6 {
>   0 -> {
>     let payload13: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload13, 0>;
>     let fnptr71: *fn = @get_struct_field<fail31, 0>;
>     let captures71: box<erased> = @get_struct_field<fail31, 1>;
>     @call_indirect(fnptr71, captures71, e)
>   }
>   1 -> {
>     let payload12: { str } = @get_union_struct<result>;
>     let v: str = @get_struct_field<payload12, 0>;
>     let fnptr70: *fn = @get_struct_field<next, 0>;
>     let captures70: box<erased> = @get_struct_field<next, 1>;
>     @call_indirect(fnptr70, captures70, v)
>   }
>   } in join join6;
>   let inner: { *fn, box<erased> } = join6;
>   let fnptr72: *fn = @get_struct_field<inner, 0>;
>   let captures72: box<erased> = @get_struct_field<inner, 1>;
>   let var185:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr72, captures72, continue);
>   return var185;
> }
> 
> proc clos_124(captures_249: box<erased>, continue: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box122:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_249 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack122:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box122>;
>   let fail33: { *fn, box<erased> } = @get_struct_field<captures_stack122, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack122, 1>;
>   let next: { *fn, box<erased> } = @get_struct_field<captures_stack122, 2>;
>   let fnptr69: *fn = @get_struct_field<fromResult, 0>;
>   let captures69: box<erased> = @get_struct_field<fromResult, 1>;
>   let captures_stack_125:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ continue, fail32, next };
>   let captures_box_125:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_125);
>   let captures_250: box<erased> = @ptr_cast(captures_box_125 as box<erased>);
>   let fn_ptr_125: *fn = @make_fn_ptr<clos_125>;
>   let var183: { *fn, box<erased> } = @make_struct{ fn_ptr_125, captures_250 };
>   let var184:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr69, captures69, var183);
>   return var184;
> }
> 
> proc clos_123(captures_247: box<erased>, next: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box121: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_247 as
>         box<{ { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack121: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box121>;
>   let fail34: { *fn, box<erased> } = @get_struct_field<captures_stack121, 0>;
>   let fromResult: { *fn, box<erased> }
>     = @get_struct_field<captures_stack121, 1>;
>   let captures_stack_124:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail33, fromResult, next };
>   let captures_box_124:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_124);
>   let captures_248: box<erased> = @ptr_cast(captures_box_124 as box<erased>);
>   let fn_ptr_124: *fn = @make_fn_ptr<clos_124>;
>   let var182: { *fn, box<erased> } = @make_struct{ fn_ptr_124, captures_248 };
>   return var182;
> }
> 
> proc clos_51(captures_103: box<erased>, fromResult: { *fn, box<erased> }):
>   { *fn, box<erased> }
> {
>   let captures_box120: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_103 as box<{ { *fn, box<erased> } }>);
>   let captures_stack120: { { *fn, box<erased> } }
>     = @get_boxed<captures_box120>;
>   let fail35: { *fn, box<erased> } = @get_struct_field<captures_stack120, 0>;
>   let captures_stack_123: { { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ fail34, fromResult };
>   let captures_box_123: box<{ { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_123);
>   let captures_246: box<erased> = @ptr_cast(captures_box_123 as box<erased>);
>   let fn_ptr_123: *fn = @make_fn_ptr<clos_123>;
>   let var181: { *fn, box<erased> } = @make_struct{ fn_ptr_123, captures_246 };
>   return var181;
> }
> 
> global inLine5: { *fn, box<erased> } = @call_direct(inLine_thunk4);
> 
> proc inLine_thunk4(): { *fn, box<erased> }
> {
>   let captures_stack_52: {} = @make_struct{};
>   let captures_box_52: box<{}> = @make_box(captures_stack_52);
>   let captures_104: box<erased> = @ptr_cast(captures_box_52 as box<erased>);
>   let fn_ptr_52: *fn = @make_fn_ptr<clos_52>;
>   let inLine_closure4: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_52, captures_104 };
>   return inLine_closure4;
> }
> 
> proc clos_126(captures_253: box<erased>, s1: str):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box125: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_253 as box<{ { *fn, box<erased> } }>);
>   let captures_stack125: { { *fn, box<erased> } }
>     = @get_boxed<captures_box125>;
>   let toNext3: { *fn, box<erased> } = @get_struct_field<captures_stack125, 0>;
>   let fnptr73: *fn = @get_struct_field<toNext3, 0>;
>   let captures73: box<erased> = @get_struct_field<toNext3, 1>;
>   let struct56: { str } = @make_struct{ s1 };
>   let var188: [ `0 { [] }, `1 { str } ] = @make_union<1, struct56>;
>   let var189:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr73, captures73, var188);
>   return var189;
> }
> 
> proc clos_52(captures_105: box<erased>, toNext3: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box124: box<{}> = @ptr_cast(captures_105 as box<{}>);
>   let captures_stack124: {} = @get_boxed<captures_box124>;
>   let captures_stack_126: { { *fn, box<erased> } } = @make_struct{ toNext3 };
>   let captures_box_126: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_126);
>   let captures_252: box<erased> = @ptr_cast(captures_box_126 as box<erased>);
>   let fn_ptr_126: *fn = @make_fn_ptr<clos_126>;
>   let var186: { *fn, box<erased> } = @make_struct{ fn_ptr_126, captures_252 };
>   let struct55: { { *fn, box<erased> } } = @make_struct{ var186 };
>   let unboxed16:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<1, struct55>;
>   let var187:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed16);
>   return var187;
> }
> 
> global outLine7: { *fn, box<erased> } = @call_direct(outLine_thunk6);
> 
> proc outLine_thunk6(): { *fn, box<erased> }
> {
>   let captures_stack_53: {} = @make_struct{};
>   let captures_box_53: box<{}> = @make_box(captures_stack_53);
>   let captures_106: box<erased> = @ptr_cast(captures_box_53 as box<erased>);
>   let fn_ptr_53: *fn = @make_fn_ptr<clos_53>;
>   let outLine_closure6: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_53, captures_106 };
>   return outLine_closure6;
> }
> 
> proc clos_128(captures_257: box<erased>, x: {}):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box128: box<{ { *fn, box<erased> } }>
>     = @ptr_cast(captures_257 as box<{ { *fn, box<erased> } }>);
>   let captures_stack128: { { *fn, box<erased> } }
>     = @get_boxed<captures_box128>;
>   let toNext2: { *fn, box<erased> } = @get_struct_field<captures_stack128, 0>;
>   let fnptr74: *fn = @get_struct_field<toNext2, 0>;
>   let captures74: box<erased> = @get_struct_field<toNext2, 1>;
>   let struct58: { {} } = @make_struct{ x };
>   let var193: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct58>;
>   let var194:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr74, captures74, var193);
>   return var194;
> }
> 
> proc clos_127(captures_255: box<erased>, toNext2: { *fn, box<erased> }):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box127: box<{ str }> = @ptr_cast(captures_255 as box<{ str }>);
>   let captures_stack127: { str } = @get_boxed<captures_box127>;
>   let s: str = @get_struct_field<captures_stack127, 0>;
>   let captures_stack_128: { { *fn, box<erased> } } = @make_struct{ toNext2 };
>   let captures_box_128: box<{ { *fn, box<erased> } }>
>     = @make_box(captures_stack_128);
>   let captures_256: box<erased> = @ptr_cast(captures_box_128 as box<erased>);
>   let fn_ptr_128: *fn = @make_fn_ptr<clos_128>;
>   let unboxed17: { *fn, box<erased> }
>     = @make_struct{ fn_ptr_128, captures_256 };
>   let var191: box<%type_1 = { *fn, box<erased> }> = @make_box(unboxed17);
>   let struct57: { str, box<%type_1 = { *fn, box<erased> }> }
>     = @make_struct{ s, var191 };
>   let unboxed18:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<2, struct57>;
>   let var192:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed18);
>   return var192;
> }
> 
> proc clos_53(captures_107: box<erased>, s: str): { *fn, box<erased> }
> {
>   let captures_box126: box<{}> = @ptr_cast(captures_107 as box<{}>);
>   let captures_stack126: {} = @get_boxed<captures_box126>;
>   let captures_stack_127: { str } = @make_struct{ s };
>   let captures_box_127: box<{ str }> = @make_box(captures_stack_127);
>   let captures_254: box<erased> = @ptr_cast(captures_box_127 as box<erased>);
>   let fn_ptr_127: *fn = @make_fn_ptr<clos_127>;
>   let var190: { *fn, box<erased> } = @make_struct{ fn_ptr_127, captures_254 };
>   return var190;
> }
> 
> proc clos_132(captures_265: box<erased>, lastName: str): { *fn, box<erased> }
> {
>   let captures_box132: box<{ str, { *fn, box<erased> } }>
>     = @ptr_cast(captures_265 as box<{ str, { *fn, box<erased> } }>);
>   let captures_stack132: { str, { *fn, box<erased> } }
>     = @get_boxed<captures_box132>;
>   let firstName: str = @get_struct_field<captures_stack132, 0>;
>   let outLine4: { *fn, box<erased> } = @get_struct_field<captures_stack132, 1>;
>   let fnptr85: *fn = @get_struct_field<outLine3, 0>;
>   let captures85: box<erased> = @get_struct_field<outLine3, 1>;
>   let var211: str = "Hello ";
>   let var212: str = " ";
>   let var213: str = "!";
>   let var214: str
>     = @call_kfn(str_concat, var211, firstName, var212, lastName, var213);
>   let var215: { *fn, box<erased> }
>     = @call_indirect(fnptr85, captures85, var214);
>   return var215;
> }
> 
> proc clos_131(captures_263: box<erased>, y: {}): { *fn, box<erased> }
> {
>   let captures_box131:
>         box<
>           {
>            { *fn, box<erased> },
>             str,
>             { *fn, box<erased> },
>             { *fn, box<erased> }
>            ,
>           }>
>     = @ptr_cast(
>         captures_263 as
>         box<
>           {
>            { *fn, box<erased> },
>             str,
>             { *fn, box<erased> },
>             { *fn, box<erased> }
>            ,
>           }>);
>   let captures_stack131:
>         { { *fn, box<erased> }, str, { *fn, box<erased> }, { *fn, box<erased> } ,
>         }
>     = @get_boxed<captures_box131>;
>   let await5: { *fn, box<erased> } = @get_struct_field<captures_stack131, 0>;
>   let firstName: str = @get_struct_field<captures_stack131, 1>;
>   let inLine3: { *fn, box<erased> } = @get_struct_field<captures_stack131, 2>;
>   let outLine5: { *fn, box<erased> } = @get_struct_field<captures_stack131, 3>;
>   let fnptr83: *fn = @get_struct_field<await4, 0>;
>   let captures83: box<erased> = @get_struct_field<await4, 1>;
>   let var208: { *fn, box<erased> }
>     = @call_indirect(fnptr83, captures83, inLine2);
>   let fnptr84: *fn = @get_struct_field<var208, 0>;
>   let captures84: box<erased> = @get_struct_field<var208, 1>;
>   let captures_stack_132: { str, { *fn, box<erased> } }
>     = @make_struct{ firstName, outLine4 };
>   let captures_box_132: box<{ str, { *fn, box<erased> } }>
>     = @make_box(captures_stack_132);
>   let captures_264: box<erased> = @ptr_cast(captures_box_132 as box<erased>);
>   let fn_ptr_132: *fn = @make_fn_ptr<clos_132>;
>   let var209: { *fn, box<erased> } = @make_struct{ fn_ptr_132, captures_264 };
>   let var210: { *fn, box<erased> }
>     = @call_indirect(fnptr84, captures84, var209);
>   return var210;
> }
> 
> proc clos_130(captures_261: box<erased>, firstName: str): { *fn, box<erased> }
> {
>   let captures_box130:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_261 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack130:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box130>;
>   let await6: { *fn, box<erased> } = @get_struct_field<captures_stack130, 0>;
>   let inLine4: { *fn, box<erased> } = @get_struct_field<captures_stack130, 1>;
>   let outLine6: { *fn, box<erased> } = @get_struct_field<captures_stack130, 2>;
>   let fnptr80: *fn = @get_struct_field<await3, 0>;
>   let captures80: box<erased> = @get_struct_field<await3, 1>;
>   let fnptr81: *fn = @get_struct_field<outLine2, 0>;
>   let captures81: box<erased> = @get_struct_field<outLine2, 1>;
>   let var203: str = "What's your last name?";
>   let var204: { *fn, box<erased> }
>     = @call_indirect(fnptr81, captures81, var203);
>   let var205: { *fn, box<erased> }
>     = @call_indirect(fnptr80, captures80, var204);
>   let fnptr82: *fn = @get_struct_field<var205, 0>;
>   let captures82: box<erased> = @get_struct_field<var205, 1>;
>   let captures_stack_131:
>         { { *fn, box<erased> }, str, { *fn, box<erased> }, { *fn, box<erased> } ,
>         }
>     = @make_struct{ await5, firstName, inLine3, outLine5 };
>   let captures_box_131:
>         box<
>           {
>            { *fn, box<erased> },
>             str,
>             { *fn, box<erased> },
>             { *fn, box<erased> }
>            ,
>           }>
>     = @make_box(captures_stack_131);
>   let captures_262: box<erased> = @ptr_cast(captures_box_131 as box<erased>);
>   let fn_ptr_131: *fn = @make_fn_ptr<clos_131>;
>   let var206: { *fn, box<erased> } = @make_struct{ fn_ptr_131, captures_262 };
>   let var207: { *fn, box<erased> }
>     = @call_indirect(fnptr82, captures82, var206);
>   return var207;
> }
> 
> proc clos_129(captures_259: box<erased>, x1: {}): { *fn, box<erased> }
> {
>   let captures_box129:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @ptr_cast(
>         captures_259 as
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>);
>   let captures_stack129:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @get_boxed<captures_box129>;
>   let await7: { *fn, box<erased> } = @get_struct_field<captures_stack129, 0>;
>   let inLine5: { *fn, box<erased> } = @get_struct_field<captures_stack129, 1>;
>   let outLine7: { *fn, box<erased> } = @get_struct_field<captures_stack129, 2>;
>   let fnptr78: *fn = @get_struct_field<await2, 0>;
>   let captures78: box<erased> = @get_struct_field<await2, 1>;
>   let var200: { *fn, box<erased> }
>     = @call_indirect(fnptr78, captures78, inLine1);
>   let fnptr79: *fn = @get_struct_field<var200, 0>;
>   let captures79: box<erased> = @get_struct_field<var200, 1>;
>   let captures_stack_130:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ await6, inLine4, outLine6 };
>   let captures_box_130:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_130);
>   let captures_260: box<erased> = @ptr_cast(captures_box_130 as box<erased>);
>   let fn_ptr_130: *fn = @make_fn_ptr<clos_130>;
>   let var201: { *fn, box<erased> } = @make_struct{ fn_ptr_130, captures_260 };
>   let var202: { *fn, box<erased> }
>     = @call_indirect(fnptr79, captures79, var201);
>   return var202;
> }
> 
> proc main_thunk(): { *fn, box<erased> }
> {
>   let fnptr75: *fn = @get_struct_field<await1, 0>;
>   let captures75: box<erased> = @get_struct_field<await1, 1>;
>   let fnptr76: *fn = @get_struct_field<outLine1, 0>;
>   let captures76: box<erased> = @get_struct_field<outLine1, 1>;
>   let var195: str = "What's your first name?";
>   let var196: { *fn, box<erased> }
>     = @call_indirect(fnptr76, captures76, var195);
>   let var197: { *fn, box<erased> }
>     = @call_indirect(fnptr75, captures75, var196);
>   let fnptr77: *fn = @get_struct_field<var197, 0>;
>   let captures77: box<erased> = @get_struct_field<var197, 1>;
>   let captures_stack_129:
>         { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }
>     = @make_struct{ await7, inLine5, outLine7 };
>   let captures_box_129:
>         box<
>           { { *fn, box<erased> }, { *fn, box<erased> }, { *fn, box<erased> } }>
>     = @make_box(captures_stack_129);
>   let captures_258: box<erased> = @ptr_cast(captures_box_129 as box<erased>);
>   let fn_ptr_129: *fn = @make_fn_ptr<clos_129>;
>   let var198: { *fn, box<erased> } = @make_struct{ fn_ptr_129, captures_258 };
>   let var199: { *fn, box<erased> }
>     = @call_indirect(fnptr77, captures77, var198);
>   return var199;
> }
> 
> global main1: { *fn, box<erased> } = @call_direct(main_thunk);
> 
> proc clos_133(captures_267: box<erased>, x2: [ `0 { [] }, `1 { {} } ]):
>   box<
>     %type_2 =
>     [
>        `0 { [ `0 { [] }, `1 { {} } ] },
>        `1 { { *fn, box<erased> } },
>        `2 { str, box<%type_1 = { *fn, box<erased> }> }
>     ]>
> {
>   let captures_box133: box<{}> = @ptr_cast(captures_267 as box<{}>);
>   let captures_stack133: {} = @get_boxed<captures_box133>;
>   let struct60: { [ `0 { [] }, `1 { {} } ] } = @make_struct{ x2 };
>   let unboxed20:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @make_union<0, struct60>;
>   let var222:
>         box<
>           %type_2 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @make_box(unboxed20);
>   return var222;
> }
> 
> proc clos_135(
>   captures_272: box<erased>,
>    t: box<%type_4 = [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>):
>   [
>      `0 {
>          [ `0 { [] }, `1 { {} } ],
>           box<
>             %type_4 =
>             [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>          ,
>         }
>   ]
> {
>   let captures_box136:
>         box<
>           {
>            { *fn, box<erased> },
>             int,
>             box<
>               %type_3 =
>               [
>                  `0 { [ `0 { [] }, `1 { {} } ] },
>                  `1 { { *fn, box<erased> } },
>                  `2 { str, box<%type_1 = { *fn, box<erased> }> }
>               ]>
>            ,
>           }>
>     = @ptr_cast(
>         captures_272 as
>         box<
>           {
>            { *fn, box<erased> },
>             int,
>             box<
>               %type_3 =
>               [
>                  `0 { [ `0 { [] }, `1 { {} } ] },
>                  `1 { { *fn, box<erased> } },
>                  `2 { str, box<%type_1 = { *fn, box<erased> }> }
>               ]>
>            ,
>           }>);
>   let captures_stack136:
>         {
>          { *fn, box<erased> },
>           int,
>           box<
>             %type_3 =
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { { *fn, box<erased> } },
>                `2 { str, box<%type_1 = { *fn, box<erased> }> }
>             ]>
>          ,
>         }
>     = @get_boxed<captures_box136>;
>   let handle: { *fn, box<erased> } = @get_struct_field<captures_stack136, 0>;
>   let i: int = @get_struct_field<captures_stack136, 1>;
>   let op1:
>         box<
>           %type_3 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @get_struct_field<captures_stack136, 2>;
>   let inner1:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { { *fn, box<erased> } },
>            `2 { str, box<%type_1 = { *fn, box<erased> }> }
>         ]
>     = @get_boxed<op1>;
>   let discr7: int = @get_union_id<inner1>;
>   switch discr7 {
>   0 -> {
>     let payload16: { [ `0 { [] }, `1 { {} } ] } = @get_union_struct<inner1>;
>     let x3: [ `0 { [] }, `1 { {} } ] = @get_struct_field<payload16, 0>;
>     let struct63:
>           {
>            [ `0 { [] }, `1 { {} } ],
>             box<
>               %type_4 =
>               [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>            ,
>           }
>       = @make_struct{ x3, t };
>     @make_union<0, struct63>
>   }
>   1 -> {
>     let payload14: { { *fn, box<erased> } } = @get_union_struct<inner1>;
>     let f: { *fn, box<erased> } = @get_struct_field<payload14, 0>;
>     let fnptr90: *fn = @get_struct_field<handle, 0>;
>     let captures90: box<erased> = @get_struct_field<handle, 1>;
>     let fnptr91: *fn = @get_struct_field<f, 0>;
>     let captures91: box<erased> = @get_struct_field<f, 1>;
>     let var225: str = "stdin";
>     let var226: str = @call_kfn(itos, i);
>     let var227: str = @call_kfn(str_concat, var225, var226);
>     let var228:
>           box<
>             %type_3 =
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { { *fn, box<erased> } },
>                `2 { str, box<%type_1 = { *fn, box<erased> }> }
>             ]>
>       = @call_indirect(fnptr91, captures91, var227);
>     let var229: { *fn, box<erased> }
>       = @call_indirect(fnptr90, captures90, var228);
>     let fnptr92: *fn = @get_struct_field<var229, 0>;
>     let captures92: box<erased> = @get_struct_field<var229, 1>;
>     let var230: int = 1;
>     let var231: int = @call_kfn(add, i, var230);
>     let var232: { *fn, box<erased> }
>       = @call_indirect(fnptr92, captures92, var231);
>     let fnptr93: *fn = @get_struct_field<var232, 0>;
>     let captures93: box<erased> = @get_struct_field<var232, 1>;
>     let struct61:
>           {
>            box<
>              %type_4 =
>              [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>            ,
>           }
>       = @make_struct{ t };
>     let unboxed21:
>           [
>              `0 {},
>              `1 {
>                  box<
>                    %type_4 =
>                    [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>                  ,
>                 },
>              `2 { str, box<%type_4> }
>           ]
>       = @make_union<1, struct61>;
>     let var233:
>           box<
>             %type_4 =
>             [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>       = @make_box(unboxed21);
>     @call_indirect(fnptr93, captures93, var233)
>   }
>   2 -> {
>     let payload15: { str, box<%type_1 = { *fn, box<erased> }> }
>       = @get_union_struct<inner1>;
>     let s2: str = @get_struct_field<payload15, 0>;
>     let f1: box<%type_1 = { *fn, box<erased> }>
>       = @get_struct_field<payload15, 1>;
>     let fnptr94: *fn = @get_struct_field<handle, 0>;
>     let captures94: box<erased> = @get_struct_field<handle, 1>;
>     let inner2: { *fn, box<erased> } = @get_boxed<f1>;
>     let fnptr95: *fn = @get_struct_field<inner2, 0>;
>     let captures95: box<erased> = @get_struct_field<inner2, 1>;
>     let var234: {} = @make_struct{};
>     let var235:
>           box<
>             %type_3 =
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { { *fn, box<erased> } },
>                `2 { str, box<%type_1 = { *fn, box<erased> }> }
>             ]>
>       = @call_indirect(fnptr95, captures95, var234);
>     let var236: { *fn, box<erased> }
>       = @call_indirect(fnptr94, captures94, var235);
>     let fnptr96: *fn = @get_struct_field<var236, 0>;
>     let captures96: box<erased> = @get_struct_field<var236, 1>;
>     let var237: int = 1;
>     let var238: int = @call_kfn(add, i, var237);
>     let var239: { *fn, box<erased> }
>       = @call_indirect(fnptr96, captures96, var238);
>     let fnptr97: *fn = @get_struct_field<var239, 0>;
>     let captures97: box<erased> = @get_struct_field<var239, 1>;
>     let struct62:
>           {
>            str,
>             box<
>               %type_4 =
>               [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>            ,
>           }
>       = @make_struct{ s2, t };
>     let unboxed22:
>           [
>              `0 {},
>              `1 {
>                  box<
>                    %type_4 =
>                    [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>                  ,
>                 },
>              `2 { str, box<%type_4> }
>           ]
>       = @make_union<2, struct62>;
>     let var240:
>           box<
>             %type_4 =
>             [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>       = @make_box(unboxed22);
>     @call_indirect(fnptr97, captures97, var240)
>   }
>   } in join join7;
>   return join7;
> }
> 
> proc clos_134(captures_270: box<erased>, i: int): { *fn, box<erased> }
> {
>   let captures_box135:
>         box<
>           {
>            { *fn, box<erased> },
>             box<
>               %type_3 =
>               [
>                  `0 { [ `0 { [] }, `1 { {} } ] },
>                  `1 { { *fn, box<erased> } },
>                  `2 { str, box<%type_1 = { *fn, box<erased> }> }
>               ]>
>            ,
>           }>
>     = @ptr_cast(
>         captures_270 as
>         box<
>           {
>            { *fn, box<erased> },
>             box<
>               %type_3 =
>               [
>                  `0 { [ `0 { [] }, `1 { {} } ] },
>                  `1 { { *fn, box<erased> } },
>                  `2 { str, box<%type_1 = { *fn, box<erased> }> }
>               ]>
>            ,
>           }>);
>   let captures_stack135:
>         {
>          { *fn, box<erased> },
>           box<
>             %type_3 =
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { { *fn, box<erased> } },
>                `2 { str, box<%type_1 = { *fn, box<erased> }> }
>             ]>
>          ,
>         }
>     = @get_boxed<captures_box135>;
>   let handle: { *fn, box<erased> } = @get_struct_field<captures_stack135, 0>;
>   let op1:
>         box<
>           %type_3 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @get_struct_field<captures_stack135, 1>;
>   let captures_stack_136:
>         {
>          { *fn, box<erased> },
>           int,
>           box<
>             %type_3 =
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { { *fn, box<erased> } },
>                `2 { str, box<%type_1 = { *fn, box<erased> }> }
>             ]>
>          ,
>         }
>     = @make_struct{ handle, i, op1 };
>   let captures_box_136:
>         box<
>           {
>            { *fn, box<erased> },
>             int,
>             box<
>               %type_3 =
>               [
>                  `0 { [ `0 { [] }, `1 { {} } ] },
>                  `1 { { *fn, box<erased> } },
>                  `2 { str, box<%type_1 = { *fn, box<erased> }> }
>               ]>
>            ,
>           }>
>     = @make_box(captures_stack_136);
>   let captures_271: box<erased> = @ptr_cast(captures_box_136 as box<erased>);
>   let fn_ptr_136: *fn = @make_fn_ptr<clos_135>;
>   let var224: { *fn, box<erased> } = @make_struct{ fn_ptr_136, captures_271 };
>   return var224;
> }
> 
> proc clos_handle(
>   captures_handle: box<erased>,
>    op1:
>      box<
>        %type_3 =
>        [
>           `0 { [ `0 { [] }, `1 { {} } ] },
>           `1 { { *fn, box<erased> } },
>           `2 { str, box<%type_1 = { *fn, box<erased> }> }
>        ]>):
>   { *fn, box<erased> }
> {
>   let captures_box134: box<{}> = @ptr_cast(captures_handle as box<{}>);
>   let captures_stack134: {} = @get_boxed<captures_box134>;
>   let rec_fn_ptr_handle: *fn = @make_fn_ptr<clos_handle>;
>   let handle: { *fn, box<erased> }
>     = @make_struct{ rec_fn_ptr_handle, captures_handle };
>   let captures_stack_135:
>         {
>          { *fn, box<erased> },
>           box<
>             %type_3 =
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { { *fn, box<erased> } },
>                `2 { str, box<%type_1 = { *fn, box<erased> }> }
>             ]>
>          ,
>         }
>     = @make_struct{ handle, op1 };
>   let captures_box_135:
>         box<
>           {
>            { *fn, box<erased> },
>             box<
>               %type_3 =
>               [
>                  `0 { [ `0 { [] }, `1 { {} } ] },
>                  `1 { { *fn, box<erased> } },
>                  `2 { str, box<%type_1 = { *fn, box<erased> }> }
>               ]>
>            ,
>           }>
>     = @make_box(captures_stack_135);
>   let captures_269: box<erased> = @ptr_cast(captures_box_135 as box<erased>);
>   let fn_ptr_135: *fn = @make_fn_ptr<clos_134>;
>   let var223: { *fn, box<erased> } = @make_struct{ fn_ptr_135, captures_269 };
>   return var223;
> }
> 
> proc main_handler_thunk():
>   [
>      `0 {
>          [ `0 { [] }, `1 { {} } ],
>           box<
>             %type_4 =
>             [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>          ,
>         }
>   ]
> {
>   let fnptr86: *fn = @get_struct_field<main1, 0>;
>   let captures86: box<erased> = @get_struct_field<main1, 1>;
>   let captures_stack_133: {} = @make_struct{};
>   let captures_box_133: box<{}> = @make_box(captures_stack_133);
>   let captures_266: box<erased> = @ptr_cast(captures_box_133 as box<erased>);
>   let fn_ptr_133: *fn = @make_fn_ptr<clos_133>;
>   let var216: { *fn, box<erased> } = @make_struct{ fn_ptr_133, captures_266 };
>   let op:
>         box<
>           %type_3 =
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { { *fn, box<erased> } },
>              `2 { str, box<%type_1 = { *fn, box<erased> }> }
>           ]>
>     = @call_indirect(fnptr86, captures86, var216);
>   let captures_stack_134: {} = @make_struct{};
>   let captures_box_134: box<{}> = @make_box(captures_stack_134);
>   let captures_268: box<erased> = @ptr_cast(captures_box_134 as box<erased>);
>   let fn_ptr_134: *fn = @make_fn_ptr<clos_handle>;
>   let handle: { *fn, box<erased> } = @make_struct{ fn_ptr_134, captures_268 };
>   let fnptr87: *fn = @get_struct_field<handle, 0>;
>   let captures87: box<erased> = @get_struct_field<handle, 1>;
>   let var217: { *fn, box<erased> } = @call_indirect(fnptr87, captures87, op);
>   let fnptr88: *fn = @get_struct_field<var217, 0>;
>   let captures88: box<erased> = @get_struct_field<var217, 1>;
>   let var218: int = 0;
>   let var219: { *fn, box<erased> }
>     = @call_indirect(fnptr88, captures88, var218);
>   let fnptr89: *fn = @get_struct_field<var219, 0>;
>   let captures89: box<erased> = @get_struct_field<var219, 1>;
>   let struct59: {} = @make_struct{};
>   let unboxed19:
>         [
>            `0 {},
>            `1 {
>                box<
>                  %type_4 =
>                  [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>                ,
>               },
>            `2 { str, box<%type_4> }
>         ]
>     = @make_union<0, struct59>;
>   let var220:
>         box<%type_4 = [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>     = @make_box(unboxed19);
>   let var221:
>         [
>            `0 {
>                [ `0 { [] }, `1 { {} } ],
>                 box<
>                   %type_4 =
>                   [ `0 {}, `1 { box<%type_4> }, `2 { str, box<%type_4> } ]>
>                ,
>               }
>         ]
>     = @call_indirect(fnptr89, captures89, var220);
>   return var221;
> }
> 
> global main_handler:
>   [
>      `0 {
>          [ `0 { [] }, `1 { {} } ],
>           box<
>             %type_0 =
>             [ `0 {}, `1 { box<%type_0> }, `2 { str, box<%type_0> } ]>
>          ,
>         }
>   ]
>   = @call_direct(main_handler_thunk);
> 
> entry main_handler;

> cor-out +eval -print
> main_handler = [0 [1 []]
>                [2
>                [72 101 108 108 111 32 115 116 100
>                105 110 49 32 115 116 100 105 110
>                51 33]
>                [1
>                [2
>                [87 104 97 116 39 115 32 121 111
>                117 114 32 108 97 115 116 32 110
>                97 109 101 63]
>                [1
>                [2
>                [87 104 97 116 39 115 32 121 111
>                117 114 32 102 105 114 115 116 32
>                110 97 109 101 63] [0]]]]]]]
>              > Done (Ok {})
>                  (Stdout "Hello stdin1 stdin3!"
>                     (Stdin
>                        (Stdout
>                           "What's your last name?"
>                           (Stdin
>                              (Stdout
>                                 "What's your first name?"
>                                 (EntryPoint ))))))