# cor +mono -print
# cor +ir -print
# cor +eval -print

# https://github.com/roc-lang/roc/issues/5464
Op a : [
    StdoutLine Str ({} -> Op a),
    StdinLine (Str -> Op a),
    Done a,
]

Task ok err op : ([ Ok ok, Err err ] -> op) -> op

sig succeed : ok -> Task ok * *
let succeed = \ok -> \toNext -> toNext (Ok ok);;

sig fail : err -> Task * err *
let fail = \err-> \toNext -> toNext (Err err);;

sig await : Task ok1 err op -> (ok1 -> Task ok2 err op) -> Task ok2 err op
let await = \fromResult -> \next ->
    \continue -> fromResult (\result ->
        let inner = when result is
            | Ok v -> next v
            | Err e -> fail e
        end
        in
        inner continue)
;;


sig outLine : Str -> Task {} * (Op *)
let outLine = \s -> (\toNext -> StdoutLine s (\x -> toNext (Ok x)));;

sig inLine : Task Str * (Op *)
let inLine = \toNext -> StdinLine (\s -> toNext (Ok s));;

sig main : Task {} * (Op *)
let main =
    await (inLine)
        (\firstName -> outLine "What's your last name?")
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

> cor-out +mono -print
> specializations:
>   let lam41 = \next -[lam41 fromResult]->
>     \continue -[lam31 fromResult next]->
>       (fromResult
>          \result -[lam21 continue next]->
>            (let inner =
>               when result is
>                 | Okv -> next v
>                 | Erre -> fail2 e
>               end
>            in
>            inner continue))
>   
>   let lam31 = \continue -[lam31 fromResult
>                         next]->
>     fromResult
>       \result -[lam21 continue next]->
>         (let inner =
>            when result is
>              | Okv -> next v
>              | Erre -> fail2 e
>            end
>         in
>         inner continue)
>   
>   let lam21 = \result -[lam21 continue next]->
>     let inner =
>       when result is
>         | Okv -> next v
>         | Erre -> fail2 e
>       end
>     in
>     inner continue
>   
>   let lam12 = \toNext1 -[lam12 err]->
>     toNext1 (Err err)
>   
>   let fail2 = \err -[fail2]->
>     \toNext1 -[lam12 err]-> (toNext1 (Err err))
>   
>   let await2 = \fromResult -[await2]->
>     \next -[lam41 fromResult]->
>       \continue -[lam31 fromResult next]->
>         (fromResult
>            \result -[lam21 continue next]->
>              (let inner =
>                 when result is
>                   | Okv -> next v
>                   | Erre -> fail2 e
>                 end
>              in
>              inner continue))
>   
>   let lam71 = \s1 -[lam71 toNext3]->
>     toNext3 (Ok s1)
>   
>   let inLine2 = \toNext3 -[inLine2]->
>     StdinLine
>       \s1 -[lam71 toNext3]-> (toNext3 (Ok s1))
>   
>   let lam81 = \firstName -[lam81]->
>     outLine2 "What's your last name?"
>   
>   let lam61 = \toNext2 -[lam61 s]->
>     StdoutLine s
>       \x -[lam51 toNext2]-> (toNext2 (Ok x))
>   
>   let lam51 = \x -[lam51 toNext2]->
>     toNext2 (Ok x)
>   
>   let outLine2 = \s -[outLine2]->
>     \toNext2 -[lam61 s]->
>       (StdoutLine s
>          \x -[lam51 toNext2]-> (toNext2 (
>                                         Ok x)))
>   
>   let main1 =
>     (await2 inLine2)
>       \firstName -[lam81]->
>         (outLine2 "What's your last name?")
>   
>   let lam91 = \x1 -[lam91]-> Done x1
>   
>   let handle11 = \op1 -[handle11]->
>     \i -[lam111 handle op1]->
>       \t -[lam101 handle i op1]->
>         when op1 is
>           | StdinLinef ->
>             ((handle
>                 (f str_concat "stdin" itos i))
>                add i 1) (Stdin t)
>           | StdoutLines2 f1 ->
>             ((handle (f1 {})) add i 1)
>               (Stdout s2 t)
>           | Donex2 -> Done x2 t
>         end
>   
>   let lam111 = \i -[lam111 handle op1]->
>     \t -[lam101 handle i op1]->
>       when op1 is
>         | StdinLinef ->
>           ((handle (f str_concat "stdin" itos i))
>              add i 1) (Stdin t)
>         | StdoutLines2 f1 ->
>           ((handle (f1 {})) add i 1)
>             (Stdout s2 t)
>         | Donex2 -> Done x2 t
>       end
>   
>   let lam101 = \t -[lam101 handle i op1]->
>     when op1 is
>       | StdinLinef ->
>         ((handle (f str_concat "stdin" itos i))
>            add i 1) (Stdin t)
>       | StdoutLines2 f1 ->
>         ((handle (f1 {})) add i 1) (Stdout s2 t)
>       | Donex2 -> Done x2 t
>     end
>   
>   let main_handler =
>     let op = main1 \x1 -[lam91]-> (Done x1) in
>     let handle =
>       \op1 -[handle11]->
>         \i -[lam111 handle op1]->
>           \t -[lam101 handle i op1]->
>             when op1 is
>               | StdinLinef ->
>                 ((handle
>                     (f str_concat "stdin" itos i))
>                    add i 1) (Stdin t)
>               | StdoutLines2 f1 ->
>                 ((handle (f1 {})) add i 1)
>                   (Stdout s2 t)
>               | Donex2 -> Done x2 t
>             end
>     in
>     ((handle op) 0) (EntryPoint )
>   
>   
> entry_points:
>   main_handler

> cor-out +ir -print
> proc lam111(
>   captures_13:
>     [
>        `0 {
>            [ `0 {} ],
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>                `2 { str, [ `0 { [ `0 {} ] } ] }
>             ]
>            ,
>           }
>     ],
>    i: int):
>   [
>      `0 {
>          [ `0 {} ],
>           int,
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>              `2 { str, [ `0 { [ `0 {} ] } ] }
>           ]
>          ,
>         }
>   ]
> {
>   let captures_stack14:
>         {
>          [ `0 {} ],
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>              `2 { str, [ `0 { [ `0 {} ] } ] }
>           ]
>          ,
>         }
>     = @get_union_struct<captures_13>;
>   let handle: [ `0 {} ] = @get_struct_field<captures_stack14, 0>;
>   let op1:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>            `2 { str, [ `0 { [ `0 {} ] } ] }
>         ]
>     = @get_struct_field<captures_stack14, 1>;
>   let struct20:
>         {
>          [ `0 {} ],
>           int,
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>              `2 { str, [ `0 { [ `0 {} ] } ] }
>           ]
>          ,
>         }
>     = @make_struct{ handle, i, op1 };
>   let var20:
>         [
>            `0 {
>                [ `0 {} ],
>                 int,
>                 [
>                    `0 { [ `0 { [] }, `1 { {} } ] },
>                    `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>                    `2 { str, [ `0 { [ `0 {} ] } ] }
>                 ]
>                ,
>               }
>         ]
>     = @make_union<0, struct20>;
>   return var20;
> }
> 
> proc handle11(
>   captures_handle: [ `0 {} ],
>    op1:
>      [
>         `0 { [ `0 { [] }, `1 { {} } ] },
>         `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>         `2 { str, [ `0 { [ `0 {} ] } ] }
>      ]):
>   [
>      `0 {
>          [ `0 {} ],
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>              `2 { str, [ `0 { [ `0 {} ] } ] }
>           ]
>          ,
>         }
>   ]
> {
>   let captures_stack13: {} = @get_union_struct<captures_handle>;
>   let struct18: {} = @make_struct{};
>   let handle: [ `0 {} ] = @make_union<0, struct18>;
>   let struct19:
>         {
>          [ `0 {} ],
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>              `2 { str, [ `0 { [ `0 {} ] } ] }
>           ]
>          ,
>         }
>     = @make_struct{ handle, op1 };
>   let var19:
>         [
>            `0 {
>                [ `0 {} ],
>                 [
>                    `0 { [ `0 { [] }, `1 { {} } ] },
>                    `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>                    `2 { str, [ `0 { [ `0 {} ] } ] }
>                 ]
>                ,
>               }
>         ]
>     = @make_union<0, struct19>;
>   return var19;
> }
> 
> proc outLine2(captures_11: [ `0 {} ], s: str): [ `0 { [] }, `1 { str } ]
> {
>   let captures_stack11: {} = @get_union_struct<captures_11>;
>   let struct13: { str } = @make_struct{ s };
>   let var14: [ `0 { [] }, `1 { str } ] = @make_union<1, struct13>;
>   return var14;
> }
> 
> proc lam91(captures_12: [ `0 {} ], x1: [ `0 { [] }, `1 { {} } ]):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack12: {} = @get_union_struct<captures_12>;
>   let struct17: { [ `0 { [] }, `1 { {} } ] } = @make_struct{ x1 };
>   let var18:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>            `2 { str, [ `0 { [ `0 {} ] } ] }
>         ]
>     = @make_union<0, struct17>;
>   return var18;
> }
> 
> proc await2(captures_5: [ `0 {} ], fromResult: [ `0 {} ]): [ `0 { [ `0 {} ] } ]
> {
>   let captures_stack5: {} = @get_union_struct<captures_5>;
>   let struct5: { [ `0 {} ] } = @make_struct{ fromResult };
>   let var5: [ `0 { [ `0 {} ] } ] = @make_union<0, struct5>;
>   return var5;
> }
> 
> proc lam41(captures_: [ `0 { [ `0 {} ] } ], next: [ `0 {} ]):
>   [ `0 { [ `0 {} ], [ `0 {} ] } ]
> {
>   let captures_stack: { [ `0 {} ] } = @get_union_struct<captures_>;
>   let fromResult: [ `0 {} ] = @get_struct_field<captures_stack, 0>;
>   let struct: { [ `0 {} ], [ `0 {} ] } = @make_struct{ fromResult, next };
>   let var: [ `0 { [ `0 {} ], [ `0 {} ] } ] = @make_union<0, struct>;
>   return var;
> }
> 
> proc lam61(captures_9: [ `0 { [] }, `1 { str } ], toNext2: [ `0 {} ]):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack9: { str } = @get_union_struct<captures_9>;
>   let s: str = @get_struct_field<captures_stack9, 0>;
>   let struct10: { [ `0 {} ] } = @make_struct{ toNext2 };
>   let var11: [ `0 { [ `0 {} ] } ] = @make_union<0, struct10>;
>   let struct11: { str, [ `0 { [ `0 {} ] } ] } = @make_struct{ s, var11 };
>   let var12:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>            `2 { str, [ `0 { [ `0 {} ] } ] }
>         ]
>     = @make_union<2, struct11>;
>   return var12;
> }
> 
> proc fail2(captures_4: [ `0 {} ], err: []): [ `0 { [] }, `1 { str } ]
> {
>   let captures_stack4: {} = @get_union_struct<captures_4>;
>   let struct4: { [] } = @make_struct{ err };
>   let var4: [ `0 { [] }, `1 { str } ] = @make_union<0, struct4>;
>   return var4;
> }
> 
> proc inLine2(captures_7: [ `0 {} ], toNext3: [ `0 { [ `0 {} ], [ `0 {} ] } ]):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack7: {} = @get_union_struct<captures_7>;
>   let struct7: { [ `0 { [ `0 {} ], [ `0 {} ] } ] } = @make_struct{ toNext3 };
>   let var7: [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ]
>     = @make_union<0, struct7>;
>   let struct8: { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] }
>     = @make_struct{ var7 };
>   let var8:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>            `2 { str, [ `0 { [ `0 {} ] } ] }
>         ]
>     = @make_union<1, struct8>;
>   return var8;
> }
> 
> proc lam81(captures_8: [ `0 {} ], firstName: str): [ `0 { [] }, `1 { str } ]
> {
>   let captures_stack8: {} = @get_union_struct<captures_8>;
>   let struct9: {} = @make_struct{};
>   let var9: [ `0 {} ] = @make_union<0, struct9>;
>   let var10: str = "What's your last name?";
>   let cond6: int = @get_union_id<var9>;
>   switch cond6 {
>   0 -> { @call_direct(outLine2, var9, var10) }
>   } in join join7;
>   return join7;
> }
> 
> proc lam51(captures_10: [ `0 { [ `0 {} ] } ], x: {}):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack10: { [ `0 {} ] } = @get_union_struct<captures_10>;
>   let toNext2: [ `0 {} ] = @get_struct_field<captures_stack10, 0>;
>   let struct12: { {} } = @make_struct{ x };
>   let var13: [ `0 { [] }, `1 { {} } ] = @make_union<1, struct12>;
>   let cond7: int = @get_union_id<toNext2>;
>   switch cond7 {
>   0 -> { @call_direct(lam91, toNext2, var13) }
>   } in join join8;
>   return join8;
> }
> 
> proc lam12(captures_3: [ `0 { [] }, `1 { str } ], toNext1: [ `0 {} ]):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack3: { [] } = @get_union_struct<captures_3>;
>   let err: [] = @get_struct_field<captures_stack3, 0>;
>   let struct3: { [] } = @make_struct{ err };
>   let var3: [ `0 { [] }, `1 { {} } ] = @make_union<0, struct3>;
>   let cond4: int = @get_union_id<toNext1>;
>   switch cond4 {
>   0 -> { @call_direct(lam91, toNext1, var3) }
>   } in join join5;
>   return join5;
> }
> 
> proc main_thunk(): [ `0 { [ `0 {} ], [ `0 {} ] } ]
> {
>   let struct14: {} = @make_struct{};
>   let var15: [ `0 {} ] = @make_union<0, struct14>;
>   let struct15: {} = @make_struct{};
>   let var16: [ `0 {} ] = @make_union<0, struct15>;
>   let cond8: int = @get_union_id<var15>;
>   switch cond8 {
>   0 -> { @call_direct(await2, var15, var16) }
>   } in join join9;
>   let struct16: {} = @make_struct{};
>   let var17: [ `0 {} ] = @make_union<0, struct16>;
>   let cond9: int = @get_union_id<join9>;
>   switch cond9 {
>   0 -> { @call_direct(lam41, join9, var17) }
>   } in join join10;
>   return join10;
> }
> 
> proc lam31(captures_1: [ `0 { [ `0 {} ], [ `0 {} ] } ], continue: [ `0 {} ]):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack1: { [ `0 {} ], [ `0 {} ] } = @get_union_struct<captures_1>;
>   let fromResult: [ `0 {} ] = @get_struct_field<captures_stack1, 0>;
>   let next: [ `0 {} ] = @get_struct_field<captures_stack1, 1>;
>   let struct1: { [ `0 {} ], [ `0 {} ] } = @make_struct{ continue, next };
>   let var1: [ `0 { [ `0 {} ], [ `0 {} ] } ] = @make_union<0, struct1>;
>   let cond: int = @get_union_id<fromResult>;
>   switch cond {
>   0 -> { @call_direct(inLine2, fromResult, var1) }
>   } in join join;
>   return join;
> }
> 
> proc lam21(
>   captures_2: [ `0 { [ `0 {} ], [ `0 {} ] } ],
>    result: [ `0 { [] }, `1 { str } ]):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack2: { [ `0 {} ], [ `0 {} ] } = @get_union_struct<captures_2>;
>   let continue: [ `0 {} ] = @get_struct_field<captures_stack2, 0>;
>   let next: [ `0 {} ] = @get_struct_field<captures_stack2, 1>;
>   let discr: int = @get_union_id<result>;
>   switch discr {
>   0 -> {
>     let payload1: { [] } = @get_union_struct<result>;
>     let e: [] = @get_struct_field<payload1, 0>;
>     let struct2: {} = @make_struct{};
>     let var2: [ `0 {} ] = @make_union<0, struct2>;
>     let cond2: int = @get_union_id<var2>;
>     switch cond2 {
>     0 -> { @call_direct(fail2, var2, e) }
>     } in join join2;
>     join2
>   }
>   1 -> {
>     let payload: { str } = @get_union_struct<result>;
>     let v: str = @get_struct_field<payload, 0>;
>     let cond1: int = @get_union_id<next>;
>     switch cond1 {
>     0 -> { @call_direct(lam81, next, v) }
>     } in join join1;
>     join1
>   }
>   } in join join3;
>   let inner: [ `0 { [] }, `1 { str } ] = join3;
>   let cond3: int = @get_union_id<inner>;
>   switch cond3 {
>   0 -> { @call_direct(lam12, inner, continue) }
>   1 -> { @call_direct(lam61, inner, continue) }
>   } in join join4;
>   return join4;
> }
> 
> global main1: [ `0 { [ `0 {} ], [ `0 {} ] } ] = @call_direct(main_thunk);
> 
> proc lam71(captures_6: [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ], s1: str):
>   [
>      `0 { [ `0 { [] }, `1 { {} } ] },
>      `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>      `2 { str, [ `0 { [ `0 {} ] } ] }
>   ]
> {
>   let captures_stack6: { [ `0 { [ `0 {} ], [ `0 {} ] } ] }
>     = @get_union_struct<captures_6>;
>   let toNext3: [ `0 { [ `0 {} ], [ `0 {} ] } ]
>     = @get_struct_field<captures_stack6, 0>;
>   let struct6: { str } = @make_struct{ s1 };
>   let var6: [ `0 { [] }, `1 { str } ] = @make_union<1, struct6>;
>   let cond5: int = @get_union_id<toNext3>;
>   switch cond5 {
>   0 -> { @call_direct(lam21, toNext3, var6) }
>   } in join join6;
>   return join6;
> }
> 
> proc lam101(
>   captures_14:
>     [
>        `0 {
>            [ `0 {} ],
>             int,
>             [
>                `0 { [ `0 { [] }, `1 { {} } ] },
>                `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>                `2 { str, [ `0 { [ `0 {} ] } ] }
>             ]
>            ,
>           }
>     ],
>    t: box<%type_1 = [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>):
>   [
>      `0 {
>          [ `0 { [] }, `1 { {} } ],
>           box<
>             %type_1 =
>             [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>          ,
>         }
>   ]
> {
>   let captures_stack15:
>         {
>          [ `0 {} ],
>           int,
>           [
>              `0 { [ `0 { [] }, `1 { {} } ] },
>              `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>              `2 { str, [ `0 { [ `0 {} ] } ] }
>           ]
>          ,
>         }
>     = @get_union_struct<captures_14>;
>   let handle: [ `0 {} ] = @get_struct_field<captures_stack15, 0>;
>   let i: int = @get_struct_field<captures_stack15, 1>;
>   let op1:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>            `2 { str, [ `0 { [ `0 {} ] } ] }
>         ]
>     = @get_struct_field<captures_stack15, 2>;
>   let discr1: int = @get_union_id<op1>;
>   switch discr1 {
>   0 -> {
>     let payload4: { [ `0 { [] }, `1 { {} } ] } = @get_union_struct<op1>;
>     let x2: [ `0 { [] }, `1 { {} } ] = @get_struct_field<payload4, 0>;
>     let struct23:
>           {
>            [ `0 { [] }, `1 { {} } ],
>             box<
>               %type_1 =
>               [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>            ,
>           }
>       = @make_struct{ x2, t };
>     @make_union<0, struct23>
>   }
>   1 -> {
>     let payload2: { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] }
>       = @get_union_struct<op1>;
>     let f: [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ]
>       = @get_struct_field<payload2, 0>;
>     let var21: str = "stdin";
>     let var22: str = @call_kfn(itos, i);
>     let var23: str = @call_kfn(str_concat, var21, var22);
>     let cond10: int = @get_union_id<f>;
>     switch cond10 {
>     0 -> { @call_direct(lam71, f, var23) }
>     } in join join11;
>     let cond11: int = @get_union_id<handle>;
>     switch cond11 {
>     0 -> { @call_direct(handle11, handle, join11) }
>     } in join join12;
>     let var24: int = 1;
>     let var25: int = @call_kfn(add, i, var24);
>     let cond12: int = @get_union_id<join12>;
>     switch cond12 {
>     0 -> { @call_direct(lam111, join12, var25) }
>     } in join join13;
>     let struct21:
>           {
>            box<
>              %type_1 =
>              [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>            ,
>           }
>       = @make_struct{ t };
>     let unboxed:
>           [
>              `0 {},
>              `1 {
>                  box<
>                    %type_1 =
>                    [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>                  ,
>                 },
>              `2 { str, box<%type_1> }
>           ]
>       = @make_union<1, struct21>;
>     let var26:
>           box<
>             %type_1 =
>             [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>       = @make_box(unboxed);
>     let cond13: int = @get_union_id<join13>;
>     switch cond13 {
>     0 -> { @call_direct(lam101, join13, var26) }
>     } in join join14;
>     join14
>   }
>   2 -> {
>     let payload3: { str, [ `0 { [ `0 {} ] } ] } = @get_union_struct<op1>;
>     let s2: str = @get_struct_field<payload3, 0>;
>     let f1: [ `0 { [ `0 {} ] } ] = @get_struct_field<payload3, 1>;
>     let var27: {} = @make_struct{};
>     let cond14: int = @get_union_id<f1>;
>     switch cond14 {
>     0 -> { @call_direct(lam51, f1, var27) }
>     } in join join15;
>     let cond15: int = @get_union_id<handle>;
>     switch cond15 {
>     0 -> { @call_direct(handle11, handle, join15) }
>     } in join join16;
>     let var28: int = 1;
>     let var29: int = @call_kfn(add, i, var28);
>     let cond16: int = @get_union_id<join16>;
>     switch cond16 {
>     0 -> { @call_direct(lam111, join16, var29) }
>     } in join join17;
>     let struct22:
>           {
>            str,
>             box<
>               %type_1 =
>               [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>            ,
>           }
>       = @make_struct{ s2, t };
>     let unboxed1:
>           [
>              `0 {},
>              `1 {
>                  box<
>                    %type_1 =
>                    [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>                  ,
>                 },
>              `2 { str, box<%type_1> }
>           ]
>       = @make_union<2, struct22>;
>     let var30:
>           box<
>             %type_1 =
>             [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>       = @make_box(unboxed1);
>     let cond17: int = @get_union_id<join17>;
>     switch cond17 {
>     0 -> { @call_direct(lam101, join17, var30) }
>     } in join join18;
>     join18
>   }
>   } in join join19;
>   return join19;
> }
> 
> proc main_handler_thunk():
>   [
>      `0 {
>          [ `0 { [] }, `1 { {} } ],
>           box<
>             %type_1 =
>             [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>          ,
>         }
>   ]
> {
>   let struct24: {} = @make_struct{};
>   let var31: [ `0 {} ] = @make_union<0, struct24>;
>   let cond18: int = @get_union_id<main1>;
>   switch cond18 {
>   0 -> { @call_direct(lam31, main1, var31) }
>   } in join join20;
>   let op:
>         [
>            `0 { [ `0 { [] }, `1 { {} } ] },
>            `1 { [ `0 { [ `0 { [ `0 {} ], [ `0 {} ] } ] } ] },
>            `2 { str, [ `0 { [ `0 {} ] } ] }
>         ]
>     = join20;
>   let struct25: {} = @make_struct{};
>   let handle: [ `0 {} ] = @make_union<0, struct25>;
>   let cond19: int = @get_union_id<handle>;
>   switch cond19 {
>   0 -> { @call_direct(handle11, handle, op) }
>   } in join join21;
>   let var32: int = 0;
>   let cond20: int = @get_union_id<join21>;
>   switch cond20 {
>   0 -> { @call_direct(lam111, join21, var32) }
>   } in join join22;
>   let struct26: {} = @make_struct{};
>   let unboxed2:
>         [
>            `0 {},
>            `1 {
>                box<
>                  %type_1 =
>                  [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>                ,
>               },
>            `2 { str, box<%type_1> }
>         ]
>     = @make_union<0, struct26>;
>   let var33:
>         box<%type_1 = [ `0 {}, `1 { box<%type_1> }, `2 { str, box<%type_1> } ]>
>     = @make_box(unboxed2);
>   let cond21: int = @get_union_id<join22>;
>   switch cond21 {
>   0 -> { @call_direct(lam101, join22, var33) }
>   } in join join23;
>   return join23;
> }
> 
> global main_handler:
>   [
>      `0 {
>          [ `0 { [] }, `1 { {} } ],
>           box<
>             %type_2 =
>             [ `0 {}, `1 { box<%type_2> }, `2 { str, box<%type_2> } ]>
>          ,
>         }
>   ]
>   = @call_direct(main_handler_thunk);
> 
> entry main_handler;

> cor-out +eval -print
> main_handler = [0 [1 []]
>                [2
>                [87 104 97 116 39 115 32 121 111
>                117 114 32 108 97 115 116 32 110
>                97 109 101 63] [1 [0]]]]
>              > Done (Ok {})
>                  (Stdout "What's your last name?"
>                     (Stdin (EntryPoint )))