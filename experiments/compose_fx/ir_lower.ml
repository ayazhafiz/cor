open Ir
open Ir_layout
open Symbol

type pending_closure = {
  proc_name : symbol;
  arg : var;
  captures : var * var list;
  body : Can.e_expr;
  (* Some (symbol) if this is a recursive closure bound to the symbol. *)
  rec_var : var option;
}

type pending_thunk = { proc_name : symbol; body : Can.e_expr }

type pending_proc =
  [ `Closure of pending_closure
  | `Thunk of pending_thunk
  | `Ready of definition ]

let get_pat_arg_var : ctx -> Can.e_pat -> var =
 fun ctx pat ->
  match pat with
  | t, PVar v ->
      let layout = layout_of_tvar ctx t in
      (layout, v)
  | _ -> failwith "non-var pattern not yet supported"

let unpack_possibly_boxed ~ctx ~unpack_unboxed ~var =
  let go (l_x, x) =
    match !l_x with
    | Box (inner, _) ->
        let inner_var = (inner, ctx.symbols.fresh_symbol "inner") in
        let asgns, (l_inner, inner) = unpack_unboxed inner_var in
        let asgns = asgns @ [ Let (inner_var, GetBoxed var) ] in
        (asgns, (l_inner, inner))
    | _ -> unpack_unboxed (l_x, x)
  in
  go var

let unpack_boxed_union : ctx -> var -> stmt list * var =
 fun ctx tag ->
  let unpack_unboxed (l_x, x) =
    match !l_x with
    | Union _ -> ([], (l_x, x))
    | _ -> failwith "non-union layout for union"
  in
  unpack_possibly_boxed ~ctx ~unpack_unboxed ~var:tag

let unpack_boxed_struct : ctx -> var -> stmt list * var =
 fun ctx tag ->
  let unpack_unboxed (l_x, x) =
    match !l_x with
    | Struct _ -> ([], (l_x, x))
    | _ -> failwith "non-struct layout for struct"
  in
  unpack_possibly_boxed ~ctx ~unpack_unboxed ~var:tag

let build_possibly_boxed ~ctx ~build_unboxed ~layout =
  let go layout =
    match !layout with
    | Box (inner, _) ->
        let inner_asgns, inner_expr = build_unboxed inner in
        let unboxed_var = (inner, ctx.symbols.fresh_symbol "unboxed") in
        let asgns = inner_asgns @ [ Let (unboxed_var, inner_expr) ] in
        (asgns, MakeBox unboxed_var)
    | _ -> build_unboxed layout
  in
  go layout

let build_possibly_boxed_struct ~ctx ~arg_vars ~layout =
  let build_unboxed l =
    match !l with
    | Struct _ ->
        let asgns = [] in
        (asgns, MakeStruct arg_vars)
    | _ ->
        failwith
          ("non-struct layout for struct: "
          ^ Format.asprintf "%a" pp_layout_top l)
  in
  build_possibly_boxed ~ctx ~build_unboxed ~layout

let build_possibly_boxed_union ~ctx ~arg_vars ~union_id ~layout =
  let build_unboxed l =
    match !l with
    | Union struct_layouts ->
        let struct_layout = List.nth struct_layouts union_id in
        let struct_expr = MakeStruct arg_vars in
        let struct_var = (struct_layout, ctx.symbols.fresh_symbol "struct") in
        let asgns = [ Let (struct_var, struct_expr) ] in
        (asgns, MakeUnion (union_id, struct_var))
    | _ -> failwith "non-union layout for union"
  in
  build_possibly_boxed ~ctx ~build_unboxed ~layout

let vars_of_captures ~ctx captures =
  List.map (fun (t, v) -> (layout_of_tvar ctx t, v)) captures

let build_closure ~ctx ~captures ~proc_name ~layout : stmt list * expr =
  (* put the captures in a record *)
  let stack_captures_name = ctx.symbols.fresh_symbol @@ "captures_stack_" in
  let captures_layouts = List.map fst @@ captures in
  let stack_captures_lay = ref @@ Struct captures_layouts in
  let stack_captures_var = (stack_captures_lay, stack_captures_name) in
  let stack_captures_asgn = Let (stack_captures_var, MakeStruct captures) in
  (* box the captures *)
  let box_captures_name = ctx.symbols.fresh_symbol @@ "captures_box_" in
  let box_captures_var =
    (ref @@ Box (stack_captures_lay, None), box_captures_name)
  in
  let box_captures_asgn = Let (box_captures_var, MakeBox stack_captures_var) in
  (* erase the boxed captures *)
  let captures_name = ctx.symbols.fresh_symbol @@ "captures_" in
  let captures_var = (erased_captures_lay, captures_name) in
  let captures_asgn =
    Let (captures_var, PtrCast (box_captures_var, erased_captures_lay))
  in

  let fn_ptr_name = ctx.symbols.fresh_symbol @@ "fn_ptr_" in
  let fn_ptr_var = (ref @@ FunctionPointer, fn_ptr_name) in
  let fn_ptr_asgn = Let (fn_ptr_var, MakeFnPtr proc_name) in

  let closure_struct_asgns, closure_struct =
    build_possibly_boxed_struct ~ctx
      ~arg_vars:[ fn_ptr_var; captures_var ]
      ~layout
  in

  let asgns =
    [ stack_captures_asgn; box_captures_asgn; captures_asgn; fn_ptr_asgn ]
    @ closure_struct_asgns
  in

  (asgns, closure_struct)

let compile_closure ~ctx ~arg:(t_a, a) ~body ~captures ~proc_name ~rec_var =
  let a_layout = layout_of_tvar ctx t_a in
  let a_var = (a_layout, a) in
  let syn_name =
    match rec_var with Some (_, x) -> Symbol.syn_of ctx.symbols x | None -> ""
  in
  let captures_name = ctx.symbols.fresh_symbol @@ "captures_" ^ syn_name in
  let captures_var = (erased_captures_lay, captures_name) in

  let pending_clos =
    `Closure
      {
        proc_name;
        arg = a_var;
        captures = (captures_var, captures);
        body;
        rec_var;
      }
  in

  pending_clos

let stmt_of_expr : ctx -> Can.e_expr -> (stmt list * var) * pending_proc list =
 fun ctx expr ->
  let pending_procs : pending_proc list ref = ref [] in
  let rec go_var e =
    let asgns, (lay, expr) = go e in
    match expr with
    | Var var -> (asgns, var)
    | _ ->
        let var = (lay, ctx.symbols.fresh_symbol "var") in
        let asgns = asgns @ [ Let (var, expr) ] in
        (asgns, var)
  and compile_branch : var -> Can.branch -> int * (stmt list * expr) =
   fun tag_var (pat, body) ->
    match pat with
    | p_ty, PTag (tag, args) ->
        let tag_id = tag_id tag p_ty in
        let arg_vars = List.map (get_pat_arg_var ctx) args in
        let payload_layout = ref @@ Struct (List.map fst arg_vars) in
        let tag_payload_var =
          (payload_layout, ctx.symbols.fresh_symbol "payload")
        in
        let tag_payload_asgn = Let (tag_payload_var, GetUnionStruct tag_var) in
        let arg_destructs =
          List.mapi
            (fun i var -> Let (var, GetStructField (tag_payload_var, i)))
            arg_vars
        in
        let body_asgns, (_, body_expr) = go body in
        let asgns = [ tag_payload_asgn ] @ arg_destructs @ body_asgns in
        (tag_id, (asgns, body_expr))
    | _ -> failwith "non-tag pattern not yet supported"
  and go (ty, e) =
    let layout = layout_of_tvar ctx ty in
    match e with
    | Str s -> ([], (layout, Lit (`String s)))
    | Int i -> ([], (layout, Lit (`Int i)))
    | Unit -> ([], (layout, MakeStruct []))
    | Var s -> ([], (layout, Var (layout, s)))
    | Tag (ctor, args) ->
        let id = tag_id ctor ty in
        let arg_asgns, arg_vars = List.split @@ List.map go_var args in
        let arg_asgns = List.concat arg_asgns in
        let union_asngs, expr =
          build_possibly_boxed_union ~ctx ~arg_vars ~union_id:id ~layout
        in
        (arg_asgns @ union_asngs, (layout, expr))
    | Let (Letval { bind = t_x, x; body; sig_ = _ }, rest) ->
        let x_layout = layout_of_tvar ctx t_x in
        let x_var = (x_layout, x) in
        let b_asgns, (_, b_expr) = go body in
        let r_asgns, r_expr = go rest in
        let asgns = b_asgns @ [ Let (x_var, b_expr) ] @ r_asgns in
        (asgns, r_expr)
    | Call (f, a) ->
        let clos_asgns, clos_var = go_var f in
        let unpack_asgns, clos_var = unpack_boxed_struct ctx clos_var in

        let fn_name = ctx.symbols.fresh_symbol "fnptr" in
        let fn_var = (ref @@ FunctionPointer, fn_name) in
        let fn_asgn = Let (fn_var, GetStructField (clos_var, 0)) in

        let captures_name = ctx.symbols.fresh_symbol "captures" in
        let captures_var = (erased_captures_lay, captures_name) in
        let captures_asgn = Let (captures_var, GetStructField (clos_var, 1)) in

        let a_asgns, a_var = go_var a in
        let asgns =
          clos_asgns @ unpack_asgns @ [ fn_asgn; captures_asgn ] @ a_asgns
        in
        (asgns, (layout, CallIndirect (fn_var, [ captures_var; a_var ])))
    | KCall (kfn, args) ->
        let args_asgns, arg_vars = List.split @@ List.map go_var args in
        let asgns = List.concat args_asgns in
        (asgns, (layout, CallKFn (kfn, arg_vars)))
    | LetFn (Letfn { bind; lam_sym; captures; _ }, rest) ->
        let t_x, x = bind in
        let layout_x = layout_of_tvar ctx t_x in
        let captures = vars_of_captures ~ctx captures in
        let clos_asngs, clos_expr =
          build_closure ~ctx ~captures ~proc_name:lam_sym ~layout:layout_x
        in
        let x_var = (layout_x, x) in
        let x_asgn = Let (x_var, clos_expr) in
        let e_asgns, e_expr = go rest in
        let asgns = clos_asngs @ [ x_asgn ] @ e_asgns in
        (asgns, e_expr)
    | Clos { lam_sym; captures; _ } ->
        let captures = vars_of_captures ~ctx captures in
        let clos_asgns, clos_expr =
          build_closure ~ctx ~captures ~proc_name:lam_sym ~layout
        in
        (clos_asgns, (layout, clos_expr))
    | When (tag_e, branches) ->
        let tag_asgns, tag_var = go_var tag_e in
        let unpack_asgns, tag_var = unpack_boxed_union ctx tag_var in
        let discr_var = (ref @@ Int, ctx.symbols.fresh_symbol "discr") in
        let discr_asgn = Let (discr_var, GetUnionId tag_var) in
        let branches =
          List.sort (fun (tag_id1, _) (tag_id2, _) -> tag_id1 - tag_id2)
          @@ List.map (compile_branch tag_var) branches
        in
        let join = (layout, ctx.symbols.fresh_symbol "join") in
        let switch = Switch { cond = discr_var; branches; join } in
        let asgns = tag_asgns @ unpack_asgns @ [ discr_asgn ] @ [ switch ] in
        (asgns, (layout, Var join))
  in
  let result = go_var expr in
  (result, List.rev !pending_procs)

let ret_var : ctx -> layout -> expr -> stmt list * var =
 fun ctx layout expr ->
  match expr with
  | Var x -> ([], x)
  | e ->
      let var_name = ctx.symbols.fresh_symbol "ret" in
      let var = (layout, var_name) in
      ([ Let (var, e) ], var)

let compile_pending_procs : ctx -> pending_proc list -> definition list =
 fun ctx pending_procs ->
  let rec go = function
    | [] -> []
    | `Ready def :: pending_procs -> def :: go pending_procs
    | `Thunk { proc_name = name; body } :: pending_procs ->
        let (asgns, ret), new_pending_procs = stmt_of_expr ctx body in
        let thunk = Proc { name; args = []; body = asgns; ret } in
        let compiled = go @@ new_pending_procs @ [ `Ready thunk ] in
        compiled @ go pending_procs
    | `Closure
        {
          proc_name = name;
          arg;
          captures = capture_arg, captures_vars;
          body;
          rec_var;
        }
      :: pending_procs ->
        let stack_captures_lay = ref @@ Struct (List.map fst captures_vars) in
        (* cast the erased captures to the real type *)
        let boxed_captures_name = ctx.symbols.fresh_symbol @@ "captures_box" in
        let boxed_captures_lay = ref @@ Box (stack_captures_lay, None) in
        let boxed_captures_var = (boxed_captures_lay, boxed_captures_name) in
        let boxed_captures_asgn =
          Let (boxed_captures_var, PtrCast (capture_arg, boxed_captures_lay))
        in

        (* unbox the captures *)
        let stack_captures_name =
          ctx.symbols.fresh_symbol @@ "captures_stack"
        in
        let stack_captures_var = (stack_captures_lay, stack_captures_name) in
        let stack_captures_asgn =
          Let (stack_captures_var, GetBoxed boxed_captures_var)
        in

        (* unpack the captures *)
        let unpack_asgns =
          List.mapi
            (fun i var -> Let (var, GetStructField (stack_captures_var, i)))
            captures_vars
        in

        (* if this is a recursive closure, we must bind the name to the cell now as well.*)
        let rec_asgns =
          match rec_var with
          | None -> []
          | Some (rec_layout, rec_var) ->
              let fn_ptr_name =
                ctx.symbols.fresh_symbol @@ "rec_fn_ptr_"
                ^ Symbol.syn_of ctx.symbols rec_var
              in
              let fn_ptr_var = (ref @@ FunctionPointer, fn_ptr_name) in
              let fn_ptr_asgn = Let (fn_ptr_var, MakeFnPtr name) in
              let rec_clos_var = (rec_layout, rec_var) in
              let asgns, rec_clos_struct =
                build_possibly_boxed_struct ~ctx
                  ~arg_vars:[ fn_ptr_var; capture_arg ]
                  ~layout:rec_layout
              in
              let rec_clos_asgn = Let (rec_clos_var, rec_clos_struct) in
              (fn_ptr_asgn :: asgns) @ [ rec_clos_asgn ]
        in

        let (asgns, ret), new_pending_procs = stmt_of_expr ctx body in
        let def =
          Proc
            {
              name;
              args = [ capture_arg; arg ];
              body =
                [ boxed_captures_asgn; stack_captures_asgn ]
                @ unpack_asgns @ rec_asgns @ asgns;
              ret;
            }
        in
        go @@ new_pending_procs @ (`Ready def :: pending_procs)
  in
  go pending_procs

let compile_defs : ctx -> Mono.ready_specialization list -> definition list =
 fun ctx specs ->
  let rec go : Mono.ready_specialization list -> pending_proc list = function
    | [] -> []
    | `Letval (Letval { bind = t_x, x; body; sig_ = _ }) :: defs ->
        let thunk_name =
          ctx.symbols.fresh_symbol (Symbol.syn_of ctx.symbols x ^ "_thunk")
        in
        let x_lay = layout_of_tvar ctx t_x in
        let init = CallDirect (thunk_name, []) in
        let pending_thunk = { proc_name = thunk_name; body } in
        let global = Global { name = x; layout = x_lay; init } in
        `Thunk pending_thunk :: `Ready global :: go defs
    | `Letfn
        ( Letfn
            { recursive; bind = t_x, x; arg; body; lam_sym; captures; sig_ = _ },
          true )
      :: defs ->
        let layout_x = layout_of_tvar ctx t_x in
        let rec_var = if recursive then Some (layout_x, x) else None in
        let syn_name = Symbol.norm_of lam_sym in
        let proc_name = ctx.symbols.fresh_symbol @@ "clos_" ^ syn_name in
        let captures = vars_of_captures ~ctx captures in
        let pending_clos =
          compile_closure ~ctx ~rec_var ~arg ~body ~captures ~proc_name
        in

        let closure_struct_asgns, closure_struct =
          build_closure ~ctx ~captures ~proc_name ~layout:layout_x
        in

        let thunk_name = ctx.symbols.fresh_symbol @@ syn_name ^ "_thunk" in
        let thunk =
          let closure_struct_name =
            ctx.symbols.fresh_symbol @@ syn_name ^ "_closure"
          in
          let ret = (layout_x, closure_struct_name) in
          let args = [] in
          let body = closure_struct_asgns @ [ Let (ret, closure_struct) ] in
          Proc { name = thunk_name; args; body; ret }
        in

        let global =
          Global
            { name = x; layout = layout_x; init = CallDirect (thunk_name, []) }
        in

        pending_clos :: `Ready thunk :: `Ready global :: go defs
    | `Letfn
        ( Letfn
            { recursive; bind = t_x, x; arg; body; lam_sym; captures; sig_ = _ },
          false )
      :: defs ->
        let layout_x = layout_of_tvar ctx t_x in
        let rec_var = if recursive then Some (layout_x, x) else None in
        let captures = vars_of_captures ~ctx captures in
        let pending_clos =
          compile_closure ~ctx ~rec_var ~arg ~body ~captures ~proc_name:lam_sym
        in
        pending_clos :: go defs
  in
  let pending_procs = go specs in
  compile_pending_procs ctx @@ pending_procs

let compile ~ctx ({ specializations; entry_points } : Mono.specialized) =
  let definitions = compile_defs ctx specializations in
  { definitions; entry_points }
