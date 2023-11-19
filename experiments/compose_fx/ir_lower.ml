open Ir
open Symbol
module S = Syntax

type fresh_rec_id = unit -> rec_id
type layout_cache = (S.variable * layout) list ref

type ctx = {
  symbols : Symbol.t;
  cache : layout_cache;
  fresh_rec_id : fresh_rec_id;
}

let new_ctx symbols =
  let cache = ref [] in
  let next_id = ref 0 in
  let fresh_rec_id () =
    let id = !next_id in
    next_id := id + 1;
    `Rec id
  in
  { symbols; cache; fresh_rec_id }

let erased_captures_lay = ref @@ Box (ref @@ Erased, None)
let closure_repr = Struct [ ref @@ FunctionPointer; erased_captures_lay ]

let layout_of_tvar : ctx -> S.tvar -> layout =
 fun { cache; fresh_rec_id; _ } tvar ->
  let rec go tvar : layout =
    let tvar = S.unlink_w_alias tvar in
    let var = S.tvar_v tvar in
    match List.assoc_opt var !cache with
    | Some layout -> layout
    | None ->
        let lay = ref @@ Union [] in
        cache := (var, lay) :: !cache;
        let repr =
          match S.tvar_deref tvar with
          | S.Link _ -> failwith "impossible"
          | S.Alias _ -> failwith "impossible"
          | S.Unbd _ -> Union []
          | S.ForA _ -> Union [] (* TODO monomorphize *)
          | S.Content (S.TPrim `Str) -> Str
          | S.Content (S.TPrim `Unit) -> Struct []
          | S.Content S.TTagEmpty -> Union []
          | S.Content (S.TTag { tags; ext = _, ext }) ->
              let tags, _ext = S.chase_tags tags ext in
              let translate_tag : S.ty_tag -> layout =
               fun (_, args) ->
                let struct' = List.map go @@ List.map snd @@ args in
                ref @@ Struct struct'
              in
              let tags = List.map translate_tag tags in
              let union = Union tags in
              union
          | S.Content (S.TFn (_, _)) -> closure_repr
        in
        let recurs = S.tvar_recurs tvar in
        let repr =
          if recurs then Box (ref @@ repr, Some (fresh_rec_id ())) else repr
        in
        lay := repr;
        lay
  in
  go tvar

let tag_id ctor ty =
  match S.tvar_deref @@ S.unlink_w_alias ty with
  | S.Content (S.TTag { tags; ext = _ }) ->
      Util.index_of (fun (name, _) -> name = ctor) tags
  | _ -> failwith "unreachable"

module SymbolMap = struct
  include Map.Make (struct
    type t = Symbol.symbol

    let compare = compare
  end)

  let union u v =
    let f _ x _ = Some x in
    union f u v
end

let rec free : S.e_expr -> S.tvar SymbolMap.t =
 fun (_, t, e) ->
  match e with
  | S.Var x -> SymbolMap.singleton x t
  | S.Tag (_, es) ->
      List.fold_left
        (fun acc e -> SymbolMap.union (free e) acc)
        SymbolMap.empty es
  | S.Let ((_, _, x), e, b) ->
      let free_e = free e in
      let free_b = free b in
      let free_b = SymbolMap.remove x free_b in
      SymbolMap.union free_e free_b
  | S.Clos ((_, _, a), b) -> SymbolMap.remove a (free b)
  | S.Call (e1, e2) ->
      let free_e1 = free e1 in
      let free_e2 = free e2 in
      SymbolMap.union free_e1 free_e2

type pending_closure = {
  proc_name : symbol;
  arg : var;
  captures : var * var list;
  body : S.e_expr;
}

type pending_thunk = { proc_name : symbol; body : S.e_expr }

type pending_proc =
  [ `Closure of pending_closure
  | `Thunk of pending_thunk
  | `Ready of definition ]

let stmt_of_expr : ctx -> S.e_expr -> (stmt list * var) * pending_proc list =
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
  and go ?(name_hint = None) (_, ty, e) =
    let layout = layout_of_tvar ctx ty in
    match e with
    | S.Var s -> ([], (layout, Var (layout, s)))
    | S.Tag (ctor, args) ->
        let id = tag_id ctor ty in
        let arg_asgns, arg_vars = List.split @@ List.map go_var args in
        let arg_asgns = List.concat arg_asgns in
        let rec build_union : layout -> stmt list * expr =
         fun layout ->
          match !layout with
          | Union struct_layouts ->
              let struct_layout = List.nth struct_layouts id in
              let make_struct = MakeStruct arg_vars in
              let struct_var =
                (struct_layout, ctx.symbols.fresh_symbol "struct")
              in
              ([ Let (struct_var, make_struct) ], MakeUnion (id, struct_var))
          | Box (inner, _) ->
              let inner_asgns, inner_expr = build_union inner in
              let union_var = (inner, ctx.symbols.fresh_symbol "union") in
              (inner_asgns @ [ Let (union_var, inner_expr) ], MakeBox union_var)
          | _ -> failwith "impossible: non-union layout"
        in
        let tag_asgns, expr = build_union layout in
        (arg_asgns @ tag_asgns, (layout, expr))
    | S.Let ((_, (_, x_ty), x), e, b) ->
        let x_layout = layout_of_tvar ctx x_ty in
        let x_var = (x_layout, x) in
        let e_asgns, (_, e_expr) =
          go ~name_hint:(Some (Symbol.syn_of ctx.symbols x)) e
        in
        let b_asgns, b_expr = go b in
        let asgns = e_asgns @ [ Let (x_var, e_expr) ] @ b_asgns in
        (asgns, b_expr)
    | S.Call (f, a) ->
        let clos_asgns, clos_var = go_var f in
        (* *)
        let fn_name = ctx.symbols.fresh_symbol "fnptr" in
        let fn_var = (ref @@ FunctionPointer, fn_name) in
        let fn_asgn = Let (fn_var, GetStructField (clos_var, 0)) in
        (* *)
        let captures_name = ctx.symbols.fresh_symbol "captures" in
        let captures_var = (erased_captures_lay, captures_name) in
        let captures_asgn = Let (captures_var, GetStructField (clos_var, 1)) in
        (* *)
        let a_asgns, a_var = go_var a in
        let asgns = clos_asgns @ [ fn_asgn; captures_asgn ] @ a_asgns in
        (asgns, (layout, CallIndirect (fn_var, [ captures_var; a_var ])))
    | S.Clos ((_, (_, a_ty), a), e) ->
        let a_layout = layout_of_tvar ctx a_ty in
        let a_var = (a_layout, a) in
        let free_in_e : S.tvar SymbolMap.t = free e in
        let free : var list =
          List.map (fun (v, t) -> (layout_of_tvar ctx t, v))
          @@ SymbolMap.bindings
          @@ SymbolMap.remove a free_in_e
        in
        let proc_name =
          ctx.symbols.fresh_symbol @@ Option.value ~default:"clos" name_hint
        in
        (* put the captures in a record *)
        let stack_captures_name =
          ctx.symbols.fresh_symbol @@ "captures_stack_"
          ^ Option.value ~default:"" name_hint
        in
        let captures_layouts = List.map fst @@ free in
        let stack_captures_lay = ref @@ Struct captures_layouts in
        let stack_captures_var = (stack_captures_lay, stack_captures_name) in
        let stack_captures_asgn = Let (stack_captures_var, MakeStruct free) in
        (* box the captures *)
        let box_captures_name =
          ctx.symbols.fresh_symbol @@ "captures_box_"
          ^ Option.value ~default:"" name_hint
        in
        let box_captures_var =
          (ref @@ Box (stack_captures_lay, None), box_captures_name)
        in
        let box_captures_asgn =
          Let (box_captures_var, MakeBox stack_captures_var)
        in
        (* erase the boxed captures *)
        let captures_name =
          ctx.symbols.fresh_symbol @@ "captures_"
          ^ Option.value ~default:"" name_hint
        in
        let captures_var = (erased_captures_lay, captures_name) in
        let captures_asgn =
          Let (captures_var, PtrCast (box_captures_var, erased_captures_lay))
        in

        pending_procs :=
          `Closure
            {
              proc_name;
              arg = a_var;
              captures = (captures_var, free);
              body = e;
            }
          :: !pending_procs;

        let fn_ptr_name =
          ctx.symbols.fresh_symbol @@ "fn_ptr_"
          ^ Option.value ~default:"" name_hint
        in
        let fn_ptr_var = (ref @@ FunctionPointer, fn_ptr_name) in
        let fn_ptr_asgn = Let (fn_ptr_var, MakeFnPtr proc_name) in
        ( [ stack_captures_asgn; box_captures_asgn; captures_asgn; fn_ptr_asgn ],
          (ref closure_repr, MakeStruct [ fn_ptr_var; captures_var ]) )
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
        { proc_name = name; arg; captures = capture_arg, captures_vars; body }
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

        let (asgns, ret), new_pending_procs = stmt_of_expr ctx body in
        let def =
          Proc
            {
              name;
              args = [ capture_arg; arg ];
              body =
                [ boxed_captures_asgn; stack_captures_asgn ]
                @ unpack_asgns @ asgns;
              ret;
            }
        in
        go @@ new_pending_procs @ (`Ready def :: pending_procs)
  in
  go pending_procs

let compile_defs :
    ctx -> Monomorphize.ready_specialization list -> definition list =
 fun ctx specs ->
  let pending_procs : pending_proc list ref = ref [] in
  let rec go : Monomorphize.ready_specialization list -> unit = function
    | [] -> ()
    | `Ready (x, e, t) :: defs ->
        let thunk_name =
          ctx.symbols.fresh_symbol (Symbol.syn_of ctx.symbols x ^ "_thunk")
        in
        let x_lay = layout_of_tvar ctx t in
        let init = CallDirect (thunk_name, []) in
        let pending_thunk = { proc_name = thunk_name; body = e } in
        pending_procs := `Thunk pending_thunk :: !pending_procs;
        pending_procs :=
          `Ready (Global { name = x; layout = x_lay; init }) :: !pending_procs;
        go defs
  in
  go specs;
  compile_pending_procs ctx @@ List.rev !pending_procs

let compile : Symbol.t -> Monomorphize.specialized -> program =
 fun symbols ({ specializations; entry_points } : Monomorphize.specialized) ->
  let ctx = new_ctx symbols in
  let definitions = compile_defs ctx specializations in
  { definitions; entry_points }
