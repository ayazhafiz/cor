open Ir
module S = Syntax

type fresh_rec_id = unit -> rec_id
type fresh_name = string -> var_name
type fresh_fn_name = string -> function_name
type layout_cache = (S.variable * layout) list ref

type ctx = {
  cache : layout_cache;
  fresh_rec_id : fresh_rec_id;
  fresh_name : fresh_name;
  fresh_fn_name : fresh_fn_name;
}

let new_ctx () =
  let fresh_name_raw = Util.fresh_name_generator () in
  let fresh_name : fresh_name =
   fun hint ->
    let name = fresh_name_raw hint in
    `Var name
  in
  let fresh_fn_name : fresh_fn_name =
   fun hint ->
    let name = fresh_name_raw hint in
    `Fn name
  in
  let cache = ref [] in
  let next_id = ref 0 in
  let fresh_rec_id () =
    let id = !next_id in
    next_id := id + 1;
    `Rec id
  in
  { cache; fresh_rec_id; fresh_name; fresh_fn_name }

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

type venv = (string * var_name) list [@@deriving show]

module VarMap = struct
  include Map.Make (struct
    type t = string

    let compare = compare
  end)

  let union u v =
    let f _ x _ = Some x in
    union f u v
end

let rec free : S.e_expr -> S.tvar VarMap.t =
 fun (_, t, e) ->
  match e with
  | S.Var x -> VarMap.singleton x t
  | S.Tag (_, es) ->
      List.fold_left (fun acc e -> VarMap.union (free e) acc) VarMap.empty es
  | S.Let ((_, _, x), e, b) ->
      let free_e = free e in
      let free_b = free b in
      let free_b = VarMap.remove x free_b in
      VarMap.union free_e free_b
  | S.Clos ((_, _, a), b) -> VarMap.remove a (free b)
  | S.Call (e1, e2) ->
      let free_e1 = free e1 in
      let free_e2 = free e2 in
      VarMap.union free_e1 free_e2

type pending_closure = {
  proc_name : function_name;
  arg : string * var;
  captures : var * (string * var) list;
  body : S.e_expr;
}

type pending_thunk = {
  introduced : string * var_name;
  proc_name : function_name;
  body : S.e_expr;
}

type pending_proc =
  [ `Closure of pending_closure
  | `Thunk of pending_thunk
  | `Ready of definition ]

let stmt_of_expr :
    ctx -> venv -> S.e_expr -> (stmt list * var) * pending_proc list =
 fun ctx venv expr ->
  let pending_procs : pending_proc list ref = ref [] in
  let rec go_var venv e =
    let asgns, (lay, expr) = go venv e in
    match expr with
    | Var var -> (asgns, var)
    | _ ->
        let var = (lay, ctx.fresh_name "var") in
        let asgns = asgns @ [ Let (var, expr) ] in
        (asgns, var)
  and go ?(name_hint = None) venv (_, ty, e) =
    let layout = layout_of_tvar ctx ty in
    match e with
    | S.Var s ->
        let var =
          match List.assoc_opt s venv with
          | Some var -> var
          | None -> raise @@ Not_found
        in
        ([], (layout, Var (layout, var)))
    | S.Tag (ctor, args) ->
        let id = tag_id ctor ty in
        let arg_asgns, arg_vars = List.split @@ List.map (go_var venv) args in
        let arg_asgns = List.concat arg_asgns in
        let tag_asgns, expr =
          match !layout with
          | Union struct_layouts ->
              let struct_layout = List.nth struct_layouts id in
              let make_struct = MakeStruct arg_vars in
              let struct_var = (struct_layout, ctx.fresh_name "struct") in
              ([ Let (struct_var, make_struct) ], MakeUnion (id, struct_var))
          | _ -> failwith "impossible"
        in
        (arg_asgns @ tag_asgns, (layout, expr))
    | S.Let ((_, (_, x_ty), x), e, b) ->
        let x_layout = layout_of_tvar ctx x_ty in
        let x_name = ctx.fresh_name x in
        let x_var = (x_layout, x_name) in
        let e_asgns, (_, e_expr) = go ~name_hint:(Some x) venv e in
        let b_venv = (x, x_name) :: venv in
        let b_asgns, b_expr = go b_venv b in
        let asgns = e_asgns @ [ Let (x_var, e_expr) ] @ b_asgns in
        (asgns, b_expr)
    | S.Call (f, a) ->
        let clos_asgns, clos_var = go_var venv f in
        (* *)
        let fn_name = ctx.fresh_name "fnptr" in
        let fn_var = (ref @@ FunctionPointer, fn_name) in
        let fn_asgn = Let (fn_var, GetStructField (clos_var, 0)) in
        (* *)
        let captures_name = ctx.fresh_name "captures" in
        let captures_var = (erased_captures_lay, captures_name) in
        let captures_asgn = Let (captures_var, GetStructField (clos_var, 1)) in
        (* *)
        let a_asgns, a_var = go_var venv a in
        let asgns = clos_asgns @ [ fn_asgn; captures_asgn ] @ a_asgns in
        (asgns, (layout, CallIndirect (fn_var, [ captures_var; a_var ])))
    | S.Clos ((_, (_, a_ty), a), e) ->
        let a_layout = layout_of_tvar ctx a_ty in
        let a_name = ctx.fresh_name a in
        let a_var = (a_layout, a_name) in
        let free_in_e : S.tvar VarMap.t = free e in
        let free : (string * var) list =
          List.map (fun (v, t) ->
              (v, (layout_of_tvar ctx t, List.assoc v venv)))
          @@ VarMap.bindings @@ VarMap.remove a free_in_e
        in
        let proc_name =
          ctx.fresh_fn_name @@ Option.value ~default:"clos" name_hint
        in
        (* put the captures in a record *)
        let stack_captures_name =
          ctx.fresh_name @@ "captures_stack_"
          ^ Option.value ~default:"" name_hint
        in
        let captures_layouts = List.map fst @@ List.map snd free in
        let stack_captures_lay = ref @@ Struct captures_layouts in
        let stack_captures_var = (stack_captures_lay, stack_captures_name) in
        let stack_captures_asgn =
          Let (stack_captures_var, MakeStruct (List.map snd free))
        in
        (* box the captures *)
        let box_captures_name =
          ctx.fresh_name @@ "captures_box_" ^ Option.value ~default:"" name_hint
        in
        let box_captures_var =
          (ref @@ Box (stack_captures_lay, None), box_captures_name)
        in
        let box_captures_asgn =
          Let (box_captures_var, MakeBox stack_captures_var)
        in
        (* erase the boxed captures *)
        let captures_name =
          ctx.fresh_name @@ "captures_" ^ Option.value ~default:"" name_hint
        in
        let captures_var = (erased_captures_lay, captures_name) in
        let captures_asgn =
          Let (captures_var, PtrCast (box_captures_var, erased_captures_lay))
        in

        pending_procs :=
          `Closure
            {
              proc_name;
              arg = (a, a_var);
              captures = (captures_var, free);
              body = e;
            }
          :: !pending_procs;

        let fn_ptr_name =
          ctx.fresh_name @@ "fn_ptr_" ^ Option.value ~default:"" name_hint
        in
        let fn_ptr_var = (ref @@ FunctionPointer, fn_ptr_name) in
        let fn_ptr_asgn = Let (fn_ptr_var, MakeFnPtr proc_name) in
        ( [ stack_captures_asgn; box_captures_asgn; captures_asgn; fn_ptr_asgn ],
          (ref closure_repr, MakeStruct [ fn_ptr_var; captures_var ]) )
  in
  let result = go_var venv expr in
  (result, List.rev !pending_procs)

let ret_var : ctx -> layout -> expr -> stmt list * var =
 fun ctx layout expr ->
  match expr with
  | Var x -> ([], x)
  | e ->
      let var_name = ctx.fresh_name "ret" in
      let var = (layout, var_name) in
      ([ Let (var, e) ], var)

let compile_pending_procs : ctx -> pending_proc list -> definition list =
 fun ctx pending_procs ->
  let rec go venv = function
    | [] -> []
    | `Ready def :: pending_procs -> def :: go venv pending_procs
    | `Thunk { introduced; proc_name = name; body } :: pending_procs ->
        let (asgns, ret), new_pending_procs = stmt_of_expr ctx venv body in
        let thunk = Proc { name; args = []; body = asgns; ret } in
        let compiled = go venv @@ new_pending_procs @ [ `Ready thunk ] in
        compiled @ go (introduced :: venv) pending_procs
    | `Closure
        {
          proc_name = name;
          arg = arg_og, arg;
          captures = capture_arg, captures;
          body;
        }
      :: pending_procs ->
        let captures_og_names = List.map fst captures in
        let captures_vars = List.map snd captures in
        let stack_captures_lay = ref @@ Struct (List.map fst captures_vars) in
        (* cast the erased captures to the real type *)
        let boxed_captures_name = ctx.fresh_name @@ "captures_box" in
        let boxed_captures_lay = ref @@ Box (stack_captures_lay, None) in
        let boxed_captures_var = (boxed_captures_lay, boxed_captures_name) in
        let boxed_captures_asgn =
          Let (boxed_captures_var, PtrCast (capture_arg, boxed_captures_lay))
        in

        (* unbox the captures *)
        let stack_captures_name = ctx.fresh_name @@ "captures_stack" in
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

        let captures_venv : venv =
          List.rev
          @@ List.combine captures_og_names (List.map snd captures_vars)
        in

        let venv : venv = [ (arg_og, snd arg) ] @ captures_venv @ venv in
        let (asgns, ret), new_pending_procs = stmt_of_expr ctx venv body in
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
        go venv @@ new_pending_procs @ (`Ready def :: pending_procs)
  in
  go [] pending_procs

let compile_defs : ctx -> S.e_def list -> program =
 fun ctx defs ->
  let pending_procs : pending_proc list ref = ref [] in
  let entry_points : var_name list ref = ref [] in
  let rec go = function
    | [] -> ()
    | (_, _, S.TyAlias _) :: defs -> go defs
    | (_, _, S.Sig _) :: defs -> go defs
    | (_, t, ((S.Def ((_, x), e) | S.Run ((_, x), e)) as def)) :: defs ->
        let thunk_name = ctx.fresh_fn_name (x ^ "_thunk") in
        let x_name = ctx.fresh_name x in
        let x_lay = layout_of_tvar ctx t in
        let init = CallDirect (thunk_name, []) in
        let pending_thunk =
          { introduced = (x, x_name); proc_name = thunk_name; body = e }
        in
        pending_procs := `Thunk pending_thunk :: !pending_procs;
        pending_procs :=
          `Ready (Global { name = x_name; layout = x_lay; init })
          :: !pending_procs;
        (match def with
        | S.Run _ -> entry_points := x_name :: !entry_points
        | _ -> ());
        go defs
  in
  go defs;
  let definitions = compile_pending_procs ctx @@ List.rev !pending_procs in
  let entry_points = List.rev !entry_points in
  { definitions; entry_points }

let compile : S.program -> program =
 fun defs ->
  let ctx = new_ctx () in
  compile_defs ctx defs
