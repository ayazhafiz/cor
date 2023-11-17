open Ir
module S = Syntax

type fresh_rec_id = unit -> rec_id
type fresh_name = string option -> var_name
type fresh_fn_name = string option -> function_name
type layout_cache = (S.variable * layout) list ref

type ctx = {
  cache : layout_cache;
  fresh_rec_id : fresh_rec_id;
  fresh_name : fresh_name;
  fresh_fn_name : fresh_fn_name;
}

let closure_repr = Struct [ ref @@ FunctionPointer; ref @@ Erased ]

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

type venv = (string * var_name) list

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
  closure_name : function_name;
  arg : var;
  captures_name : var_name;
  captures : var list;
  body : S.e_expr;
}

let mkname prefix name =
  match prefix with "" -> name | _ -> prefix ^ "_" ^ name

let stmt_of_expr : ctx -> venv -> S.e_expr -> stmt list * var =
 fun ctx venv expr ->
  let pending_closures : pending_closure list ref = ref [] in
  let rec go_var venv e =
    let asgns, (lay, expr) = go venv e in
    match expr with
    | Var var -> (asgns, var)
    | _ ->
        let var = (lay, ctx.fresh_name None) in
        let asgns = asgns @ [ Let (var, expr) ] in
        (asgns, var)
  and go ?(name_hint = "") venv (_, ty, e) =
    let layout = layout_of_tvar ctx ty in
    match e with
    | S.Var s ->
        let var = List.assoc s venv in
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
              let struct_var = (struct_layout, ctx.fresh_name None) in
              ([ Let (struct_var, make_struct) ], MakeUnion (id, struct_var))
          | _ -> failwith "impossible"
        in
        (arg_asgns @ tag_asgns, (layout, expr))
    | S.Let ((_, (_, x_ty), x), e, b) ->
        let x_layout = layout_of_tvar ctx x_ty in
        let x_name = ctx.fresh_name @@ Some x in
        let x_var = (x_layout, x_name) in
        let e_asgns, (_, e_expr) = go ~name_hint:x venv e in
        let b_venv = (x, x_name) :: venv in
        let b_asgns, b_expr = go b_venv b in
        let asgns = e_asgns @ [ Let (x_var, e_expr) ] @ b_asgns in
        (asgns, b_expr)
    | S.Call (f, a) ->
        let f_asgns, f_expr = go_var venv f in
        let a_asgns, a_expr = go_var venv a in
        let asgns = f_asgns @ a_asgns in
        (asgns, (layout, CallIndirect (f_expr, a_expr)))
    | S.Clos ((_, (_, a_ty), a), e) ->
        let a_layout = layout_of_tvar ctx a_ty in
        let a_name = ctx.fresh_name @@ Some a in
        let a_var = (a_layout, a_name) in
        let free_in_e : S.tvar VarMap.t = free e in
        let free : var list =
          List.map (fun (v, t) -> (layout_of_tvar ctx t, List.assoc v venv))
          @@ VarMap.bindings @@ VarMap.remove a free_in_e
        in
        let closure_name =
          ctx.fresh_fn_name @@ Some (mkname name_hint "clos")
        in
        let stack_captures_name =
          ctx.fresh_name @@ Some (mkname name_hint "captures_stack")
        in
        let stack_captures_lay = ref @@ Erased in
        let stack_captures_var = (stack_captures_lay, stack_captures_name) in
        let stack_captures_asgn = Let (stack_captures_var, MakeStruct free) in
        let box_captures_name =
          ctx.fresh_name @@ Some (mkname name_hint "captures")
        in
        let box_captures_lay = ref @@ Box (stack_captures_lay, None) in
        let box_captures_var = (box_captures_lay, box_captures_name) in
        let box_captures_asgn =
          Let (box_captures_var, MakeBox stack_captures_var)
        in

        pending_closures :=
          {
            closure_name;
            arg = a_var;
            captures_name = box_captures_name;
            captures = free;
            body = e;
          }
          :: !pending_closures;

        let closure = MakeErased (closure_name, box_captures_var) in
        ([ stack_captures_asgn; box_captures_asgn ], (ref closure_repr, closure))
  in
  go_var venv expr
