module S = Syntax
open Ir

let rec convert_decision_tree ctx result_ty =
  let open Decision_tree in
  let rec go = function
    | Unreachable -> None
    | Immediate body -> Some (stmt_of_expr ctx body)
    | Switch (cond, cases) -> (
        let tag_id = (Int, ctx.fresh_var ()) in
        let get_tag_id = Let (tag_id, GetUnionId cond) in
        let result_layout = layout_of_type result_ty in
        let join_var : var = (result_layout, ctx.fresh_var ()) in
        let branches =
          List.filter_map
            (function
              | Case (Tag (_, index), vars, decision) ->
                  (* Get the union payload, which is a struct. That contains the
                     arguments we need to unwrap. *)
                  let union_struct_layout = Struct (List.map fst vars) in
                  let union_struct = (union_struct_layout, ctx.fresh_var ()) in
                  let union_struct_def =
                    Let (union_struct, GetUnionStruct cond)
                  in
                  let vars_asgns =
                    List.mapi
                      (fun i var -> Let (var, GetStructField (i, union_struct)))
                      vars
                  in
                  go decision
                  |> Option.map (fun (asgns, var) ->
                         (index, ((union_struct_def :: vars_asgns) @ asgns, var))))
            cases
        in
        match branches with
        | [ (_, (stmts, var)) ] -> Some (stmts, var)
        | branches ->
            let switch_stmt =
              Ir.Switch { cond = tag_id; branches; join = join_var }
            in
            Some ([ get_tag_id; switch_stmt ], join_var))
  in
  go

and stmt_of_expr ctx expr : stmt list * var =
  let rec help (_, ty, e) =
    let layout = layout_of_type ty in
    match e with
    | S.Var s ->
        let var = (layout, s) in
        ([], var)
    | S.Tag (ctor, args) ->
        let id = tag_id ctor ty in
        let asgns, arg_vars = List.split @@ List.map help args in
        let asgns = List.concat asgns in
        let build_asgns, expr =
          match layout with
          | Void -> failwith "cannot create tags of void layout"
          | Int -> failwith "tag cannot have int layout"
          | Struct _ -> ([], BuildStruct arg_vars)
          | Union struct_layouts ->
              let struct_layout = Struct (List.nth struct_layouts id) in
              let build_struct = BuildStruct arg_vars in
              let struct_var = (struct_layout, ctx.fresh_var ()) in
              ([ Let (struct_var, build_struct) ], BuildUnion (id, struct_var))
        in
        let var = (layout, ctx.fresh_var ()) in
        (asgns @ build_asgns @ [ Let (var, expr) ], var)
    | S.Let ((_, x_ty, x), def, rest) ->
        let x_layout = layout_of_type x_ty in
        let body_asgns, body_var = help def in
        let rest_asgns, rest_var = help rest in
        let x_var = (x_layout, x) in
        let asgns = body_asgns @ [ Let (x_var, Var body_var) ] @ rest_asgns in
        (asgns, rest_var)
    | S.Match (cond, branches) ->
        let cond_asgn, cond_var = help cond in
        let decision_tree =
          Decision_tree.compile_branches ctx (S.xty cond) cond_var branches
        in
        let branches_asgns, branches_var =
          Option.get @@ convert_decision_tree ctx ty decision_tree
        in
        (cond_asgn @ branches_asgns, branches_var)
  in
  help expr

let ir_of_expr ctx expr =
  let stmts, var = stmt_of_expr ctx expr in
  Program (stmts, var)
