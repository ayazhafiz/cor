module S = Syntax
open Ir

let rec convert_decision_tree ctx result_ty =
  let open Decision_tree in
  let rec go = function
    | Unreachable -> failwith "todo"
    | Immediate body -> stmt_of_expr ctx body
    | Switch (cond, cases) ->
        let tag_id = (Int, ctx.fresh_var ()) in
        let get_tag_id = Let (tag_id, GetTagId cond) in
        let result_layout = layout_of_type result_ty in
        let join_var : var = (result_layout, ctx.fresh_var ()) in
        let branches =
          List.map
            (function
              | Case (Tag (_, index), vars, decision) ->
                  let vars_asgns =
                    List.mapi
                      (fun i var -> Let (var, GetStructField (i, cond)))
                      vars
                  in
                  let asgns, var = go decision in
                  (index, (vars_asgns @ asgns, var)))
            cases
        in
        let switch_stmt =
          Ir.Switch { cond = tag_id; branches; join = join_var }
        in
        ([ get_tag_id; switch_stmt ], join_var)
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
          | Void -> failwith "todo"
          | Int -> failwith "tag cannot have int layout"
          | Struct _ -> ([], BuildStruct arg_vars)
          | Union struct_layouts ->
              let struct_layout = Struct (List.nth struct_layouts id) in
              let build_struct = BuildStruct arg_vars in
              let struct_var = (struct_layout, ctx.fresh_var ()) in
              ( [ Let (struct_var, build_struct) ],
                BuildTag (layout, id, struct_var) )
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
    | S.When (cond, branches) ->
        let cond_asgn, cond_var = help cond in
        let decision_tree =
          Decision_tree.compile_branches ctx cond_var branches
        in
        let branches_asgns, branches_var =
          convert_decision_tree ctx ty decision_tree
        in
        (cond_asgn @ branches_asgns, branches_var)
  in
  help expr

let ir_of_expr ctx expr =
  let stmts, var = stmt_of_expr ctx expr in
  Program (stmts, var)
