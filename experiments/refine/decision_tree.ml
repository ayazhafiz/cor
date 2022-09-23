open Ir
module S = Syntax

type index = int [@@deriving show]
type ctor = Tag of layout * index [@@deriving show]

let pp_ctor f =
  let open Format in
  function
  | Tag (lay, i) ->
      fprintf f "Tag(%d, " i;
      Ir.pp_layout f lay;
      fprintf f ")"

let string_of_ctor ctor =
  Util.with_buffer (fun f -> pp_ctor f ctor) Language.default_width

type pat =
  | Ctor of ctor * pat list
      (** a tag pattern - its layout, the tag ID of this particular variant,
      and the patterns of the arguments *)
  | Wild
[@@deriving show]

type column = var * pat [@@deriving show]
(**
   A column in a pattern matching table.
   A column contains a single variable to test, and a pattern to test against
   that variable.
   A row may contain multiple columns as we build the decision tree, though it
   always contains exactly one from the source language (or zero if it's a
   catch-all case).
*)

type row = column list * S.e_expr [@@deriving show]
(** A single row (case) in a when expression. Contains the [columns] to test and
    the body of the case. *)

(** The decision tree. Subtrees are constructed with [case]. *)
type decision =
  | Unreachable
  | Immediate of S.e_expr
  | Switch of var * case list
[@@deriving show]

(** constructor to match against, variables to bind arguments to and introduce, and the body *)
and case = Case of ctor * var list * decision [@@deriving show]

(** Translate a `when` expression, with condition lowered to a variable, to a
    list of [rows]. *)
let rows_of_branches (cond_var : var) (branches : S.branch list) =
  let rec convert_pat (_, ty, pat) =
    match pat with
    | S.PTag ((_, ctor), args) ->
        let index = tag_id ctor ty in
        let layout = layout_of_type ty in
        let arg_pats = List.map convert_pat args in
        Ctor (Tag (layout, index), arg_pats)
    | S.PWild -> Wild
  in

  let pat_to_row cond_var body pat =
    match pat with
    | _, _, S.PTag _ ->
        let column = (cond_var, convert_pat pat) in
        Some ([ column ], body)
    | _, _, S.PWild ->
        (* immediate *)
        Some ([], body)
    (* None *)
  in

  (* translate one branch to zero or more rows *)
  let branch_to_rows cond_var ((_, _, pat), body) =
    match pat with
    | S.PAtom pats -> List.filter_map (pat_to_row cond_var body) pats
    | S.PAs _ -> failwith "todo"
  in

  List.concat_map (branch_to_rows cond_var) branches

let filter_wildcard_columns (rows : row list) =
  let is_wild = function Wild -> true | _ -> false in

  List.map
    (fun (cols, body) ->
      (List.filter (fun (_, pat) -> not (is_wild pat)) cols, body))
    rows

type counts = (var * int) list [@@deriving show]

let choose_branch_var (rows : row list) =
  let cand_var_counts =
    List.hd rows |> fst |> List.map fst |> List.map (fun var -> (var, 0))
  in
  let count_column (var, _) counts =
    match List.assoc_opt var counts with
    | None -> (* var is not a candidate *) counts
    | Some count -> (var, count + 1) :: counts
  in
  let count_row (cols, _) counts = List.fold_right count_column cols counts in
  let final_counts = List.fold_right count_row rows cand_var_counts in
  let rec find_max_count = function
    | None, [] -> failwith "unreachable 91"
    | Some (var, _), [] -> var
    | None, best :: rest -> find_max_count (Some best, rest)
    | Some (var1, count1), (var2, count2) :: rest ->
        let best = if count2 > count1 then (var2, count2) else (var1, count1) in
        find_max_count (Some best, rest)
  in
  find_max_count (None, final_counts)

type ctor_case = [ `CtorCase of ctor * var list * row list ] [@@deriving show]
type rows = row list [@@deriving show]
type cases = (int * ctor_case) list [@@deriving show]
type ctor_cases = ctor_case list [@@deriving show]

let rec compile_ctor_cases ctx (rows : row list) (branch_var : var)
    (cases : (index * ctor_case) list) =
  let remove_col var (cols, body) =
    let col = List.find_opt (fun (v, _) -> v = var) cols in
    let cols' = List.filter (fun (v, _) -> v <> var) cols in
    let row' = (cols', body) in
    (row', col)
  in

  let extend_subrows_of_case row (`CtorCase (ctor, vars, rows)) =
    `CtorCase (ctor, vars, rows @ [ row ])
  in

  let go_row cases row =
    let row, col = remove_col branch_var row in
    match col with
    | Some (_, pat) -> (
        match pat with
        | Wild ->
            (* nothing more to test here, we pass through *)
            cases
        | Ctor (ctor, arg_pats) ->
            let (Tag (_, index)) = ctor in
            (* Take the remaining columns of the row, and attach new columns
               corresponding to testing the arguments of the present constructor.
               This forms a new row we'll test under the body of this matched
               constructor. *)
            let remaining_cols, body = row in
            let (`CtorCase (ctor', vars, sub_rows)) = List.assoc index cases in
            assert (ctor = ctor');
            let partial_cases = List.remove_assoc index cases in
            (* build the new case *)
            let new_ctor_case =
              let new_cols = List.combine vars arg_pats in
              let total_cols_for_subrow = remaining_cols @ new_cols in
              let subrow = (total_cols_for_subrow, body) in
              let new_sub_rows = sub_rows @ [ subrow ] in
              `CtorCase (ctor', vars, new_sub_rows)
            in
            (* update the total cases *)
            let cases' = (index, new_ctor_case) :: partial_cases in
            cases')
    | None ->
        (* This row does not test the given branch variable; copy it into the
           list of rows that will be tested under each constructor case. *)
        let cases' =
          List.map (fun (i, case) -> (i, extend_subrows_of_case row case)) cases
        in
        cases'
  in

  let cases' =
    List.fold_left go_row cases rows
    |> List.sort (fun (i1, _) (i2, _) -> compare i1 i2)
    |> List.map snd
  in
  let built_cases =
    List.map
      (function
        | `CtorCase (ctor, vars, rows) ->
            let sub_rows = compile_rows ctx rows in
            Case (ctor, vars, sub_rows))
      cases'
  in
  built_cases

and compile_rows ctx rows =
  (* Columns that are wildcards are irrelevant in each row, so remove them
     before we proceed. *)
  let rows = filter_wildcard_columns rows in
  match rows with
  | [] -> failwith "empty rows!"
  | ([], body) :: _redundant_rows ->
      (* A branch with no columns always matches, since there is nothing more
         to check - and that also means the rest of the rows, if there are any,
         are redundant. *)
      Immediate body
  | rows -> (
      let branch_var = choose_branch_var rows in
      let branch_var_layout = fst branch_var in
      let new_vars_of_args = List.map (fun lay -> (lay, ctx.fresh_var ())) in
      match branch_var_layout with
      | Void -> Unreachable
      | Int -> failwith "layout of branch var cannot be int"
      | Struct _ ->
          let body = snd @@ List.hd rows in
          Immediate body
      | Union variants ->
          let cases : (index * ctor_case) list =
            List.mapi
              (fun i args ->
                let ctor = Tag (branch_var_layout, i) in
                let vars = new_vars_of_args args in
                let new_rows = [] in
                (i, `CtorCase (ctor, vars, new_rows)))
              variants
          in
          let compiled_cases = compile_ctor_cases ctx rows branch_var cases in

          Switch (branch_var, compiled_cases))

let compile_branches ctx (cond_var : var) (branches : S.branch list) =
  let rows = rows_of_branches cond_var branches in
  compile_rows ctx rows
