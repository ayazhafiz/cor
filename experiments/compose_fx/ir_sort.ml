open Ir
open Symbol

module G = Graph.Imperative.Digraph.Concrete (struct
  type t = Symbol.symbol

  let compare = compare
  let hash = Hashtbl.hash
  let equal = ( = )
end)

module Topological = Graph.Topological.Make (G)

let build_definition_map : definition list -> (symbol * definition) list =
 fun defs ->
  let map_def = function
    | (Proc { name; _ } | Global { name; _ }) as def -> (name, def)
  in
  List.map map_def defs

let sym_edges ~def_map s = if List.mem_assoc s def_map then [ s ] else []
let var_edges ~def_map (_, s) = sym_edges ~def_map s

let expr_edges ~def_map = function
  | Var v -> var_edges ~def_map v
  | Lit _ -> []
  | MakeUnion (_, v) -> var_edges ~def_map v
  | GetUnionId v -> var_edges ~def_map v
  | GetUnionStruct v -> var_edges ~def_map v
  | MakeStruct vs -> List.concat (List.map (var_edges ~def_map) vs)
  | GetStructField (v, _) -> var_edges ~def_map v
  | CallDirect (s, vs) ->
      sym_edges ~def_map s @ List.concat (List.map (var_edges ~def_map) vs)
  | CallKFn (_, vs) -> List.concat (List.map (var_edges ~def_map) vs)
  | MakeBox v -> var_edges ~def_map v
  | GetBoxed v -> var_edges ~def_map v

let rec stmt_edges ~def_map = function
  | Let (_, e) -> expr_edges ~def_map e
  | Switch { cond; branches; join } ->
      let c_edges = var_edges ~def_map cond in
      let b_edges =
        List.map
          (fun (_, (stmts, e)) ->
            stmts_edges ~def_map stmts @ expr_edges ~def_map e)
          branches
      in
      let b_edges = List.concat b_edges in
      let j_edges = var_edges ~def_map join in
      c_edges @ b_edges @ j_edges

and stmts_edges ~def_map stmts =
  List.concat (List.map (stmt_edges ~def_map) stmts)

let sort_definitions : definition list -> definition list =
 fun definitions ->
  let graph = G.create () in
  let add_node = G.add_vertex graph in
  let add_edge = G.add_edge graph in
  let def_map = build_definition_map definitions in
  List.iter (fun (name, _) -> add_node name) def_map;
  let add_def_edges = function
    | Proc { name; body; ret; _ } ->
        let b_edges = stmts_edges ~def_map body in
        let r_edges = var_edges ~def_map ret in
        List.iter (fun dep -> add_edge dep name) (b_edges @ r_edges)
    | Global { name; init; _ } ->
        let i_edges = expr_edges ~def_map init in
        List.iter (fun dep -> add_edge dep name) i_edges
  in
  List.iter add_def_edges definitions;
  let sorted =
    Topological.fold (fun x acc -> List.assoc x def_map :: acc) graph []
  in
  List.rev sorted

let sort_program : program -> program =
 fun { definitions; entry_points } ->
  let definitions = sort_definitions definitions in
  { definitions; entry_points }
