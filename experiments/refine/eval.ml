open Ir
open Util

type memory_cell = Cell of int | Block of memory_cell list [@@deriving show]
type memory = (var * memory_cell) list

let expr memory = function
  | Var x -> List.assoc x memory
  | GetUnionId x -> (
      match List.assoc x memory with
      | Block (Cell id :: _) -> Cell id
      | mem ->
          failwith
            ("bad memory layout " ^ show_memory_cell mem ^ " "
            ^ with_buffer (fun f -> pp_var f x) 80))
  | BuildUnion (id, var) -> (
      match List.assoc var memory with
      | Block mem -> Block (Cell id :: mem)
      | _ -> failwith "bad tag payload memory layout")
  | GetUnionStruct var -> (
      match List.assoc var memory with
      | Block (Cell _ :: struct') -> Block struct'
      | _ -> failwith "bad tag payload memory layout")
  | BuildStruct vars -> Block (List.map (fun v -> List.assoc v memory) vars)
  | GetStructField (i, x) -> (
      match List.assoc x memory with
      | Block block -> List.nth block i
      | _ -> failwith "bad struct memory layout")

let rec stmt memory = function
  | Let (x, e) ->
      let data = expr memory e in
      (x, data) :: memory
  | Switch { cond; branches; join } ->
      let discr =
        match List.assoc cond memory with
        | Cell n -> n
        | _ -> failwith "bad discriminant memory layout"
      in
      let stmts, var = List.assoc discr branches in
      let memory' = List.fold_left stmt memory stmts in
      stmt memory' (Let (join, Var var))

let eval = function
  | Program (stmts, var) ->
      let memory = [] in
      let memory' = List.fold_left stmt memory stmts in
      (var, memory')

(* readback *)

module S = Syntax

let pp_bot f = Format.fprintf f "⊥"

let rec readback f ty layout data =
  let open Format in
  match !(S.unlink ty) with
  | S.Content (S.TTag tags) -> (
      match layout with
      | Void -> pp_bot f
      | Int -> (
          match data with
          | Cell i -> fprintf f "%d" i
          | _ -> failwith "illegal memory for int")
      | Struct layouts -> (
          match (tags, data) with
          | _, Block [] -> ()
          | [ ("#struct", payload_types) ], Block cells ->
              if List.length cells > 1 then fprintf f "{ ";
              intersperse f ", "
                (fun f _ (ty, (lay, data)) -> readback f ty lay data)
                (List.combine payload_types @@ List.combine layouts cells);
              if List.length cells > 1 then fprintf f "{ "
          | _ -> failwith "illegal memory for int")
      | Union union -> (
          match data with
          | Block (id_cell :: rest) ->
              let id =
                match id_cell with
                | Cell i -> i
                | _ -> failwith "illegal memory for tag id"
              in
              let tag, payload_types = List.nth tags id in
              let payload_layouts = List.nth union id in
              fprintf f "%s" tag;
              if List.length payload_layouts > 0 then fprintf f " ";
              readback f
                (ref @@ S.Content (S.TTag [ ("#struct", payload_types) ]))
                (Struct payload_layouts) (Block rest)
          | _ -> failwith "illegal type/memory for union"))
  | S.Unbd _ -> pp_bot f
  | S.Link _ -> failwith "unreachable"

let print_back width ty var memory =
  with_buffer
    (fun f ->
      let layout = fst var in
      match !(S.unlink ty) with
      | S.Content (S.TTag _) -> (
          match layout with
          | Void -> pp_bot f
          | Int | Struct _ | Union _ ->
              readback f ty layout (List.assoc var memory))
      | S.Unbd _ -> pp_bot f
      | S.Link _ -> failwith "unreachable")
    width
