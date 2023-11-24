open Ir

type memory_cell =
  | Word of int
  | Label of Symbol.symbol
  | Block of memory_cell list
[@@deriving show]

type memory = (var * memory_cell) list

let word i = Word i
let label l = Label l
let block l = Block l
let get_word = function Word i -> i | _ -> failwith "not a word"
let get_label = function Label l -> l | _ -> failwith "not a label"
let get_block = function Block l -> l | _ -> failwith "not a block"

let rec eval_expr : memory -> expr -> memory_cell =
 fun memory expr ->
  let lookup x = List.assoc x memory in
  match expr with
  | Var x -> lookup x
  | Lit (`Int i) -> word i
  | Lit (`String s) ->
      block @@ List.map word @@ List.map Char.code @@ List.of_seq
      @@ String.to_seq s
  | MakeUnion (id, var) -> block @@ (word id :: get_block (lookup var))
  | GetUnionId var -> List.hd @@ get_block @@ lookup var
  | GetUnionStruct var -> block @@ List.tl @@ get_block @@ lookup var
  | MakeStruct vs -> block @@ List.map lookup vs
  | GetStructField (v, i) -> List.nth (get_block @@ lookup v) i
  | CallIndirect (fn, args) ->
      let fn = get_label @@ lookup fn in
      let args = List.map lookup args in
      eval_call memory fn args
  | CallDirect (fn, args) ->
      let args = List.map lookup args in
      eval_call memory fn args
  | MakeBox v -> block [ lookup v ]
  | GetBoxed v -> List.hd @@ get_block @@ lookup v
  | PtrCast (v, _) -> lookup v
  | MakeFnPtr fn -> label fn

and eval_call : memory -> Symbol.symbol -> memory_cell list -> memory_cell =
 fun _memory _fn _args -> failwith "TODO eval_call"
