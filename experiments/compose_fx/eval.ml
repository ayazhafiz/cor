open Ir
open Symbol

type memory_cell = Word of int | Label of symbol | Block of memory_cell list
type memory = (symbol * memory_cell) list
type procs = (symbol * proc) list

let word i = Word i
let label l = Label l
let block l = Block l
let get_word = function Word i -> i | _ -> failwith "not a word"
let get_label = function Label l -> l | _ -> failwith "not a label"
let get_block = function Block l -> l | _ -> failwith "not a block"

let get_string cell =
  let block = get_block cell in
  let words = List.map get_word block in
  String.of_seq @@ List.to_seq @@ List.map Char.chr words

let make_string s =
  block @@ List.map word @@ List.map Char.code @@ List.of_seq @@ String.to_seq s

let eval_kcall : Syntax.kernelfn -> memory_cell list -> memory_cell =
 fun kfn args ->
  match kfn with
  | `StrConcat ->
      let ss = List.map get_string args in
      make_string @@ String.concat "" ss
  | `Itos ->
      let i = get_word @@ List.hd args in
      make_string @@ string_of_int i
  | `Add ->
      let is = List.map get_word args in
      word @@ List.fold_left ( + ) 0 is

let rec eval_expr : procs -> memory -> expr -> memory_cell =
 fun procs memory expr ->
  let lookup x = List.assoc (snd x) memory in
  match expr with
  | Var x -> lookup x
  | Lit (`Int i) -> word i
  | Lit (`String s) -> make_string s
  | MakeUnion (id, var) -> block @@ (word id :: get_block (lookup var))
  | GetUnionId var -> List.hd @@ get_block @@ lookup var
  | GetUnionStruct var -> block @@ List.tl @@ get_block @@ lookup var
  | MakeStruct vs -> block @@ List.map lookup vs
  | GetStructField (v, i) -> List.nth (get_block @@ lookup v) i
  | CallIndirect (fn, args) ->
      let fn = get_label @@ lookup fn in
      let args = List.map lookup args in
      eval_call procs memory fn args
  | CallDirect (fn, args) ->
      let args = List.map lookup args in
      eval_call procs memory fn args
  | CallKFn (fn, args) ->
      let args = List.map lookup args in
      eval_kcall fn args
  (* ignore boxes *)
  | MakeBox v -> lookup v
  | GetBoxed v -> lookup v
  | PtrCast (v, _) -> lookup v
  | MakeFnPtr fn -> label fn

and eval_stmt : procs -> memory -> stmt -> memory =
 fun procs memory stmt ->
  match stmt with
  | Let (x, e) ->
      let data = eval_expr procs memory e in
      (snd x, data) :: memory
  | Switch { cond; branches; join } ->
      let id = get_word @@ List.assoc (snd cond) memory in
      let branch_stmts, branch_expr = List.assoc id branches in
      let memory = eval_stmts procs memory branch_stmts in
      eval_stmt procs memory (Let (join, branch_expr))

and eval_stmts : procs -> memory -> stmt list -> memory =
 fun procs memory stmts -> List.fold_left (eval_stmt procs) memory stmts

and eval_call : procs -> memory -> symbol -> memory_cell list -> memory_cell =
 fun procs memory fn args ->
  let { args = arg_vars; body; ret; name = _ } = List.assoc fn procs in
  let arg_syms = List.map snd arg_vars in
  let arg_cells = List.combine arg_syms args in
  let memory = arg_cells @ memory in
  let memory = eval_stmts procs memory body in
  List.assoc (snd ret) memory

let eval_globals : procs -> definition list -> memory =
 fun procs definitions ->
  let rec go memory = function
    | [] -> memory
    | Proc _ :: rest -> go memory rest
    | Global { name; init; layout = _ } :: rest ->
        let data = eval_expr procs memory init in
        go ((name, data) :: memory) rest
  in
  go [] definitions

let rec find_procs = function
  | [] -> []
  | Proc ({ name; _ } as proc) :: rest -> (name, proc) :: find_procs rest
  | _ :: rest -> find_procs rest

type evaled = { symbol : symbol; cell : memory_cell; var : Type.tvar }

let eval_program : program -> evaled list =
 fun { definitions; entry_points } ->
  let procs = find_procs definitions in
  let memory = eval_globals procs definitions in
  List.map
    (fun (symbol, var) -> { symbol; cell = List.assoc symbol memory; var })
    entry_points

(* readback *)

let pp_memory_cell f cell =
  let rec go f = function
    | Word i -> Format.fprintf f "%d" i
    | Label l -> Format.fprintf f "%s" (Symbol.norm_of l)
    | Block l ->
        Format.fprintf f "@[[%a]@]"
          (Format.pp_print_list ~pp_sep:Format.pp_print_space go)
          l
  in
  go f cell

let readback : Symbol.t -> memory_cell -> Type.tvar -> Syntax.e_expr =
 fun symbols cell tvar ->
  let open Syntax in
  let open Type in
  let rec go cell t =
    let t = unlink_w_alias t in
    let expr =
      match tvar_deref t with
      | Link _ -> failwith "link after unlink"
      | Unbd _ -> Var (symbols.fresh_symbol "<unbound>")
      | ForA _ -> failwith "forA after monomorphization"
      | Content (TPrim `Unit) -> Unit
      | Content (TPrim `Int) -> Int (get_word cell)
      | Content (TPrim `Str) -> Str (get_string cell)
      | Content TTagEmpty -> Var (symbols.fresh_symbol "<void>")
      | Content (TLambdaSet _) -> failwith "lambda set in surface syntax"
      | Content (TTag { tags; ext = _, ext }) ->
          let tags, _ext = chase_tags tags ext in

          let block = get_block cell in
          let tag_id = get_word @@ List.hd block in
          let tag_struct = List.tl block in

          let tag_name, tag_payload_vars = List.nth tags tag_id in
          let tag_payload_vars = List.map snd tag_payload_vars in

          let tag_payloads = List.map2 go tag_struct tag_payload_vars in
          Tag (tag_name, tag_payloads)
      | Content (TFn _) -> Var (symbols.fresh_symbol "<fn>")
      | Alias _ -> failwith "alias after unlink"
    in
    (Loc.noloc, t, expr)
  in
  go cell tvar

let pp_readback symbols f (cell, tvar) =
  let expr = readback symbols cell tvar in
  Format.fprintf f "@[%a@]" (Syntax.pp_e_expr symbols) expr

let pp_evaled symbols f { symbol; cell; var } =
  Format.fprintf f "@[%s @[<v 0>= %a@,> %a@]@]" (Symbol.norm_of symbol)
    pp_memory_cell cell (pp_readback symbols) (cell, var)

let pp_evaled_list f symbols (l : evaled list) =
  Format.fprintf f "@[<v 0>%a@]" (Format.pp_print_list (pp_evaled symbols)) l

let string_of_evaled ?(width = Util.default_width) symbols (list : evaled list)
    =
  Util.with_buffer (fun f -> pp_evaled_list f symbols list) width
