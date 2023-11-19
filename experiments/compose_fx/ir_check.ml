open Ir

type fenv = (Symbol.symbol * proc) list
type venv = (Symbol.symbol * layout) list

let globals_names : definition list -> Symbol.symbol list =
 fun defs ->
  List.fold_left
    (fun acc def ->
      match def with Global { name; _ } -> name :: acc | _ -> acc)
    [] defs

let failctx : string -> string -> 'a =
 fun ctx msg -> failwith @@ "[" ^ ctx ^ "]: " ^ msg

let check_lay_equiv : string -> layout -> layout -> unit =
 fun ctx l1 l2 ->
  let visited_pairs = ref [] in
  let rec go l1 l2 =
    let already_visited =
      List.exists (fun (l1', l2') -> l1' == l1 && l2' == l2) !visited_pairs
    in
    if not already_visited then visited_pairs := (l1, l2) :: !visited_pairs;
    match (!l1, !l2) with
    | Str, Str -> ()
    | Struct ls1, Struct ls2 ->
        if List.length ls1 <> List.length ls2 then
          failctx ctx "Structs have different number of fields";
        List.iter2 go ls1 ls2
    | Union ls1, Union ls2 ->
        if List.length ls1 <> List.length ls2 then
          failctx ctx "Unions have different number of variants";
        List.iter2 go ls1 ls2
    | Box (l1, _), Box (l2, _) -> go l1 l2
    | Erased, Erased -> ()
    | FunctionPointer, FunctionPointer -> ()
    | _ ->
        failctx ctx @@ "Layouts are not equivalent: " ^ show_layout l1 ^ " and "
        ^ show_layout l2
  in
  go l1 l2

let get_union : layout -> layout list =
 fun lay ->
  match !lay with
  | Union ls -> ls
  | _ -> failwith @@ "Not a union: " ^ show_layout lay

let get_union_variant : layout -> int -> layout =
 fun lay i -> List.nth (get_union lay) i

let check_is_union : layout -> unit = fun lay -> ignore @@ get_union lay

let get_struct lay =
  match !lay with
  | Struct ls -> ls
  | _ -> failwith @@ "Not a struct: " ^ show_layout lay

let get_struct_field : layout -> int -> layout =
 fun lay i -> List.nth (get_struct lay) i

let check_is_ptr_type : layout -> unit =
 fun lay ->
  match !lay with
  | Box _ -> ()
  | _ -> failwith @@ "Not a pointer: " ^ show_layout lay

let lookup_var : string -> venv -> var -> layout =
 fun ctx venv (l_x, x) ->
  let l_x' = List.assoc x venv in
  check_lay_equiv ctx l_x' l_x;
  l_x

let check_expr : string -> fenv -> venv -> layout -> expr -> unit =
 fun ctx fenv venv lay e ->
  match e with
  | Var x ->
      let l_x = lookup_var ctx venv x in
      check_lay_equiv ctx l_x lay
  | MakeUnion (i, x) ->
      let l_variant = get_union_variant lay i in
      let l_x = lookup_var ctx venv x in
      check_lay_equiv ctx l_variant l_x
  | GetUnionId x ->
      let l_x = lookup_var ctx venv x in
      check_is_union l_x
  | GetUnionStruct x ->
      let l_x = lookup_var ctx venv x in
      check_is_union l_x
  | MakeStruct xs ->
      let ls = List.map (lookup_var ctx venv) xs in
      check_lay_equiv ctx (ref @@ Struct ls) lay
  | GetStructField (x, i) ->
      let l_x = lookup_var ctx venv x in
      let l_field = get_struct_field l_x i in
      check_lay_equiv ctx l_field lay
  | CallIndirect (f, args) ->
      let l_f = lookup_var ctx venv f in
      check_lay_equiv ctx (ref @@ FunctionPointer) l_f;
      ignore @@ List.map (lookup_var ctx venv) args
  | CallDirect (f, args) ->
      let proc = List.assoc f fenv in
      let l_args = List.map (lookup_var ctx venv) args in
      let proc_args = List.map (fun (l, _) -> l) proc.args in
      List.iter2 (check_lay_equiv ctx) proc_args l_args;
      let proc_l_ret = fst proc.ret in
      check_lay_equiv ctx proc_l_ret lay
  | MakeBox x ->
      let l_x = lookup_var ctx venv x in
      check_lay_equiv ctx (ref @@ Box (l_x, None)) lay
  | GetBoxed x ->
      let l_x = lookup_var ctx venv x in
      check_lay_equiv ctx l_x (ref @@ Box (lay, None))
  | PtrCast (x, new_l) ->
      let l_x = lookup_var ctx venv x in
      check_is_ptr_type l_x;
      check_is_ptr_type new_l;
      check_lay_equiv ctx new_l lay
  | MakeFnPtr f ->
      ignore @@ List.assoc f fenv;
      check_lay_equiv ctx (ref @@ FunctionPointer) lay

let ctx_join : string -> string -> string = fun ctx1 ctx2 -> ctx1 ^ ":" ^ ctx2

let check_body : string -> fenv -> venv -> var -> stmt list -> unit =
 fun ctx fenv venv (l_ret, ret) stmts ->
  let rec go i venv = function
    | [] ->
        let ret_layout = List.assoc ret venv in
        check_lay_equiv (ctx_join ctx "ret") ret_layout l_ret
    | Let ((l_x, x), e) :: rest ->
        check_expr (ctx_join ctx (Symbol.show_symbol x)) fenv venv l_x e;
        go (i + 1) ((x, l_x) :: venv) rest
  in
  go 0 venv stmts

let check_definitions : definition list -> unit =
 fun definitions ->
  let rec go fenv venv = function
    | [] -> ()
    | Global { name; layout; init } :: rest ->
        check_expr ("global " ^ Symbol.show_symbol name) fenv venv layout init;
        go fenv ((name, layout) :: venv) rest
    | Proc ({ name; args; body; ret } as proc) :: rest ->
        let body_venv' =
          List.fold_left
            (fun acc (layout, name) -> (name, layout) :: acc)
            venv args
        in
        check_body ("proc " ^ Symbol.show_symbol name) fenv body_venv' ret body;
        go ((name, proc) :: fenv) venv rest
  in

  go [] [] definitions

let check : program -> unit =
 fun { definitions; entry_points } ->
  let globals = globals_names definitions in
  List.iter
    (fun ep ->
      if not (List.mem ep globals) then
        failwith ("Entry point " ^ Symbol.show_symbol ep ^ " not found"))
    entry_points;
  check_definitions definitions
