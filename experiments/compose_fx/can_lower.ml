open Syntax
open Symbol
open Type

exception Can_error of string

type ctx = { symbols : Symbol.t; fresh_tvar : fresh_tvar }

let can_error f s = raise (Can_error (f ^ ": " ^ s))

type named_var = string * tvar

type alias_definition = {
  alias_type : tvar;
  name : symbol;
  args : named_var list;
  real : tvar;
}

let opt_extract_named_var ty =
  match tvar_deref ty with ForA (Some x) -> Some (x, ty) | _ -> None

let extract_named_var ty =
  match opt_extract_named_var ty with
  | Some r -> r
  | None ->
      can_error "extract_named_var" "alias args must be a ForA with a name"

let rec collect_aliases : program -> alias_definition list = function
  | [] -> []
  | (_, ty, TyAlias (((_, x) as loc_x), args, real)) :: rest ->
      tvar_set ty @@ Alias { alias = (loc_x, args); real = snd real };

      let args = List.map extract_named_var @@ List.map snd args in
      { alias_type = ty; name = x; args; real = snd real }
      :: collect_aliases rest
  | _ :: rest -> collect_aliases rest

let rec collect_globals : program -> symbol list = function
  | [] -> []
  | (_, _, TyAlias _) :: rest -> collect_globals rest
  | (_, _, (Sig ((_, x), _) | Def ((_, x), _))) :: rest ->
      x :: collect_globals rest
  | (_, _, Run _) :: rest -> collect_globals rest

(** Must be called on a type before canonicalization (i.e. no links expected) *)
let rec extract_all_named_vars : tvar -> named_var list =
 fun tvar ->
  match tvar_deref tvar with
  | Unbd _ -> []
  | Link ty ->
      can_error "extract_all_named_vars"
        ("did not expect linked type" ^ show_tvar ty)
  | ForA (Some x) -> [ (x, tvar) ]
  | ForA None ->
      (* This is a *, let it go *)
      []
  | Content (TFn ((_, t1), lset, (_, t2))) ->
      extract_all_named_vars t1 @ extract_all_named_vars t2
      @ extract_all_named_vars lset
  | Content (TLambdaSet lset) ->
      let lset_args =
        List.flatten @@ List.map (fun { captures; _ } -> captures) lset
      in
      let extracted =
        List.flatten @@ List.map extract_all_named_vars lset_args
      in
      extracted
  | Content (TTag { tags; ext }) ->
      let tag_args = List.map snd @@ List.flatten @@ List.map snd tags in
      let extracted = List.flatten (List.map extract_all_named_vars tag_args) in
      extracted @ extract_all_named_vars (snd ext)
  | Content TTagEmpty -> []
  | Content (TPrim (`Str | `Unit | `Int)) -> []
  | Alias { alias = (_, _), args; real } ->
      (match tvar_deref real with
      | Unbd None -> ()
      | _ ->
          can_error "extract_all_named_vars"
            ("expected alias " ^ show_tvar tvar ^ " real to be unbound"));

      List.flatten @@ List.map extract_all_named_vars @@ List.map snd args

let canonicalize_alias { alias_type; name; args; real } =
  (* Go through and replace:
     - References to a type argument name with the alias's type argument type
     - References to the same alias with a recursive pointer
  *)
  let is_same_alias : loc_symbol * loc_tvar list -> bool =
   fun ((_, other_name), other_args) ->
    let other_args =
      List.map opt_extract_named_var @@ List.map snd other_args
    in
    let rec args_eq = function
      | [], [] -> true
      | (x, _) :: rest, Some (other_x, _) :: other_rest when x = other_x ->
          args_eq (rest, other_rest)
      | _ -> false
    in
    name = other_name && args_eq (args, other_args)
  in

  let rec update_ty : tvar -> unit =
   fun tvar ->
    match tvar_deref tvar with
    | Unbd _ -> ()
    | Link ty -> update_ty ty
    | ForA (Some x) -> (
        match List.assoc_opt x args with
        | Some arg -> tvar_set tvar @@ Link arg
        | None ->
            can_error "canonicalize_alias"
              ("alias " ^ show_symbol name ^ " does not have arg " ^ x))
    | ForA None ->
        can_error "canonicalize_alias"
          ("alias " ^ show_symbol name ^ " has a type argument without a name")
    | Content (TFn ((_, t1), lset, (_, t2))) ->
        update_ty t1;
        update_ty t2;
        update_ty lset
    | Content (TLambdaSet lset) ->
        let lset_args =
          List.flatten @@ List.map (fun { captures; _ } -> captures) lset
        in
        List.iter update_ty lset_args
    | Content (TTag { tags; ext }) ->
        let tag_args = List.map snd @@ List.flatten @@ List.map snd tags in
        List.iter update_ty tag_args;
        update_ty @@ snd ext
    | Content TTagEmpty -> ()
    | Content (TPrim (`Str | `Unit | `Int)) -> ()
    | Alias { alias; real = _ } when is_same_alias alias ->
        tvar_set tvar @@ Link alias_type;
        tvar_set_recur (unlink alias_type) true
    | Alias _ ->
        can_error "canonicalize_alias"
          ("cannot reference an alias " ^ show_tvar tvar
         ^ " with a different type")
  in
  update_ty real

type alias_map = (symbol * alias_definition) list
type arg_map = (variable * tvar) list

let show_arg_map : arg_map -> string =
 fun arg_map ->
  let show_arg (x, ty) = show_variable x ^ " -> " ^ show_tvar ty in
  String.concat "\t\n" @@ List.map show_arg arg_map

let sig_arg_map : tvar -> arg_map =
 fun tyvar ->
  let named_vars = extract_all_named_vars tyvar in
  List.filter_map
    (fun (x, ty) ->
      let canonical_ty = List.assoc x named_vars in
      if tvar_v ty = tvar_v canonical_ty then None
      else Some (tvar_v ty, canonical_ty))
    named_vars

let instantiate_signature : ctx -> alias_map -> tvar -> unit =
 fun ctx alias_map tvar ->
  let rec inst_alias : arg_map -> tvar -> ty_alias_content -> tvar =
   fun arg_map alias_type { alias = (_, name), args; real } ->
    (match tvar_deref real with
    | Unbd None -> ()
    | _ ->
        can_error "instantiate_type"
          "expected alias real to be unbound before instantiation");
    let {
      alias_type = scheme_alias_type;
      args = schme_args;
      real = scheme_ty;
      _;
    } =
      match List.assoc_opt name alias_map with
      | Some r -> r
      | None ->
          can_error "instantiate_alias"
            ("alias " ^ show_symbol name ^ " not found")
    in
    if List.length args <> List.length schme_args then
      can_error "instantiate_alias"
        ("alias " ^ show_symbol name ^ " has the wrong number of arguments");
    (* instantiate the arguments properly before continuing. *)
    List.iter
      (fun (_, tvar) -> tvar_set tvar @@ Link (inst_ty arg_map tvar))
      args;
    (* map the arguments in the scheme to the types we wish to instantiate.
       the alias may also appear in the scheme, so we map it as well. *)
    let scheme_arg_vars = List.map tvar_v @@ List.map snd @@ schme_args in
    let arg_tys = List.map snd args in
    tvar_set_recur (unlink alias_type) (tvar_recurs @@ unlink scheme_alias_type);
    let new_arg_map =
      (tvar_v scheme_alias_type, alias_type)
      :: List.combine scheme_arg_vars arg_tys
    in
    (* make sure we didn't override any variable mappings - if we did that's a
       bug. *)
    (match
       List.find_opt (fun (x, _) -> List.mem_assoc x arg_map) new_arg_map
     with
    | Some (x, _) ->
        can_error "instantiate_alias" (show_variable x ^ " already mapped")
    | None -> ());
    (* instantiate the real type *)
    let real = inst_ty new_arg_map scheme_ty in
    real
  and inst_ty : arg_map -> tvar -> tvar =
   fun arg_map tvar ->
    let rec inst_ty : tvar -> tvar =
     fun tvar ->
      let var = tvar_v tvar in
      let t' = ctx.fresh_tvar @@ Unbd None in
      let ty' =
        match List.assoc_opt var arg_map with
        | Some r ->
            if tvar_v r = var then
              can_error "instantiate_alias"
                ("alias " ^ show_variable var
               ^ " is told to instantiate to itself");
            Link r
        | None -> (
            match tvar_deref tvar with
            | Unbd s -> Unbd s
            | Link ty -> Link (inst_ty ty)
            | ForA a -> ForA a
            | Content TTagEmpty -> Content TTagEmpty
            | Content (TPrim `Str) -> Content (TPrim `Str)
            | Content (TPrim `Unit) -> Content (TPrim `Unit)
            | Content (TPrim `Int) -> Content (TPrim `Int)
            | Content (TFn ((_, t1), lset, (_, t2))) ->
                let t1' = ctx.fresh_tvar @@ Link (inst_ty t1) in
                let t2' = ctx.fresh_tvar @@ Link (inst_ty t2) in
                let lset' = ctx.fresh_tvar @@ Link (inst_ty lset) in
                Content (TFn ((Loc.noloc, t1'), lset', (Loc.noloc, t2')))
            | Content (TLambdaSet _) ->
                can_error "instantiate_type" "unexpected lambda set"
            | Content (TTag { tags; ext = _, ext }) ->
                let map_tag : ty_tag -> ty_tag =
                 fun (tag, vars) ->
                  let vars' =
                    List.map
                      (fun (_, t) ->
                        (Loc.noloc, ctx.fresh_tvar @@ Link (inst_ty t)))
                      vars
                  in
                  (tag, vars')
                in
                let tags' = List.map map_tag tags in
                let ext' = ctx.fresh_tvar @@ Link (inst_ty ext) in
                Content (TTag { tags = tags'; ext = (Loc.noloc, ext') })
            | Alias alias_content ->
                let real_ty = inst_alias arg_map t' alias_content in
                tvar_set alias_content.real (Link real_ty);
                Alias alias_content)
      in
      tvar_set t' ty';
      t'
    in
    inst_ty tvar
  in

  let arg_map = sig_arg_map tvar in
  tvar_set tvar @@ Link (inst_ty arg_map tvar)

let canonicalize_pat : e_pat -> Can.e_pat * tvar SymbolMap.t =
  let rec go_pat (_, t, p) =
    match p with
    | PVar (_, x) ->
        let can_pat = (t, Can.PVar x) in
        (can_pat, SymbolMap.singleton x t)
    | PTag ((_, tag), ps) ->
        let can_pats, refs = List.split @@ List.map go_pat ps in
        let can_pat = (t, Can.PTag (tag, can_pats)) in
        let refs = List.fold_left SymbolMap.union SymbolMap.empty refs in
        (can_pat, refs)
  in
  go_pat

type canonicalized_expr_output = {
  can_expr : Can.e_expr;
  references : tvar SymbolMap.t;
}

let canonicalize_expr ~ctx ~globals e =
  let rec go_branch (p, e) =
    let can_pat, defined_p = canonicalize_pat p in
    let can_expr, free_e = go_expr e in
    ((can_pat, can_expr), SymbolMap.diff free_e defined_p)
  and go_expr (_, t, e) =
    let can_expr, free =
      match e with
      | Var x ->
          let can_var = Can.Var x in
          (can_var, SymbolMap.singleton x t)
      | Str s ->
          let can_str = Can.Str s in
          (can_str, SymbolMap.empty)
      | Int i ->
          let can_int = Can.Int i in
          (can_int, SymbolMap.empty)
      | Unit ->
          let can_unit = Can.Unit in
          (can_unit, SymbolMap.empty)
      | Tag (tag, es) ->
          let can_exprs, free_es = List.split @@ List.map go_expr es in
          let free_es =
            List.fold_left SymbolMap.union SymbolMap.empty free_es
          in
          let can_tag = Can.Tag (tag, can_exprs) in
          (can_tag, free_es)
      | Let { recursive; bind = _, (_, t_x), x; expr; body } ->
          let expr, free_e = go_expr expr in
          recursive := SymbolMap.mem x free_e;
          let free_e = SymbolMap.remove x free_e in

          let body, free_b = go_expr body in
          let free_b = SymbolMap.remove x free_b in

          let t_expr, expr = expr in

          let can_let =
            match expr with
            | Can.Clos { arg; body = clos_body; captures; lam_sym = _ } ->
                (* We drop the closure can_expr type in the canonicalized def, so tie it to
                   the bind variable now. *)
                tvar_set t_expr @@ Link t_x;

                let captures = List.filter (fun (_, s) -> s <> x) captures in

                let letfn =
                  Can.Letfn
                    {
                      recursive = !recursive;
                      bind = (t_x, x);
                      arg;
                      body = clos_body;
                      captures;
                      sig_ = None;
                    }
                in
                Can.LetFn (letfn, body)
            | _ ->
                Can.Let
                  ( Letval
                      { bind = (t_x, x); body = (t_expr, expr); sig_ = None },
                    body )
          in

          (can_let, SymbolMap.union free_e free_b)
      | Clos { arg = _, (_, t_a), a; body } ->
          let body, free_b = go_expr body in
          let free = SymbolMap.remove a free_b in
          let captures =
            List.map (fun (s, t) -> (t, s))
            @@ SymbolMap.bindings
            @@ SymbolMap.remove_keys globals free
          in
          let lam_sym = ctx.symbols.fresh_symbol "lam" in
          let can_clos = Can.Clos { arg = (t_a, a); body; captures; lam_sym } in
          (can_clos, free)
      | Call (e1, e2) ->
          let can_e1, free_e1 = go_expr e1 in
          let can_e2, free_e2 = go_expr e2 in
          let free = SymbolMap.union free_e1 free_e2 in
          let can_call = Can.Call (can_e1, can_e2) in
          (can_call, free)
      | KCall (kfn, es) ->
          let can_es, free_es = List.split @@ List.map go_expr es in
          let free = List.fold_left SymbolMap.union SymbolMap.empty free_es in
          let can_kcall = Can.KCall (kfn, can_es) in
          (can_kcall, free)
      | When (e, branches) ->
          let can_e, free_e = go_expr e in
          let can_branches, free_branches =
            List.split @@ List.map go_branch branches
          in
          let free_branches =
            List.fold_left SymbolMap.union SymbolMap.empty free_branches
          in
          let free = SymbolMap.union free_e free_branches in
          let can_when = Can.When (can_e, can_branches) in
          (can_when, free)
    in
    ((t, can_expr), free)
  in
  let can_expr, references = go_expr e in
  { can_expr; references }

let mk_canonical_def ~ctx ~expr ~globals ~bind ~sig_ ~run =
  let { can_expr; references } = canonicalize_expr ~ctx ~globals expr in
  let t_bind_x, bind_x = bind in
  let recursive = SymbolMap.mem bind_x references in

  let t_can_expr, can_expr = can_expr in

  let references =
    SymbolMap.remove_keys globals @@ SymbolMap.remove bind_x references
  in
  assert (SymbolMap.is_empty references);

  match (run, can_expr) with
  | true, _ ->
      if recursive then
        can_error "canonicalize_defs" "run definitions cannot be recursive";
      Can.Run { bind; body = (t_can_expr, can_expr); sig_ }
  | false, Clos { arg; body; captures; lam_sym = _ } ->
      (* We drop the closure can_expr type in the canonicalized def, so tie it to
         the bind variable now. *)
      tvar_set t_can_expr @@ Link t_bind_x;

      let captures =
        List.filter
          (fun (_, s) -> s <> bind_x && not (List.mem s globals))
          captures
      in

      if List.length captures > 0 then
        failwith @@ "captured on toplevel: " ^ String.concat ", "
        @@ List.map show_symbol @@ List.map snd @@ captures;

      let letfn =
        Can.Letfn { recursive; bind; arg; body; sig_; captures = [] }
      in
      Can.Def { kind = `Letfn letfn }
  | false, _ ->
      if recursive then
        can_error "canonicalize_defs"
          "non-closure definitions cannot be recursive";
      let letval = Can.Letval { bind; body = (t_can_expr, can_expr); sig_ } in
      Can.Def { kind = `Letval letval }

let canonicalize_defs :
    ctx:ctx ->
    globals:symbol list ->
    alias_map:alias_map ->
    e_def list ->
    Can.def list =
 fun ~ctx ~globals ~alias_map defs ->
  let rec inner = function
    | [] -> []
    | (_, _, TyAlias _) :: rest -> inner rest
    | (_, sig_t, Sig ((_, x), (_, sig_)))
      :: (_, def_t, ((Def ((_, y), expr) | Run ((_, y), expr)) as def))
      :: rest ->
        if x <> y then
          can_error "canonicalize_defs"
            ("signature and definition names do not match: " ^ show_symbol x
           ^ " vs " ^ show_symbol y);
        let run = match def with Run _ -> true | _ -> false in
        instantiate_signature ctx alias_map sig_;
        (* Link the signature type to the signature def. We'll check that the
           signature matches the definition during solving. *)
        tvar_set sig_t @@ Link sig_;

        let bind : Can.typed_symbol = (def_t, y) in
        let sig_ = Some sig_ in

        let def = mk_canonical_def ~ctx ~expr ~globals ~bind ~sig_ ~run in
        def :: inner rest
    | (_, def_t, ((Def ((_, x), expr) | Run ((_, x), expr)) as def)) :: rest ->
        let run = match def with Run _ -> true | _ -> false in

        let bind : Can.typed_symbol = (def_t, x) in
        let sig_ = None in

        let def = mk_canonical_def ~ctx ~expr ~globals ~bind ~sig_ ~run in
        def :: inner rest
    | (_, sig_t, Sig ((_, x), (_, sig_))) :: rest ->
        instantiate_signature ctx alias_map sig_;
        tvar_set sig_t @@ Link sig_;
        if false then
          can_error "canonicalize_defs"
            ("signature " ^ show_symbol x ^ " does not have a definition");
        inner rest
  in

  inner @@ defs

let canonicalize : ctx -> Syntax.program -> Can.program =
 fun ctx program ->
  let aliases = collect_aliases program in
  List.iter canonicalize_alias aliases;
  let alias_map =
    List.map (fun (alias : alias_definition) -> (alias.name, alias)) aliases
  in
  let globals = collect_globals program in
  let defs = canonicalize_defs ~ctx ~globals ~alias_map program in
  defs
