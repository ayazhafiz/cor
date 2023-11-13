open Syntax

exception Can_error of string

type ctx = { fresh_tvar : fresh_tvar }

let can_error f s = raise (Can_error (f ^ ": " ^ s))

type alias_arg = string * tvar

type alias_definition = {
  alias_type : tvar;
  name : string;
  args : alias_arg list;
  real : tvar;
}

let opt_extract_alias_arg ty =
  match tvar_deref ty with ForA (Some x) -> Some (x, ty) | _ -> None

let extract_alias_arg ty =
  match opt_extract_alias_arg ty with
  | Some r -> r
  | None ->
      can_error "extract_alias_arg" "alias args must be a ForA with a name"

let rec collect_aliases : program -> alias_definition list = function
  | [] -> []
  | (_, ty, TyAlias (((_, x) as loc_x), args, real)) :: rest ->
      tvar_set ty @@ Alias { alias = (loc_x, args); real = snd real };

      let args = List.map extract_alias_arg @@ List.map snd args in
      { alias_type = ty; name = x; args; real = snd real }
      :: collect_aliases rest
  | _ :: rest -> collect_aliases rest

let canonicalize_alias { alias_type; name; args; real } =
  (* Go through and replace:
     - References to a type argument name with the alias's type argument type
     - References to the same alias with a recursive pointer
  *)
  let is_same_alias : loc_str * loc_tvar list -> bool =
   fun ((_, other_name), other_args) ->
    let other_args =
      List.map opt_extract_alias_arg @@ List.map snd other_args
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
    | Unbd ->
        can_error "canonicalize_alias"
          ("did not expect unbound type" ^ show_tvar tvar)
    | Link ty -> update_ty ty
    | ForA (Some x) -> (
        match List.assoc_opt x args with
        | Some arg -> tvar_set tvar @@ Link arg
        | None ->
            can_error "canonicalize_alias"
              ("alias " ^ name ^ " does not have arg " ^ x))
    | ForA None ->
        can_error "canonicalize_alias"
          ("alias " ^ name ^ " has a type argument without a name")
    | Content (TFn ((_, t1), (_, t2))) ->
        update_ty t1;
        update_ty t2
    | Content (TTag { tags; ext }) ->
        let tag_args = List.map snd @@ List.flatten @@ List.map snd tags in
        List.iter update_ty tag_args;
        update_ty @@ snd ext
    | Content TTagEmpty -> ()
    | Content (TPrim (`Str | `Unit)) -> ()
    | Alias { alias; real = _ } when is_same_alias alias ->
        tvar_set tvar @@ Link alias_type
    | Alias _ ->
        can_error "canonicalize_alias"
          ("cannot reference an alias " ^ show_tvar tvar
         ^ " with a different type")
  in
  update_ty real

type alias_map = (string * alias_definition) list
type arg_map = (variable * tvar) list

let instantiate_type : ctx -> alias_map -> tvar -> unit =
 fun ctx alias_map tvar ->
  let rec inst_alias : arg_map -> tvar -> ty_alias_content -> ty =
   fun arg_map alias_type { alias = (_, name), args; real } ->
    (match tvar_deref real with
    | Unbd -> ()
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
      | None -> can_error "instantiate_alias" ("alias " ^ name ^ " not found")
    in
    if List.length args <> List.length schme_args then
      can_error "instantiate_alias"
        ("alias " ^ name ^ " has the wrong number of arguments");
    (* map the arguments in the scheme to the types we wish to instantiate.
       the alias may also appear in the scheme, so we map it as well. *)
    let scheme_arg_vars = List.map tvar_v @@ List.map snd @@ schme_args in
    let arg_tys = List.map snd args in
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
    inst_ty new_arg_map scheme_ty
  and inst_ty : arg_map -> tvar -> ty =
   fun arg_map tvar ->
    let rec inst_ty : tvar -> ty =
     fun tvar ->
      let var = tvar_v tvar in
      match List.assoc_opt var arg_map with
      | Some r -> Link r
      | None -> (
          match tvar_deref tvar with
          | Unbd ->
              can_error "instantiate_alias" ("unbound type" ^ show_tvar tvar)
          | Link ty -> Link ty
          | ForA a -> ForA a
          | Content TTagEmpty -> Content TTagEmpty
          | Content (TPrim `Str) -> Content (TPrim `Str)
          | Content (TPrim `Unit) -> Content (TPrim `Unit)
          | Content (TFn ((_, t1), (_, t2))) ->
              let t1' = ctx.fresh_tvar @@ inst_ty t1 in
              let t2' = ctx.fresh_tvar @@ inst_ty t2 in
              Content (TFn ((noloc, t1'), (noloc, t2')))
          | Content (TTag { tags; ext = _, ext }) ->
              let map_tag : ty_tag -> ty_tag =
               fun (tag, vars) ->
                let vars' =
                  List.map
                    (fun (_, t) -> (noloc, ctx.fresh_tvar @@ inst_ty t))
                    vars
                in
                (tag, vars')
              in
              let tags' = List.map map_tag tags in
              let ext' = ctx.fresh_tvar @@ inst_ty ext in
              Content (TTag { tags = tags'; ext = (noloc, ext') })
          | Alias alias_content ->
              let real_ty = inst_alias arg_map tvar alias_content in
              tvar_set alias_content.real real_ty;
              Alias alias_content)
    in
    inst_ty tvar
  in

  tvar_set tvar @@ inst_ty [] tvar

type can_def = {
  name : string;
  ty : tvar;
  def : e_expr;
  sig_ : tvar option;
  run : bool;
}

let canonicalize_defs : ctx -> alias_map -> e_def list -> can_def list =
 fun ctx alias_map defs ->
  let rec inner = function
    | [] -> []
    | (_, _, TyAlias _) :: rest -> inner rest
    | (_, sig_t, Sig ((_, x), (_, sig_)))
      :: (_, def_t, ((Def ((_, y), expr) | Run ((_, y), expr)) as def))
      :: rest ->
        if x <> y then
          can_error "canonicalize_defs"
            ("signature and definition names do not match: " ^ x ^ " vs " ^ y);
        let run = match def with Run _ -> true | _ -> false in
        (* instantiate the signature *)
        instantiate_type ctx alias_map sig_;
        (* Link the signature type to the signature def. We'll check that the
           signature matches the definition during solving. *)
        tvar_set sig_t @@ Link sig_;
        let def = { name = x; ty = def_t; def = expr; sig_ = Some sig_; run } in
        def :: inner rest
    | (_, def_t, ((Def ((_, x), expr) | Run ((_, x), expr)) as def)) :: rest ->
        let run = match def with Run _ -> true | _ -> false in
        let def = { name = x; ty = def_t; def = expr; sig_ = None; run } in
        def :: inner rest
    | (_, _, Sig ((_, x), _)) :: _ ->
        can_error "canonicalize_defs"
          ("signature " ^ x ^ " does not have a definition")
  in
  inner @@ defs

type program = can_def list

let canonicalize : ctx -> Syntax.program -> program =
 fun ctx program ->
  let aliases = collect_aliases program in
  List.iter canonicalize_alias aliases;
  let alias_map =
    List.map (fun (alias : alias_definition) -> (alias.name, alias)) aliases
  in
  let defs = canonicalize_defs ctx alias_map program in
  defs
