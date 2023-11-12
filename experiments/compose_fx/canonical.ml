open Syntax

exception Can_error of string

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

let can_alias { alias_type; name; args; real } =
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
        can_error "can_alias" ("did not expect unbound type" ^ show_tvar tvar)
    | Link ty -> update_ty ty
    | ForA (Some x) -> (
        match List.assoc_opt x args with
        | Some arg -> tvar_set tvar @@ Link arg
        | None ->
            can_error "can_alias" ("alias " ^ name ^ " does not have arg " ^ x))
    | ForA None ->
        can_error "can_alias"
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
    | Alias { alias; real } when is_same_alias alias ->
        tvar_set real @@ Link alias_type
    | Alias _ ->
        can_error "can_alias"
          ("cannot reference an alias " ^ show_tvar tvar
         ^ " with a different type")
  in
  update_ty real

let canonicalize : program -> unit =
 fun program ->
  let aliases = collect_aliases program in
  List.iter can_alias aliases
