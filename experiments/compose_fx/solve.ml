open Syntax

exception Solve_err of string

let failsolve f s = raise (Solve_err (f ^ ": " ^ s))

type venv = (string * tvar) list

let inst : fresh_tvar -> tvar -> tvar =
 fun fresh_tvar tvar ->
  let tenv : (variable * tvar) list ref = ref [] in
  let rec go : tvar -> tvar =
   fun t ->
    let var = tvar_v t in
    match List.assoc_opt var !tenv with
    | Some t -> t
    | None ->
        let set_t = fresh_tvar (Unbd None) in
        tenv := (var, set_t) :: !tenv;
        let t' =
          match tvar_deref t with
          | Unbd _ -> t
          | Link t -> go t
          | ForA x -> fresh_tvar (Unbd x)
          | Content (TPrim (`Str | `Unit)) | Content TTagEmpty -> t
          | Content (TTag { tags; ext = _, ext }) ->
              let map_tag : ty_tag -> ty_tag =
               fun (tag, args) ->
                let args = List.map (fun (_, t) -> (noloc, go t)) args in
                (tag, args)
              in
              let tags = List.map map_tag tags in
              let ext = (noloc, go ext) in
              fresh_tvar @@ Content (TTag { tags; ext })
          | Content (TFn ((_, t1), (_, t2))) ->
              let t1 = (noloc, go t1) in
              let t2 = (noloc, go t2) in
              fresh_tvar @@ Content (TFn (t1, t2))
          | Alias { alias = name, args; real } ->
              let args = List.map (fun (_, t) -> (noloc, go t)) args in
              let real = go real in
              fresh_tvar @@ Alias { alias = (name, args); real }
        in
        tvar_set_recur t' (tvar_recurs @@ unlink t);
        tvar_set set_t (Link t');
        t'
  in

  go tvar

let occurs : variable -> tvar -> bool =
 fun v t ->
  let visited = ref [] in
  let rec go t =
    let var = tvar_v t in
    if List.mem var !visited then false
    else (
      visited := var :: !visited;
      match tvar_deref t with
      | Unbd _ -> var = v
      | ForA _ ->
          (* generalized variables are not a specific instance, they cannot
             occur because there is nothing more general. *)
          false
      | Link t -> go t
      | Content (TPrim (`Str | `Unit)) | Content TTagEmpty -> false
      | Content (TTag { tags; ext }) ->
          let check_tag : ty_tag -> bool =
           fun (_, args) -> List.exists (fun (_, t) -> go t) args
          in
          List.exists check_tag tags || go (snd ext)
      | Content (TFn ((_, t1), (_, t2))) -> go t1 || go t2
      | Alias { alias = _, args; real } ->
          List.exists (fun (_, t) -> go t) args || go real)
  in
  go t

let gen : venv -> tvar -> unit =
 fun venv t ->
  let visited = ref [] in
  let rec go t =
    let var = tvar_v t in
    if List.mem var !visited then ()
    else (
      visited := var :: !visited;
      match tvar_deref t with
      | Unbd s ->
          if List.exists (fun (_, t) -> occurs var t) venv then
            (* variable occurs in the current env, don't generalize *)
            ()
          else tvar_set t (ForA s)
      | Link t -> go t
      | ForA _ -> ()
      | Content (TPrim (`Str | `Unit)) | Content TTagEmpty -> ()
      | Content (TTag { tags; ext }) ->
          let gen_tag : ty_tag -> unit =
           fun (_, args) -> List.iter (fun (_, t) -> go t) args
          in
          List.iter gen_tag tags;
          go (snd ext)
      | Content (TFn ((_, t1), (_, t2))) ->
          go t1;
          go t2
      | Alias { alias = _, args; real } ->
          List.iter (fun (_, t) -> go t) args;
          go real)
  in
  go t

let sort_tags : ty_tag list -> ty_tag list =
 fun tags -> List.sort (fun (tag1, _) (tag2, _) -> compare tag1 tag2) tags

type separated_tags = {
  shared : (ty_tag * ty_tag) list;
  only1 : ty_tag list;
  only2 : ty_tag list;
}

let separate_tags tags1 ext1 tags2 ext2 =
  let tags1, ext1 = chase_tags tags1 ext1 in
  let tags2, ext2 = chase_tags tags2 ext2 in
  let tags1, tags2 = (sort_tags tags1, sort_tags tags2) in
  let rec walk shared only1 only2 = function
    | [], [] -> { shared; only1 = List.rev only1; only2 = List.rev only2 }
    | o :: rest, [] -> walk shared (o :: only1) only2 (rest, [])
    | [], o :: rest -> walk shared only1 (o :: only2) ([], rest)
    | t1 :: rest1, t2 :: rest2 when fst t1 < fst t2 ->
        walk shared (t1 :: only1) only2 (rest1, t2 :: rest2)
    | t1 :: rest1, t2 :: rest2 when fst t1 > fst t2 ->
        walk shared only1 (t2 :: only2) (t1 :: rest1, rest2)
    | t1 :: rest1, t2 :: rest2 ->
        walk ((t1, t2) :: shared) only1 only2 (rest1, rest2)
  in
  let result = walk [] [] [] (tags1, tags2) in
  (result, ext1, ext2)

let unify : string -> fresh_tvar -> tvar -> tvar -> unit =
 fun ctx fresh_tvar a b ->
  let error prefix =
    failsolve "unify"
      ("(" ^ ctx ^ ")" ^ prefix ^ " at "
      ^ string_of_tvar default_width [] a
      ^ " ~ "
      ^ string_of_tvar default_width [] b)
  in
  let rec unify_tags : _ -> ty_tag -> ty_tag -> unit =
   fun visited (t1, args1) (t2, args2) ->
    assert (t1 = t2);
    if List.length args1 <> List.length args2 then
      error ("arity mismatch for tag " ^ t1);
    List.iter2 (unify visited) (List.map snd args1) (List.map snd args2)
  and unify visited a b =
    let a, b = (unlink a, unlink b) in
    let vara, varb = (tvar_v a, tvar_v b) in
    if List.mem (vara, varb) visited then (
      tvar_set_recur a true;
      tvar_set_recur b true)
    else if vara <> varb then (
      let visited = (vara, varb) :: visited in
      let unify = unify visited in
      let ty_a = tvar_deref a in
      let ty_b = tvar_deref b in
      let ty =
        match (ty_a, ty_b) with
        | Link _, _ | _, Link _ -> error "found a link where none was expected"
        | ForA _, _ | _, ForA _ ->
            error
              ("cannot unify generalized type; forgot to instantiate?"
              ^ show_tvar (fresh_tvar @@ ty_a)
              ^ " ~ "
              ^ show_tvar (fresh_tvar @@ ty_b))
        | Unbd None, Unbd (Some x) | Unbd (Some x), Unbd None -> Unbd (Some x)
        | Unbd _, other | other, Unbd _ -> other
        | _, Alias { alias; real } ->
            unify a real;
            Alias { alias; real }
        | Alias { alias; real }, _ ->
            unify real b;
            Alias { alias; real }
        | Content c1, Content c2 ->
            let c' =
              match (c1, c2) with
              | TPrim `Str, TPrim `Str -> TPrim `Str
              | TPrim `Unit, TPrim `Unit -> TPrim `Unit
              | TTagEmpty, TTagEmpty -> TTagEmpty
              | TTagEmpty, TTag { tags = []; ext = _, ext }
              | TTag { tags = []; ext = _, ext }, TTagEmpty ->
                  unify a ext;
                  TTagEmpty
              | ( TTag { tags = tags1; ext = _, ext1 },
                  TTag { tags = tags2; ext = _, ext2 } ) -> (
                  let { shared; only1; only2 }, ext1, ext2 =
                    separate_tags tags1 ext1 tags2 ext2
                  in

                  let shared : ty_tag list =
                    List.map
                      (fun (t1, t2) ->
                        unify_tags visited t1 t2;
                        t1)
                      shared
                  in

                  match ((only1, ext1), (only2, ext2)) with
                  | ([], ext1), ([], ext2) ->
                      unify ext1 ext2;
                      TTag { tags = shared; ext = (noloc, ext1) }
                  | (others, ext1), ([], ext2) | ([], ext2), (others, ext1) ->
                      let other_tag_union =
                        fresh_tvar
                        @@ Content (TTag { tags = others; ext = (noloc, ext1) })
                      in
                      unify ext2 other_tag_union;
                      let tags = sort_tags @@ shared @ others in
                      TTag { tags; ext = (noloc, ext1) }
                  | (others1, ext1), (others2, ext2) ->
                      let new_ext = (noloc, fresh_tvar @@ Unbd None) in
                      let tags1 =
                        fresh_tvar
                        @@ Content (TTag { tags = others1; ext = new_ext })
                      in
                      let tags2 =
                        fresh_tvar
                        @@ Content (TTag { tags = others2; ext = new_ext })
                      in
                      unify ext1 tags2;
                      unify ext2 tags1;

                      let all_tags = sort_tags @@ shared @ others1 @ others2 in
                      TTag { tags = all_tags; ext = new_ext })
              | TFn ((_, t11), (_, t12)), TFn ((_, t21), (_, t22)) ->
                  unify t11 t21;
                  unify t12 t22;
                  TFn ((noloc, t11), (noloc, t12))
              | _ -> error "incompatible"
            in
            Content c'
      in
      (* unify up-front to avoid infinite recursion at recursive types *)
      let recurs = tvar_recurs a || tvar_recurs b in
      let c = fresh_tvar @@ Unbd None in
      tvar_set a (Link c);
      tvar_set b (Link c);
      tvar_set c ty;
      tvar_set_recur c recurs)
  in
  unify [] a b

let infer_expr : fresh_tvar -> venv -> e_expr -> tvar =
 fun fresh_tvar venv expr ->
  let unify c = unify c fresh_tvar in
  let rec infer : venv -> e_expr -> tvar =
   fun venv (_, t, e) ->
    let ty =
      match e with
      | Var x -> (
          match List.assoc_opt x venv with
          | Some t -> inst fresh_tvar t
          | None -> failsolve "infer" ("unbound variable " ^ x))
      | Tag (tag, args) ->
          let arg_tys =
            List.map (fun t -> (noloc, t)) @@ List.map (infer venv) @@ args
          in
          let ext = (noloc, fresh_tvar @@ Unbd None) in
          fresh_tvar @@ Content (TTag { tags = [ (tag, arg_tys) ]; ext })
      | Let ((_, (_, t_x), x), e, b) ->
          let t_x' = infer venv e in
          unify ("let " ^ x) t_x t_x';
          infer ((x, t_x) :: venv) b
      | Clos ((_, (_, t_x), x), e) ->
          let t_ret = infer ((x, t_x) :: venv) e in
          fresh_tvar @@ Content (TFn ((noloc, t_x), (noloc, t_ret)))
      | Call (e1, e2) ->
          let t_fn = infer venv e1 in
          let t_arg = infer venv e2 in
          let t_ret = fresh_tvar @@ Unbd None in
          let t_fn_expected =
            fresh_tvar @@ Content (TFn ((noloc, t_arg), (noloc, t_ret)))
          in
          unify "call" t_fn t_fn_expected;
          t_ret
    in
    unify "top-level expr" t ty;
    ty
  in
  infer venv expr

let infer_def : fresh_tvar -> venv -> Canonical.can_def -> tvar =
 fun fresh_tvar venv { name; ty; def; sig_; run = _ } ->
  let t = infer_expr fresh_tvar venv def in
  Option.iter
    (fun t_sig ->
      let t_sig = inst fresh_tvar t_sig in
      unify ("with sig " ^ name) fresh_tvar t t_sig)
    sig_;
  unify ("with toplevel def" ^ name) fresh_tvar t ty;
  gen venv ty;
  t

type ctx = { fresh_tvar : fresh_tvar }

let infer_program : ctx -> Canonical.program -> unit =
 fun { fresh_tvar } defs ->
  let rec go venv = function
    | [] -> ()
    | def :: defs ->
        let t = infer_def fresh_tvar venv def in
        go ((def.name, t) :: venv) defs
  in
  go [] defs
