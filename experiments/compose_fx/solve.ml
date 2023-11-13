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
        tenv := (var, t') :: !tenv;
        t'
  in

  go tvar

let occurs : variable -> tvar -> bool =
  let visited = ref [] in
  fun v t ->
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
  let rec go t =
    let var = tvar_v t in
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
        go real
  in
  go t

let unify : fresh_tvar -> tvar -> tvar -> unit =
 fun fresh_tvar a b ->
  let error prefix =
    failsolve "unfify"
      (prefix ^ " at "
      ^ string_of_tvar default_width [] a
      ^ " ~ "
      ^ string_of_tvar default_width [] b)
  in
  let rec unify a b =
    let a, b = (unlink a, unlink b) in
    if tvar_v a <> tvar_v b then (
      let c = fresh_tvar @@ Unbd None in
      (* unify up-front to avoid infinite recursion at recursive types *)
      tvar_set a (Link c);
      tvar_set b (Link c);
      let ty =
        match (tvar_deref a, tvar_deref b) with
        | Link _, _ | _, Link _ -> error "found a link where none was expected"
        | ForA _, _ | _, ForA _ ->
            error "cannot unify generalized type; forgot to instantiate?"
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
              | ( TTag { tags = tags1; ext = ext1 },
                  TTag { tags = tags2; ext = ext2 } ) -> (
                  let { shared; only1; only2 }, ext1, ext2 =
                    separate_tags tags1 ext1 tags2 ext2
                  in
                  List.iter (fun ((t1, args1), (t2, args2)) ->
                      assert (t1 = t2);
                      if List.length args1 <> List.length args2 then
                        error ("arity mismatch for tag " ^ t1);
                      List.iter2 unify (List.map snd args1) (List.map snd args2));

                  match ((only1, ext1), (only2, ext2)) with
                  | ([], ext1), ([], ext2) ->
                      unify ext1 ext2;
                      TTag { tags = shared; ext = ext1 }
                  | (others, ext1), ([], ext2) | ([], ext2), (others, ext1) ->
                      unify ext2
                        (ctx.fresh_tvar
                        @@ Content (TTag { tags = others; ext = ext1 }));
                      let tags = sort_tags @@ shared @ others in
                      TTag { tags; ext = ext1 }
                  | (others1, ext1), (others2, ext2) ->
                      let new_ext = ctx.fresh_tvar @@ Content Unbd in
                      let tags1 =
                        ctx.fresh_tvar
                        @@ Content (TTag { tags = others1; ext = new_ext })
                      in
                      let tags2 =
                        ctx.fresh_tvar
                        @@ Content (TTag { tags = others2; ext = new_ext })
                      in
                      unify ext1 tag2;
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
        | _ -> error "incompatible"
      in
      tvar_set c ty)
  in
  unify a b
