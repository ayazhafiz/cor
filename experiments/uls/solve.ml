open Syntax

(** resolve a linked type *)
let rec unlink = function
  | TVar v as t -> ( match !v with Unbd _ -> t | Link t -> unlink t)
  | t -> t

let occurs x =
  let rec go = function
    | TVar t -> ( match !t with Unbd n -> n = x | Link t -> go t)
    | UVar _ -> false
    | TVal _ -> false
    | TLSet { solved = _; unspec } ->
        List.exists
          (fun unspec ->
            match !unspec with Solved _ -> false | Pending { ty; _ } -> go ty)
          unspec
    | GUls _ -> false
    | TFn ((_, t1), c, (_, t2)) -> go t1 || go c || go t2
  in
  go

let rec unify a b =
  let error prefix =
    failwith
      ("Unify error: " ^ prefix ^ " at " ^ string_of_ty [] a ^ " ~ "
     ^ string_of_ty [] b)
  in
  match (unlink a, unlink b) with
  | TVar x, t | t, TVar x -> (
      match !x with
      | Link _ -> error "found a link where none was expected"
      | Unbd n -> if occurs n t then error "occurs" else x := Link t)
  | TFn ((_, t11), c1, (_, t12)), TFn ((_, t21), c2, (_, t22)) ->
      unify t11 t21;
      unify t12 t22;
      unify c1 c2
  | UVar _, _ | _, UVar _ -> error "attempting to unify generalization"
  | TVal v1, TVal v2 -> if v1 <> v2 then error "differing values"
  | TLSet ls1, TLSet ls2 ->
      let new_lset =
        {
          solved = ls1.solved @ ls2.solved;
          unspec = List.sort_uniq compare @@ ls1.unspec @ ls2.unspec;
        }
      in
      compact_lset new_lset;
      (* commit the new solved to the respective lsets *)
      let commit lset =
        lset.solved <- new_lset.solved;
        lset.unspec <- new_lset.unspec
      in
      commit ls1;
      commit ls2
  | GUls _, _ | _, GUls _ -> error "attempting to unify generalized lambda sets"
  | _ -> error "incompatible types"

let inst fresh t =
  let tenv = ref [] in
  let rec inst = function
    | UVar x ->
        if not (List.mem_assoc x !tenv) then tenv := (x, fresh ()) :: !tenv;
        List.assoc x !tenv
    | GUls { region; ty; proto } ->
        if not (List.mem_assoc ty !tenv) then tenv := (ty, fresh ()) :: !tenv;
        let ty' = List.assoc ty !tenv in
        TLSet
          {
            solved = [];
            unspec = [ ref (Pending { region; ty = ty'; proto }) ];
          }
    | TVar x -> TVar x
    | TVal v -> TVal v
    | TFn ((l1, t1), tclos, (l2, t2)) ->
        TFn ((l1, inst t1), inst tclos, (l2, inst t2))
    | TLSet { unspec; solved = _ } as t ->
        List.iter
          (fun unspec ->
            match !unspec with
            | Solved _ -> ()
            | Pending { ty; _ } ->
                let ty' = inst ty in
                if ty <> ty' then
                  failwith
                    ("Inst error: found a generalized type in an \
                      non-generalized lset: " ^ string_of_ty [] t))
          unspec;
        t
  in
  inst t

let generalize venv =
  let rec go = function
    | TVar x as ty -> (
        match !x with
        | Link t -> TVar (ref (Link (go t)))
        | Unbd n ->
            if List.exists (fun (_, t) -> occurs n t) venv then ty
              (* variable occurs in env, don't generalize *)
            else UVar n (* variable is new, generalize *))
    | TVal v -> TVal v
    | UVar n -> UVar n (* stays generalized *)
    | GUls uls -> GUls uls (* stays generalized *)
    | TLSet { solved = _; unspec } as tlset ->
        List.iter
          (fun spec ->
            match !spec with
            | Solved _ -> ()
            | Pending { ty; _ } ->
                let ty' = go ty in
                if ty <> ty' then
                  failwith
                    ("Generalization error: lsets can only be non-generalized \
                      but a type was generalize: " ^ string_of_ty [] tlset))
          unspec;
        tlset
    | TFn ((l1, t1), c, (l2, t2)) -> TFn ((l1, go t1), go c, (l2, go t2))
  in
  go

let infer fresh e =
  let noloc ty = (noloc, ty) in
  let rec infer venv (_, t, e) =
    match e with
    | Val v ->
        unify t (TVal v);
        t
    | Var x -> (
        match List.assoc_opt x venv with
        | Some t -> inst fresh t
        | None -> failwith ("Variable " ^ x ^ " not in scope"))
    | Let ((_, x), e, b) ->
        let t_x = generalize venv @@ infer venv e in
        infer ((x, t_x) :: venv) b
    | Call (fn, arg) ->
        let t_ret = fresh () in
        let t_clos = fresh () in
        let t_arg = infer venv arg in
        let t_fn = infer venv fn in
        unify (TFn (noloc t_arg, t_clos, noloc t_ret)) t_fn;
        t_ret
    | Clos ((_, t_x, x), lam, body) ->
        let venv' =
          match x with PVal _ -> venv | PVar x -> (x, t_x) :: venv
        in
        let t_body = infer venv' body in
        let lset = { solved = [ lam ]; unspec = [] } in
        let t_clos = TLSet lset in
        TFn (noloc t_x, t_clos, noloc t_body)
    | Choice choices ->
        let t = fresh () in
        List.iter
          (fun e ->
            let t_e = infer venv e in
            unify t t_e)
          choices;
        t
  in
  infer [] e
