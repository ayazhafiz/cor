open Syntax

module IntMap = struct
  include Map.Make (struct
    type t = int

    let compare = compare
  end)
end

type spec_table = ((string * string) * (int * lset) list) list
(** Specialization table : (general var, spec type, proto) -> (region -> spec lset) *)

let add_spec (spec_type, proto, regions) (spec_table : spec_table) =
  ((spec_type, proto), regions) :: spec_table

type uls_of_var = unspec ref list IntMap.t
(** specialization var -> (unspecialized lambda sets) *)

let union_uls_v =
  IntMap.union (fun _ unspec1 unspec2 ->
      Some (List.sort_uniq compare (unspec1 @ unspec2)))

exception Solve_err of string

let failsolve s = raise (Solve_err s)

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
    | TFn ((_, t1), c, (_, t2)) -> go t1 || go c || go t2
  in
  go

let unify (spec_table : spec_table) (gen_of_inst : uls_of_var) a b =
  let error prefix =
    failsolve
      ("Unify error: " ^ prefix ^ " at " ^ string_of_ty [] a ^ " ~ "
     ^ string_of_ty [] b)
  in
  let rec unify a b =
    match (unlink a, unlink b) with
    | TVar x, t | t, TVar x -> (
        match !x with
        | Link _ -> error "found a link where none was expected"
        | Unbd n -> (
            if occurs n t then error "occurs" else x := Link t;
            match (unlink t, IntMap.find_opt n gen_of_inst) with
            | TVal spec_sym, Some unspec_lsets ->
                List.iter
                  (fun unspec ->
                    match !unspec with
                    | Solved _ -> ()
                    | Pending { region; ty; proto }
                      when unlink ty = TVal spec_sym ->
                        let spec_of_region =
                          List.assoc (spec_sym, proto) spec_table
                        in
                        let lset = List.assoc region spec_of_region in
                        unspec := Solved lset
                    | Pending _ -> ())
                  unspec_lsets
            | _ -> ()))
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
    | _ -> error "incompatible types"
  in
  unify a b

let inst ?(proto_spec = false)
    (* whether we're instantiating for proto specialization *) fresh t :
    ty * uls_of_var =
  let tenv = ref [] in
  let rec inst = function
    | UVar x ->
        if not (List.mem_assoc x !tenv) then tenv := (x, fresh ()) :: !tenv;
        (List.assoc x !tenv, IntMap.empty)
    | TVar x -> (
        match !x with
        | Unbd _ -> (TVar x, IntMap.empty)
        | Link t ->
            let t', uls_v = inst t in
            (TVar (ref (Link t')), uls_v))
    | TVal v -> (TVal v, IntMap.empty)
    | TFn ((l1, t1), tclos, (l2, t2)) ->
        let t1', uls_v1 = inst t1 in
        let tclos', uls_v_clos = inst tclos in
        let t2', uls_v2 = inst t2 in
        ( TFn ((l1, t1'), tclos', (l2, t2')),
          union_uls_v uls_v2 @@ union_uls_v uls_v1 uls_v_clos )
    | TLSet lset when proto_spec ->
        assert (lset.solved = [] && List.length lset.unspec = 1);
        (TLSet { solved = []; unspec = [] }, IntMap.empty)
    | TLSet lset ->
        let lset', uls_v = inst_lset lset in
        (TLSet lset', uls_v)
  and inst_lset { solved; unspec } =
    let unspec', uls_vs =
      List.split
      @@ List.map
           (fun unspec ->
             match !unspec with
             | Solved lset ->
                 let lset', uls_v = inst_lset lset in
                 (ref (Solved lset'), uls_v)
             | Pending { region; ty; proto } ->
                 let ty', uls_v = inst ty in
                 let unspec' = ref (Pending { region; ty = ty'; proto }) in
                 let uls_v' =
                   if List.exists (fun (_, b) -> b = unlink ty') !tenv then
                     (* instantiated generalized *)
                     let inst_n =
                       match unlink ty' with
                       | TVar r -> (
                           match !r with Unbd n -> n | _ -> assert false)
                       | _ -> assert false
                     in
                     IntMap.singleton inst_n [ unspec' ]
                   else IntMap.empty
                 in
                 (unspec', union_uls_v uls_v uls_v'))
           unspec
    in
    let uls_v = List.fold_left union_uls_v IntMap.empty uls_vs in
    ({ solved; unspec = unspec' }, uls_v)
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
    | TLSet lset -> TLSet (go_lset lset)
    | TFn ((l1, t1), c, (l2, t2)) -> TFn ((l1, go t1), go c, (l2, go t2))
  and go_lset { solved; unspec } =
    let unspec' =
      List.map
        (fun unspec ->
          ref
            (match !unspec with
            | Solved lset -> Solved (go_lset lset)
            | Pending { region; ty; proto } ->
                Pending { region; ty = go ty; proto }))
        unspec
    in
    { solved; unspec = unspec' }
  in
  go

let infer spec_table fresh =
  let noloc ty = (noloc, ty) in
  let gen_of_inst = ref IntMap.empty in
  let rec infer venv (_, t, e) =
    let ty =
      match e with
      | Val v ->
          unify spec_table !gen_of_inst t (TVal v);
          t
      | Var x -> (
          match List.assoc_opt x venv with
          | Some t ->
              let t, gen_of_inst1 = inst fresh t in
              gen_of_inst := union_uls_v !gen_of_inst gen_of_inst1;
              t
          | None -> failsolve ("Variable " ^ x ^ " not in scope"))
      | Let ((_, x), e, b) ->
          let t_x = generalize venv @@ infer venv e in
          infer ((x, t_x) :: venv) b
      | Call (fn, arg) ->
          let t_ret = fresh () in
          let t_clos = fresh () in
          let t_arg = infer venv arg in
          let t_fn = infer venv fn in
          unify spec_table !gen_of_inst
            (TFn (noloc t_arg, t_clos, noloc t_ret))
            t_fn;
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
              unify spec_table !gen_of_inst t t_e)
            choices;
          t
    in
    unify spec_table !gen_of_inst t ty;
    ty
  in
  infer

(** [resolve_specialization p a s] takes a prototype [p], its specialization
    variable [a], a specialization [s]. It finds what value-type [s] is
    specialized for, and the lambda sets in [s] associated
    with the generalized lambda sets present in the prototype [p]. *)
let resolve_specialization p a s =
  let assoc_lset = function
    | TLSet { solved = []; unspec = [ unspec ] }, TLSet spec -> (
        match !unspec with
        | Pending { region; ty = UVar _; _ } -> (region, spec)
        | _ -> failsolve "unspec in proto is solved somehow")
    | proto, spec ->
        failsolve
          ("something weird ended up in proto, spec lsets. Proto: "
         ^ string_of_ty [] proto ^ " Spec: " ^ string_of_ty [] spec)
  in
  let spec_a = ref None in
  let rec go p s =
    if unlink p <> p then failsolve "p has links";
    match (p, unlink s) with
    | TFn ((_, t11), c1, (_, t12)), TFn ((_, t21), c2, (_, t22)) ->
        (* By construction in parsing: we expect this closure to be regioned first,
           then the LHS, then the RHS *)
        assoc_lset (c1, c2) :: (go t11 t21 @ go t12 t22)
    | UVar b, TVal v when a = b ->
        spec_a := Some v;
        []
    | UVar b, spec when a = b ->
        failsolve
          ("found specialization for non-value type " ^ string_of_ty [] spec)
    | _, TVar _ | UVar _, _ -> []
    | TVal _, _ | _, TVal _ -> []
    | TFn _, _ | _, TFn _ -> failsolve "don't unify"
    | TVar _, _ -> failsolve "var ended up in proto"
    | TLSet _, _ -> failsolve "should always be covered in assoc_lset"
  in
  let table = go p s in
  let sorted_table =
    List.sort_uniq (fun (r1, _) (r2, _) -> compare r1 r2) table
  in
  if table <> sorted_table then
    failsolve "Created lset table has duplicates or is unsorted!";
  match !spec_a with
  | None -> failsolve "proto is not specialized!"
  | Some spec_a -> (spec_a, table)

let infer_program fresh program =
  let rec go venv proto_table (spec_table : spec_table) = function
    | [] -> spec_table
    | it :: rest ->
        let venv', proto_table', spec_table' =
          match it with
          | Proto ((_, x), (t_a, a), (_, t_proto)) ->
              let venv' = (x, t_proto) :: venv in
              let proto_table' = (x, ((t_a, a), t_proto)) :: proto_table in
              (venv', proto_table', spec_table)
          | Def ((_, x), e, _) ->
              let t_x = generalize venv @@ infer spec_table fresh venv e in
              let venv', spec_table' =
                match List.assoc_opt x proto_table with
                | Some ((t_a, _a), t_proto) ->
                    (* specialization def; first unify with an instantiated
                       version of the proto so we know the shape is correct *)
                    let proto = x in
                    let inst_proto, gen_of_inst =
                      inst ~proto_spec:true fresh t_proto
                    in
                    unify spec_table gen_of_inst t_x inst_proto;
                    (* now, line up all the generalized lambda sets with the
                       specialized ones *)
                    let spec_a, specializations =
                      resolve_specialization t_proto t_a t_x
                    in
                    (venv, add_spec (spec_a, proto, specializations) spec_table)
                | None ->
                    (* non-specialization def, no spec update *)
                    ((x, t_x) :: venv, spec_table)
              in
              (venv', proto_table, spec_table')
        in
        go venv' proto_table' spec_table' rest
  in
  go [] [] [] program
