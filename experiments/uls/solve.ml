open Syntax

module IntMap = struct
  include Map.Make (struct
    type t = int

    let compare = compare
  end)
end

type spec_table = ((string * string) * (int * ty) list) list
(** Specialization table : (spec type, proto) -> (region -> ambient function) *)

let add_spec (spec_type, proto, regions) (spec_table : spec_table) =
  ((spec_type, proto), regions) :: spec_table

type uls_link = { unspec : unspec ref; ambient : ty }

type uls_of_var = uls_link list IntMap.t
(** specialization var -> (unspecialized lambda set, ambient var) list *)

let union_uls_of_vars : uls_of_var -> uls_of_var -> uls_of_var =
  IntMap.union (fun _ unspec1 unspec2 ->
      Some (List.sort_uniq compare (unspec1 @ unspec2)))

exception Solve_err of string

let failsolve s = raise (Solve_err s)

(** resolve a linked type *)
let rec unlink = function
  | TVar v as t -> ( match !v with Unbd _ -> t | Link t -> unlink t)
  | t -> t

let islinked = function TVar _ -> true | _ -> false

let occurs x =
  let rec go = function
    | TVar t -> ( match !t with Unbd n -> n = x | Link t -> go t)
    | UVar _ -> false
    | TVal _ -> false
    | TLSet { solved = _; unspec; ambient = _ } ->
        List.exists
          (fun unspec ->
            match !unspec with Solved _ -> false | Pending { ty; _ } -> go ty)
          unspec
    | TFn ((_, t1), c, (_, t2)) -> go t1 || go c || go t2
  in
  go

let inst ?(proto_spec = false)
    (* whether we're instantiating for proto specialization *) fresh t :
    ty * uls_of_var =
  let freshened = ref [] in
  let rec inst = function
    | UVar x ->
        if not (List.mem_assoc x !freshened) then
          freshened := (x, fresh ()) :: !freshened;
        (List.assoc x !freshened, IntMap.empty)
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
          union_uls_of_vars uls_v2 @@ union_uls_of_vars uls_v1 uls_v_clos )
    | TLSet lset when proto_spec ->
        assert (lset.solved = [] && List.length lset.unspec = 1);
        ( TLSet { solved = []; unspec = []; ambient = lset.ambient },
          IntMap.empty )
    | TLSet lset ->
        let lset', uls_v = inst_lset lset in
        (TLSet lset', uls_v)
  and inst_lset { solved; unspec; ambient } =
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
                 let uls = { unspec = unspec'; ambient = !ambient } in
                 let uls_v' =
                   if List.exists (fun (_, b) -> b = unlink ty') !freshened then
                     (* instantiated generalized *)
                     let inst_n =
                       match unlink ty' with
                       | TVar r -> (
                           match !r with Unbd n -> n | _ -> assert false)
                       | _ -> assert false
                     in
                     IntMap.singleton inst_n [ uls ]
                   else IntMap.empty
                 in
                 (unspec', union_uls_of_vars uls_v uls_v'))
           unspec
    in
    let uls_v = List.fold_left union_uls_of_vars IntMap.empty uls_vs in
    ({ solved; unspec = unspec'; ambient }, uls_v)
  in
  inst t

let rec compact_lambda_set fresh uls_of_var spec_table spec_sym unspec_lsets =
  List.iter
    (fun { unspec; ambient } ->
      match !unspec with
      | Solved _ -> ()
      | Pending { region; ty; proto } when unlink ty = TVal spec_sym ->
          let ambient_of_region = List.assoc (spec_sym, proto) spec_table in
          (* remove the unspec lambda from the lambda set whose ambient function
             is about to be unified with the specialization region's ambient function *)
          unspec := Solved { solved = []; unspec = []; ambient = ref ambient };
          (* unify the ambient function of this pending lambda's set with the
             ambient function of the target lambda set *)
          let specialized_ambient = List.assoc region ambient_of_region in
          let specialized_ambient, uls_of_var' =
            inst ~proto_spec:false fresh specialized_ambient
          in
          uls_of_var := union_uls_of_vars !uls_of_var uls_of_var';
          print_endline
            (string_of_ty [] ambient ^ " ~~ "
            ^ string_of_ty [] specialized_ambient);
          unify fresh spec_table uls_of_var ambient specialized_ambient;
          print_endline "1"
      | Pending _ -> ())
    unspec_lsets

and unify fresh (spec_table : spec_table) (uls_of_var : uls_of_var ref) a b =
  let rec unify a b =
    let error prefix =
      failsolve
        ("Unify error: " ^ prefix ^ " at " ^ string_of_ty [] a ^ " ~ "
       ^ string_of_ty [] b)
    in
    match (unlink a, unlink b) with
    | TVar x, t | t, TVar x -> (
        match !x with
        | Link _ -> error "found a link where none was expected"
        | Unbd n -> (
            if occurs n t then error "occurs" else x := Link t;
            match (unlink t, IntMap.find_opt n !uls_of_var) with
            | TVal spec_sym, Some unspec_lsets ->
                compact_lambda_set fresh uls_of_var spec_table spec_sym
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
            solved = List.sort_uniq compare @@ ls1.solved @ ls2.solved;
            unspec = List.sort_uniq compare @@ ls1.unspec @ ls2.unspec;
            ambient = ls1.ambient;
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
  and go_lset { solved; unspec; ambient } =
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
    { solved; unspec = unspec'; ambient }
  in
  go

let infer spec_table fresh =
  let noloc ty = (noloc, ty) in
  let uls_of_var = ref IntMap.empty in
  let rec infer venv (_, t, e) =
    let ty =
      match e with
      | Val v ->
          unify fresh spec_table uls_of_var t (TVal v);
          t
      | Var x -> (
          match List.assoc_opt x venv with
          | Some t ->
              let t, uls_of_var1 = inst fresh t in
              uls_of_var := union_uls_of_vars !uls_of_var uls_of_var1;
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
          unify fresh spec_table uls_of_var
            (TFn (noloc t_arg, t_clos, noloc t_ret))
            t_fn;
          t_ret
      | Clos ((_, t_x, x), lam, body) ->
          let venv' =
            match x with PVal _ -> venv | PVar x -> (x, t_x) :: venv
          in
          let t_body = infer venv' body in
          let t_fn = ref (TVal "") in
          let lset = { solved = [ lam ]; unspec = []; ambient = t_fn } in
          let t_clos = TLSet lset in
          t_fn := TFn (noloc t_x, t_clos, noloc t_body);
          !t_fn
      | Choice choices ->
          let t = fresh () in
          List.iter
            (fun e ->
              let t_e = infer venv e in
              unify fresh spec_table uls_of_var t t_e)
            choices;
          t
    in
    unify fresh spec_table uls_of_var t ty;
    ty
  in
  infer

(** [resolve_specialization p a s] takes a prototype [p], its specialization
    variable [a], a specialization [s]. It finds what value-type [s] is
    specialized for, and the ambient functions of the lambda sets in [s] associated
    with the generalized lambda sets present in the prototype [p]. *)
let resolve_specialization p a s =
  let assoc_lset = function
    | ( TLSet { solved = []; unspec = [ unspec ]; ambient = _ },
        TLSet { solved = _; unspec = _; ambient = spec_ambient } ) -> (
        match !unspec with
        | Pending { region; ty = UVar _; _ } -> (region, !spec_ambient)
        | _ -> failsolve "unspec in proto is solved somehow")
    | proto, spec ->
        failsolve
          ("something weird ended up in proto, spec lsets. Proto: "
         ^ string_of_ty [] proto ^ " Spec: " ^ string_of_ty [] spec)
  in
  let spec_a = ref None in
  let rec go p s =
    if islinked p then failsolve "p has links";
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
  if List.map fst table <> List.map fst sorted_table then
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
          | Proto { name = _, x; arg; sig' = _, t_proto; bound_vars } ->
              let venv' = (x, t_proto) :: venv in
              let arg_var = List.assoc arg bound_vars in
              let proto_table' =
                (x, ((arg_var, arg), t_proto)) :: proto_table
              in
              (venv', proto_table', spec_table)
          | Def ((_, x), e, _) ->
              print_endline x;
              let t_x = generalize venv @@ infer spec_table fresh venv e in
              let venv', spec_table' =
                match List.assoc_opt x proto_table with
                | Some ((t_a, _a), t_proto) ->
                    (* specialization def; first unify with an instantiated
                       version of the proto so we know the shape is correct *)
                    let proto = x in
                    let inst_proto, uls_of_var =
                      inst ~proto_spec:true fresh t_proto
                    in
                    unify fresh spec_table (ref uls_of_var) t_x inst_proto;
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
