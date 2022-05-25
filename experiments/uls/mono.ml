(** Monomorphizes ULS *)

open Syntax
open Solve

exception Mono_error of string

let fail s = raise (Mono_error s)

let concrete_type =
  let rec go t =
    match unlink t with
    | TVar _ -> false
    | TVal _ -> true
    | GUls _ -> false
    | UVar _ -> false
    | TLSet lset ->
        compact_lset lset;
        List.length lset.unspec = 0
    | TFn ((_, t1), tc, (_, t2)) -> go t1 && go tc && go t2
  in
  go

(** Clones a type t, breaking all refs. *)
let clone_type t =
  let rec go = function
    | UVar i -> (UVar i, IntMap.empty)
    | TVal v -> (TVal v, IntMap.empty)
    | TVar v -> (
        match !v with
        | Unbd n -> (TVar (ref (Unbd n)), IntMap.empty)
        | Link t ->
            let t', uls_v = go t in
            (TVar (ref (Link t')), uls_v))
    | TFn ((l1, t1), tc, (l2, t2)) ->
        let t1', uls_v1 = go t1 in
        let tclos', uls_v_clos = go tc in
        let t2', uls_v2 = go t2 in
        let uls_v = union_uls_v uls_v2 @@ union_uls_v uls_v1 uls_v_clos in
        (TFn ((l1, t1'), tclos', (l2, t2')), uls_v)
    | GUls { region; ty; proto } -> (GUls { region; ty; proto }, IntMap.empty)
    | TLSet lset ->
        let lset', uls_v = go_lset lset in
        (TLSet lset', uls_v)
  and go_lset { solved; unspec } =
    let unspec', uls_vs =
      List.split
      @@ List.map
           (fun unspec ->
             match !unspec with
             | Solved lset ->
                 let lset', uls_v = go_lset lset in
                 (ref (Solved lset'), uls_v)
             | Pending { region; ty; proto } ->
                 let ty', uls_v = go ty in
                 (ref (Pending { region; ty = ty'; proto }), uls_v))
           unspec
    in
    let uls_v = List.fold_left union_uls_v IntMap.empty uls_vs in
    ({ solved; unspec = unspec' }, uls_v)
  in

  go t

let clone_expr : e_expr -> e_expr * uls_of_var =
  let go_pat (l, t, p) =
    let p' = match p with PVal v -> PVal v | PVar x -> PVar x in
    let t', uls_v = clone_type t in
    ((l, t', p'), uls_v)
  in
  let rec go (l, t, e) =
    let e', uls_v =
      match e with
      | Val v -> (Val v, IntMap.empty)
      | Var x -> (Var x, IntMap.empty)
      | Let (x, e1, e2) ->
          let e1', uls_v1 = go e1 in
          let e2', uls_v2 = go e2 in
          (Let (x, e1', e2'), union_uls_v uls_v1 uls_v2)
      | Call (e1, e2) ->
          let e1', uls_v1 = go e1 in
          let e2', uls_v2 = go e2 in
          (Call (e1', e2'), union_uls_v uls_v1 uls_v2)
      | Clos (p, lam, e) ->
          let p', uls_p = go_pat p in
          let e', uls_e = go e in
          (Clos (p', lam, e'), union_uls_v uls_p uls_e)
      | Choice es ->
          let es', uls_vs = List.split @@ List.map go es in
          (Choice es', List.fold_left union_uls_v IntMap.empty uls_vs)
    in
    let t', uls_v1 = clone_type t in
    ((l, t', e'), union_uls_v uls_v uls_v1)
  in
  go

type ctx = {
  spec_table : spec_table;
  mutable var_specializations : ((string * ty) * string) list;
      (** original x, spec ty -> spec x *)
  mutable defs : (string * (string * e_expr)) list;
      (** source defs: real name -> (human name, body)
      "real name" is the lambda name if it exists, otherwise the human name *)
  mutable mono_defs : ((string * ty) * (string * e_expr)) list;
      (** monomorphized defs: original x, spec ty -> spec x, spec body *)
}

let specialize_var ctx x ty =
  match List.assoc_opt (x, ty) ctx.var_specializations with
  | Some x' -> x'
  | None ->
      let n =
        (List.length
        @@ List.filter (fun ((y, _), _) -> x = y) ctx.var_specializations)
        + 1
      in
      let x' = x ^ "~" ^ string_of_int n in
      ctx.var_specializations <- ((x, ty), x') :: ctx.var_specializations;
      x'

let remove_var_specializations ctx x =
  let spec, other =
    List.partition (fun ((y, _), _) -> x = y) ctx.var_specializations
  in
  ctx.var_specializations <- other;
  spec

let rec mono_def ctx x spec_ty =
  let num_spec_for_x =
    List.length @@ List.filter (fun ((y, _), _) -> x = y) ctx.mono_defs
  in
  let human_name, body = List.assoc x ctx.defs in
  let x' =
    (if x <> human_name then x ^ "(" ^ human_name ^ ")" else x)
    ^ "~"
    ^ string_of_int (num_spec_for_x + 1)
  in
  let spec_body, uls_v = clone_expr body in
  unify ctx.spec_table uls_v (xty body) spec_ty;
  let rec go ((_, t, e) as eexpr) =
    let error s = fail ("Mono error: " ^ s ^ " at " ^ string_of_expr eexpr) in
    let e' =
      match e with
      | Val v -> Val v
      | Var x -> (
          if not (concrete_type t) then
            error ("unspecialized var type " ^ string_of_ty [] t);
          match unlink t with
          | TFn (_, TLSet lset, _) -> (
              compact_lset lset;
              assert (List.length lset.unspec = 0);
              let choices =
                List.map
                  (fun lam ->
                    let x = string_of_lambda lam in
                    if List.mem_assoc x ctx.defs then
                      (* a known def *)
                      let x' = mono_def ctx x t in
                      Var x'
                    else
                      (* local var that needs specialization *)
                      Var (specialize_var ctx x t))
                  lset.solved
              in
              match choices with
              | [ one ] -> one
              | many -> Choice (List.map (fun e -> (noloc, t, e)) many))
          | _ -> Var (specialize_var ctx x t))
      | Call (e1, e2) -> Call (go e1, go e2)
      | Clos (pat, lam, body) ->
          assert (string_of_lambda lam = x);
          let body' = go body in
          Clos (pat, lam, body')
      | Choice es -> Choice (List.map go es)
      | Let ((_, x), e, body) ->
          let body' = go body in
          let needed_specializations = remove_var_specializations ctx x in
          List.fold_right
            (fun ((_, ty), x') body'' ->
              let e', uls_of_var = clone_expr e in
              unify ctx.spec_table uls_of_var (xty e') ty;
              let e' = go e' in
              (* wrap body as e_expr with type of the entire body [t] *)
              let body'' = (noloc, t, body'') in
              Let ((noloc, x'), e', body''))
            needed_specializations (xv body')
    in
    (noloc, t, e')
  in
  let specializations_before = ctx.var_specializations in
  ctx.var_specializations <- [];
  let spec_body' = go spec_body in
  if List.length ctx.var_specializations > 0 then
    fail
      ("Mono error: leftover specializations for " ^ String.concat ", "
      @@ List.map (fun ((x, _), _) -> x) ctx.var_specializations);
  ctx.var_specializations <- specializations_before;
  ctx.mono_defs <- ((x, spec_ty), (x', spec_body')) :: ctx.mono_defs;
  x'

(** Lifts closures to the toplevel, leaving their lambda name in their place.
    Also drops prototypes and assigns human names to lifted closures where
    possible. *)
let rec lift =
  let lift_e def_name =
    let rec go (l, t, e) =
      let e', lifted =
        match e with
        | Val v -> (Val v, [])
        | Var x -> (Var x, [])
        | Let (x, e, b) ->
            let e', l1 = go e in
            let b', l2 = go b in
            (Let (x, e', b'), l1 @ l2)
        | Call (e1, e2) ->
            let e1', l1 = go e1 in
            let e2', l2 = go e2 in
            (Call (e1', e2'), l1 @ l2)
        | Clos (p, lam, body) ->
            let lam_name = string_of_lam lam in
            let body', l = go body in
            let clos' = Clos (p, lam, body') in
            if lam_name = def_name then (* keep around for the def *) (clos', l)
            else
              let lifted = Def ((noloc, lam_name), (noloc, t, clos')) in
              (Var lam_name, lifted :: l)
        | Choice es ->
            let es', l = List.split @@ List.map go es in
            (Choice es', List.flatten l)
      in
      ((l, t, e'), lifted)
    in
    go
  in
  function
  | [] -> []
  | Proto _ :: rest -> lift rest
  | Def ((_, human_name), body) :: rest ->
      let real_name =
        match xv body with
        | Clos (_, lam, _) -> string_of_lam lam
        | _ -> human_name
      in
      let body', lifted = lift_e real_name body in
      (real_name, (human_name, body')) :: lift (lifted @ rest)

let mono program spec_table : program =
  let defs = lift program in
  let ctx = { spec_table; var_specializations = []; defs; mono_defs = [] } in
  List.iter
    (fun (x, (_, e)) ->
      if concrete_type (xty e) then
        let _x' = mono_def ctx x (xty e) in
        ())
    defs;
  let mono_defs = ctx.mono_defs in
  if List.length mono_defs = 0 then fail "No monomorphized roots found!";
  List.map (fun ((_, _), (x', e)) -> Def ((noloc, x'), e)) @@ List.rev mono_defs
