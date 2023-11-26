open Symbol
open Can
open Solve
open Type
open Mono

type queue = val_specialization list
type spec_procs = ready_specialization list
type fenv = (symbol * [ `Fn of letfn | `Val of letval ]) list

let symbol_of_needed_specialization : val_specialization -> symbol * tvar =
 fun (`Val (Letval { bind = t_x, x; _ })) -> (x, t_x)

let find_entry_points defs =
  let rec go = function
    | [] -> []
    | Run { bind = t_x, x; _ } :: rest -> (x, t_x) :: go rest
    | _ :: rest -> go rest
  in
  go defs

let find_toplevel_values : def list -> val_specialization list =
 fun defs ->
  let rec go = function
    | [] -> []
    | Run { bind; body; sig_ } :: rest ->
        let letval = Letval { bind; body; sig_ } in
        `Val letval :: go rest
    | _ :: rest -> go rest
  in
  go defs

let find_fenv : def list -> fenv =
 fun defs ->
  let rec go : fenv -> def list -> fenv =
   fun fenv -> function
    | [] -> fenv
    | (Def { kind = `Letfn letfn } as def) :: rest ->
        let x = name_of_def def in
        go ((x, `Fn letfn) :: fenv) rest
    | (Def { kind = `Letval letval } as def) :: rest ->
        let x = name_of_def def in
        go ((x, `Val letval) :: fenv) rest
    | _ :: rest -> go fenv rest
  in
  go [] defs

type type_cache = (variable * tvar) list ref

let clone_type : fresh_tvar -> type_cache -> tvar -> tvar =
 fun fresh_tvar cache tvar ->
  let rec go_loc : loc_tvar -> loc_tvar = fun (l, t) -> (l, go t)
  and go : tvar -> tvar =
   fun tvar ->
    let { var; ty; recur } = unlink tvar in
    match List.assoc_opt var !cache with
    | Some tvar -> tvar
    | None ->
        let tvar' = fresh_tvar @@ Unbd None in
        tvar_set_recur tvar' !recur;
        cache := (var, tvar') :: !cache;

        let real_ty_content =
          match !ty with
          | Link _ -> failwith "clone_type: Link"
          | Unbd x -> Unbd x
          | ForA x -> Unbd x
          | Content (TPrim (`Unit | `Str | `Int)) -> !ty
          | Content TTagEmpty -> Content TTagEmpty
          | Content (TTag { tags; ext = loc_ext, ty_ext }) ->
              let go_tag : ty_tag -> ty_tag =
               fun (tag, args) -> (tag, List.map go_loc args)
              in
              let ext = (loc_ext, go ty_ext) in
              let tags = List.map go_tag tags in
              Content (TTag { tags; ext })
          | Content (TFn (t1, t2)) ->
              let t1 = go_loc t1 in
              let t2 = go_loc t2 in
              Content (TFn (t1, t2))
          | Alias { alias = sym, args; real } ->
              let args = List.map go_loc args in
              let real = go real in
              Alias { alias = (sym, args); real }
        in

        tvar_set tvar' real_ty_content;
        tvar'
  in
  go tvar

let bind_of_fenv = function
  | `Fn (Letfn { bind; _ }) -> bind
  | `Val (Letval { bind; _ }) -> bind

let rec create_specialization ~(ctx : Ir.ctx) ~specs ~fenv ~kind ~new_sym
    ~type_cache ~t_x =
  match kind with
  | `Fn (Letfn { recursive; bind = _; arg = t_a, a; body; sig_; captures }) ->
      let t_a = clone_type ctx.fresh_tvar type_cache t_a in
      let body, needed = clone_expr ~ctx ~specs ~fenv ~type_cache ~expr:body in
      let sig_ = Option.map (clone_type ctx.fresh_tvar type_cache) sig_ in
      let captures, captures_needed =
        clone_captures ~ctx ~specs ~fenv ~type_cache ~captures
      in
      let bind = (t_x, new_sym) in
      let arg = (t_a, a) in
      let letfn = Letfn { recursive; bind; arg; body; sig_; captures } in
      let spec_procs = needed @ captures_needed @ [ `Letfn letfn ] in
      (new_sym, spec_procs)
  | `Val (Letval { bind = _; body; sig_ }) ->
      let body, needed = clone_expr ~ctx ~specs ~fenv ~type_cache ~expr:body in
      let sig_ = Option.map (clone_type ctx.fresh_tvar type_cache) sig_ in

      let letval = Letval { bind = (t_x, new_sym); body; sig_ } in
      let spec_procs = needed @ [ `Letval letval ] in
      (new_sym, spec_procs)

and find_specialization ~(ctx : Ir.ctx) ~specs ~fenv ~kind ~t_needed =
  let type_cache = ref [] in

  let t_x, x = bind_of_fenv kind in
  let t_x = clone_type ctx.fresh_tvar type_cache t_x in
  unify ctx.symbols "find_specialization" ctx.fresh_tvar t_x t_needed;

  let new_sym, spec_kind = Mono_symbol.add_specialization ~ctx specs x t_x in

  match spec_kind with
  | `Existing -> (new_sym, [])
  | `New ->
      create_specialization ~ctx ~specs ~fenv ~kind ~t_x ~new_sym ~type_cache

and clone_captures ~(ctx : Ir.ctx) ~specs ~fenv ~type_cache ~captures :
    typed_symbol list * spec_procs =
  let go_capture (t_x, x) =
    let x, needed =
      clone_expr ~ctx ~specs ~fenv ~type_cache ~expr:(t_x, Var x)
    in
    let t_x, x =
      match x with t, Var x -> (t, x) | _ -> failwith "impossible"
    in
    ((t_x, x), needed)
  in
  let captures, needed = List.split @@ List.map go_capture captures in
  (captures, List.concat needed)

and clone_expr ~(ctx : Ir.ctx) ~specs ~fenv ~type_cache ~expr :
    e_expr * spec_procs =
  let rec go_pat : e_pat -> e_pat * spec_procs =
   fun (t, p) ->
    let t = clone_type ctx.fresh_tvar type_cache t in
    let p, needed =
      match p with
      | PVar x -> (PVar x, [])
      | PTag (tag, args) ->
          let args, needed = List.split @@ List.map go_pat args in
          (PTag (tag, args), List.concat needed)
    in
    ((t, p), needed)
  and go_branch : branch -> branch * spec_procs =
   fun (p, e) ->
    let p, p_needed = go_pat p in
    let e, e_needed = go e in
    ((p, e), p_needed @ e_needed)
  and go : e_expr -> e_expr * spec_procs =
   fun (t, e) ->
    let t = clone_type ctx.fresh_tvar type_cache t in
    let e, needed =
      match e with
      | Str s -> (Str s, [])
      | Int i -> (Int i, [])
      | Unit -> (Unit, [])
      | Var x -> (
          match List.assoc_opt x fenv with
          | Some kind ->
              let new_x, spec_procs =
                find_specialization ~ctx ~specs ~fenv ~kind ~t_needed:t
              in
              (Var new_x, spec_procs)
          | None -> (Var x, []))
      | Tag (t, es) ->
          let es, needed = List.split @@ List.map go es in
          (Tag (t, es), List.concat needed)
      | Let (Letval { bind = t_x, x; body; sig_ }, rest) ->
          let t_x = clone_type ctx.fresh_tvar type_cache t_x in
          let body, b_needed = go body in
          let rest, r_needed = go rest in
          let sig_ = Option.map (clone_type ctx.fresh_tvar type_cache) sig_ in
          ( Let (Letval { bind = (t_x, x); body; sig_ }, rest),
            b_needed @ r_needed )
      | LetFn
          ( Letfn
              { recursive; bind = t_x, x; arg = t_a, a; body; sig_; captures },
            rest ) ->
          let t_x = clone_type ctx.fresh_tvar type_cache t_x in
          let bind = (t_x, x) in
          let t_a = clone_type ctx.fresh_tvar type_cache t_a in
          let arg = (t_a, a) in
          let body, b_needed = go body in
          let rest, r_needed = go rest in
          let sig_ = Option.map (clone_type ctx.fresh_tvar type_cache) sig_ in
          let captures, c_needed =
            clone_captures ~ctx ~specs ~fenv ~type_cache ~captures
          in
          let needed = b_needed @ r_needed @ c_needed in
          let letfn = Letfn { recursive; bind; arg; body; sig_; captures } in
          (LetFn (letfn, rest), needed)
      | Clos { arg = t_a, a; body; captures } ->
          let t_a = clone_type ctx.fresh_tvar type_cache t_a in
          let body, b_needed = go body in
          let captures, c_needed =
            clone_captures ~ctx ~specs ~fenv ~type_cache ~captures
          in
          (Clos { arg = (t_a, a); body; captures }, b_needed @ c_needed)
      | Call (e1, e2) ->
          let e1, e1_needed = go e1 in
          let e2, e2_needed = go e2 in
          (Call (e1, e2), e1_needed @ e2_needed)
      | KCall (kfn, es) ->
          let es, needed = List.split @@ List.map go es in
          (KCall (kfn, es), List.concat needed)
      | When (e, branches) ->
          let e, e_needed = go e in
          let branches, branches_needed =
            List.split @@ List.map go_branch branches
          in
          let branches_needed = List.concat branches_needed in
          (When (e, branches), e_needed @ branches_needed)
    in
    ((t, e), needed)
  in
  go expr

let specialize_queue ~(ctx : Ir.ctx) ~specs ~fenv ~queue =
  let specialize_let_val (Letval { bind = t_x, _old_sym; body; sig_ }) ~t_needed
      ~new_sym =
    let type_cache : type_cache = ref [] in
    let t_x = clone_type ctx.fresh_tvar type_cache t_x in
    unify ctx.symbols "specialize" ctx.fresh_tvar t_x t_needed;

    let body, needed = clone_expr ~ctx ~specs ~fenv ~type_cache ~expr:body in
    let sig_ = Option.map (clone_type ctx.fresh_tvar type_cache) sig_ in

    let letval = Letval { bind = (t_x, new_sym); body; sig_ } in
    (letval, needed)
  in
  let rec go : queue -> ready_specialization list = function
    | [] -> []
    | `Val letval :: rest ->
        let (Letval { bind = t_x, x; _ }) = letval in
        let letval, specs =
          specialize_let_val letval ~t_needed:t_x ~new_sym:x
        in
        (specs @ [ `Letval letval ]) @ go rest
  in
  go queue

let specialize : Ir.ctx -> Can.program -> specialized =
 fun ctx program ->
  let specs = Mono_symbol.make () in
  let entry_point_symbols = find_entry_points program in
  let toplevel_values = find_toplevel_values program in
  let fenv = find_fenv program in
  let queue = List.map (function `Val ep -> `Val ep) toplevel_values in
  let specializations = specialize_queue ~ctx ~specs ~fenv ~queue in
  { specializations; entry_points = entry_point_symbols }
