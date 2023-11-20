open Symbol
open Syntax
open Solve

type ready_specialization = [ `Ready of symbol * e_expr * tvar ]
type needed_specialization = [ `Needed of symbol * symbol * tvar ]
type queue = needed_specialization list
type fenv = (symbol * e_expr) list

let symbol_of_needed_specialization : needed_specialization -> symbol =
 fun (`Needed (sym, _, _)) -> sym

let find_entry_points : e_def list -> needed_specialization list =
 fun defs ->
  let rec go = function
    | [] -> []
    | (_, tvar, Run ((_, x), _)) :: rest -> `Needed (x, x, tvar) :: go rest
    | _ :: rest -> go rest
  in
  go defs

let find_fenv : e_def list -> fenv =
 fun defs ->
  let rec go : fenv -> e_def list -> fenv =
   fun fenv -> function
    | [] -> fenv
    | (_, _, (Def ((_, x), e) | Run ((_, x), e))) :: rest ->
        go ((x, e) :: fenv) rest
    | _ :: rest -> go fenv rest
  in
  go [] defs

type type_cache = (variable * tvar) list ref

let clone_type : type_cache -> tvar -> tvar =
 fun cache tvar ->
  let rec go_loc : loc_tvar -> loc_tvar = fun (l, t) -> (l, go t)
  and go : tvar -> tvar =
   fun { var; ty; recur } ->
    match List.assoc_opt var !cache with
    | Some tvar -> tvar
    | None ->
        let ty_cell = ref @@ Unbd None in
        let tvar' = { var; ty = ty_cell; recur = ref !recur } in
        cache := (var, tvar') :: !cache;

        let real_ty_content =
          match !ty with
          | Link t -> Link (go t)
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

        ty_cell := real_ty_content;

        tvar'
  in
  go tvar

type ctx = { symbols : Symbol.t; fresh_tvar : fresh_tvar }

let clone_expr : ctx -> fenv -> e_expr -> e_expr * queue =
 fun ctx fenv expr ->
  let type_cache : type_cache = ref [] in
  let rec go_pat : e_pat -> e_pat * queue =
   fun (l, t, p) ->
    let t = clone_type type_cache t in
    let p, needed =
      match p with
      | PVar (l_x, x) -> (PVar (l_x, x), [])
      | PTag ((l_tag, tag), args) ->
          let args, needed = List.split @@ List.map go_pat args in
          (PTag ((l_tag, tag), args), List.concat needed)
    in
    ((l, t, p), needed)
  and go_branch : branch -> branch * queue =
   fun (p, e) ->
    let p, p_needed = go_pat p in
    let e, e_needed = go e in
    ((p, e), p_needed @ e_needed)
  and go : e_expr -> e_expr * queue =
   fun (l, t, e) ->
    let t = clone_type type_cache t in
    let e, needed =
      match e with
      | Str s -> (Str s, [])
      | Int i -> (Int i, [])
      | Var x -> (
          match List.assoc_opt x fenv with
          | Some _ ->
              let new_x =
                ctx.symbols.fresh_symbol_named (Symbol.syn_of ctx.symbols x)
              in
              (Var new_x, [ `Needed (new_x, x, t) ])
          | None -> (Var x, []))
      | Tag (t, es) ->
          let es, needed = List.split @@ List.map go es in
          (Tag (t, es), List.concat needed)
      | Let (letrec, (l_x, (l_tx, tx), x), e, b) ->
          let tx = clone_type type_cache tx in
          let e, e_needed = go e in
          let b, b_needed = go b in
          (Let (letrec, (l_x, (l_tx, tx), x), e, b), e_needed @ b_needed)
      | Clos ((l_a, (l_ta, ta), a), b) ->
          let ta = clone_type type_cache ta in
          let b, b_needed = go b in
          (Clos ((l_a, (l_ta, ta), a), b), b_needed)
      | Call (e1, e2) ->
          let e1, e1_needed = go e1 in
          let e2, e2_needed = go e2 in
          (Call (e1, e2), e1_needed @ e2_needed)
      | When (e, branches) ->
          let e, e_needed = go e in
          let branches, branches_needed =
            List.split @@ List.map go_branch branches
          in
          let branches_needed = List.concat branches_needed in
          (When (e, branches), e_needed @ branches_needed)
    in
    ((l, t, e), needed)
  in
  go expr

let specialize_queue : ctx -> fenv -> queue -> ready_specialization list =
 fun ctx fenv queue ->
  let rec go : queue -> ready_specialization list = function
    | [] -> []
    | `Needed (new_sym, sym, tvar) :: rest ->
        let e_expr = List.assoc sym fenv in
        let ((_, tvar', _) as e_expr), needed = clone_expr ctx fenv e_expr in
        unify ctx.symbols "specialize" ctx.fresh_tvar tvar tvar';
        (go needed @ [ `Ready (new_sym, e_expr, tvar) ]) @ go rest
  in
  go queue

type specialized = {
  specializations : ready_specialization list;
  entry_points : symbol list;
}

let specialize : ctx -> Syntax.program -> specialized =
 fun ctx program ->
  let entry_points = find_entry_points program in
  let entry_point_symbols =
    List.map symbol_of_needed_specialization entry_points
  in
  let fenv = find_fenv program in
  let specializations = specialize_queue ctx fenv entry_points in
  { specializations; entry_points = entry_point_symbols }

let pp_specialized : Symbol.t -> Format.formatter -> specialized -> unit =
 fun symbols f { specializations; entry_points } ->
  let pp_entry_point f sym =
    Format.fprintf f "@[<hov 2>%s@]@." (Symbol.norm_of sym)
  in
  let pp_specialization f = function
    | `Ready (sym, e, tvar) ->
        Format.fprintf f "@[<hv 2>%s:@ %a =@ %a@]" (Symbol.norm_of sym)
          (Syntax.pp_tvar symbols [] [])
          tvar (Syntax.pp_expr symbols) e
  in
  Format.fprintf f "@[<v 2>entry_points:@,";
  List.iter (pp_entry_point f) entry_points;
  Format.fprintf f "@]@.";
  Format.fprintf f "@[<v 2>specializations:@,";
  List.iter
    (fun s ->
      pp_specialization f s;
      Format.fprintf f "@,")
    specializations;
  Format.fprintf f "@]@."

let show_specialized symbols specialized =
  Util.with_buffer (fun f -> pp_specialized symbols f specialized) 80
