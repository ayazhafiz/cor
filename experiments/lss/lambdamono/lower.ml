open Ast
open Lower_type
open Type_clone_inst
open Ctx
open Symbol
module M = Lambdasolved.Ast
module T = Lambdasolved.Type
module P = Lambdasolved.Type_print

let specialize_expr ~(ctx : Ctx.t) ~ty_cache ~mono_cache expr =
  let lower_type = lower_type mono_cache ctx.fresh_tvar in
  let rec go (t, e) =
    let t = clone_inst ctx.s_fresh_tvar ty_cache t in
    let e =
      match e with
      | M.Var x -> (
          match
            Specializations.specialize_fn ctx.specializations mono_cache
              ctx.fresh_tvar x t
          with
          | None -> Var x (* No specialization needed *)
          | Some _fn_sym ->
              (* construct the lambda set tag *)
              let captures =
                extract_closure_captures mono_cache ctx.fresh_tvar t x
              in
              let tag_name = lambda_tag_name x in
              let captures_expr =
                match captures with
                | None -> None
                | Some { captures; ty = t_captures } ->
                    let build_field (x, t) =
                      (Symbol.show_symbol_raw x, (t, Var x))
                    in
                    let captures_rcd = Record (List.map build_field captures) in
                    Some (t_captures, captures_rcd)
              in
              let tag = Tag (tag_name, Option.to_list captures_expr) in
              tag)
      | M.Int i -> Int i
      | M.Str s -> Str s
      | M.Tag (t, args) ->
          let args = List.map go args in
          Tag (t, args)
      | M.Record fields ->
          let fields = List.map (fun (f, e) -> (f, go e)) fields in
          Record fields
      | M.Access (e, f) ->
          let e = go e in
          Access (e, f)
      | M.Let ((t_x, x), body, rest) ->
          let t_x = clone_inst ctx.s_fresh_tvar ty_cache t_x in
          let body = go body in
          let rest = go rest in
          Let ((lower_type t_x, x), body, rest)
      | M.Call (((t_f, _) as f), a) ->
          let t_f = clone_inst ctx.s_fresh_tvar ty_cache t_f in
          let f = go f in
          let a = go a in
          let compile_branch ((lambda, _) : symbol * T.captures) : branch =
            let captures_sym = ctx.symbols.fresh_symbol_named "captures" in
            let t_captures =
              extract_closure_captures mono_cache ctx.fresh_tvar t_f lambda
            in
            let lambda_real =
              Specializations.specialize_fn ctx.specializations mono_cache
                ctx.fresh_tvar lambda t_f
              |> Option.get
            in
            match t_captures with
            | None ->
                let pat = (fst f, PTag (lambda_tag_name lambda, [])) in
                let body = (fst a, Call (lambda_real, [ a ])) in
                (pat, body)
            | Some { ty = t_captures; _ } ->
                let pat =
                  ( fst f,
                    PTag
                      ( lambda_tag_name lambda,
                        [ (t_captures, PVar captures_sym) ] ) )
                in
                let body =
                  ( fst a,
                    Call (lambda_real, [ a; (t_captures, Var captures_sym) ]) )
                in
                (pat, body)
          in
          let lambda_set = extract_lambda_set t_f in
          let branches =
            SymbolMap.bindings lambda_set |> List.map compile_branch
          in
          When (f, branches)
      | M.KCall (kfn, args) ->
          let args = List.map go args in
          KCall (kfn, args)
      | M.When (e, branches) ->
          let e = go e in
          let branches = List.map go_branch branches in
          When (e, branches)
    in
    (lower_type t, e)
  and go_branch (p, e) =
    let p = go_pat p in
    let e = go e in
    (p, e)
  and go_pat (t, p) =
    let t = lower_type @@ clone_inst ctx.s_fresh_tvar ty_cache t in
    let p =
      match p with
      | M.PVar x -> PVar x
      | M.PTag (tag, args) ->
          let args = List.map go_pat args in
          PTag (tag, args)
    in
    (t, p)
  in
  go expr

let fresh_ty_cache () = ref []

let specialize_fn ~ctx ~ty_cache ~mono_cache ~t_new ~lambda ~t
    ({ arg = t_arg, arg; captures = _; body } : M.fn) =
  let t = clone_inst ctx.s_fresh_tvar ty_cache t in
  Lambdasolved.Solve.unify ctx.s_fresh_tvar t t_new;

  let t_arg = clone_inst ctx.s_fresh_tvar ty_cache t_arg in
  let body = specialize_expr ~ctx ~ty_cache ~mono_cache body in

  let t_arg = lower_type mono_cache ctx.fresh_tvar t_arg in

  let captures = extract_closure_captures mono_cache ctx.fresh_tvar t lambda in
  match captures with
  | None -> { args = [ (t_arg, arg) ]; body }
  | Some { captures; ty = t_captures } ->
      let captures_sym = ctx.symbols.fresh_symbol_named "captures" in
      let args = [ (t_arg, arg); (t_captures, captures_sym) ] in
      let body =
        List.fold_left
          (fun body (x, t) ->
            let captures_arg = (t_captures, Var captures_sym) in
            let access = (t, Access (captures_arg, Symbol.show_symbol_raw x)) in
            let bind = (t, x) in
            (fst body, Let (bind, access, body)))
          body captures
      in
      { args; body }

let specialize_val ~ctx ~ty_cache ~mono_cache body =
  let body = specialize_expr ~ctx ~ty_cache ~mono_cache body in
  body

let specialize_run ~ctx ~ty_cache ~mono_cache body =
  let body = specialize_val ~ctx ~ty_cache ~mono_cache body in
  body

let loop_specializations : Ctx.t -> unit =
 fun ctx ->
  let rec go () =
    match Specializations.next_specialization ctx.specializations with
    | None -> ()
    | Some { name; t_fn; fn; t_new; specialized; name_new = _ } ->
        let fn =
          specialize_fn ~ctx ~ty_cache:(fresh_ty_cache ())
            ~mono_cache:(fresh_mono_cache ()) ~t_new ~lambda:name ~t:t_fn fn
        in
        specialized := Some fn;
        go ()
  in
  go ()

let init_specializations : Ctx.t -> M.program -> def list =
 fun ctx program ->
  let rec go (acc : def list) = function
    | [] -> List.rev acc
    | ((_, x), def) :: defs ->
        let acc =
          match def with
          | `Run (run, t) ->
              let ty_cache = fresh_ty_cache () in
              let mono_cache = fresh_mono_cache () in
              let run = specialize_run ~ctx ~ty_cache ~mono_cache run in
              let acc = (x, `Run (run, t)) :: acc in
              acc
          | `Val val_ ->
              let ty_cache = fresh_ty_cache () in
              let mono_cache = fresh_mono_cache () in
              let val_ = specialize_val ~ctx ~ty_cache ~mono_cache val_ in
              let acc = (x, `Val val_) :: acc in
              acc
          | `Fn _ ->
              (* these will get specialized when called *)
              acc
        in
        go acc defs
  in
  go [] program

let lower : Ctx.t -> M.program -> program =
 fun ctx program ->
  let val_run_defs = init_specializations ctx program in
  loop_specializations ctx;
  let fn_defs = Specializations.solved_specializations ctx.specializations in
  fn_defs @ val_run_defs
