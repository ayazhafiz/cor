open Symbol
open Ir

type specialization = {
  name : symbol;
  args : layout list;
  ret : layout;
  specialization_symbol : symbol;
}

type t = { specializations : specialization list ref }

let determine_specialization ~ctx tvar =
  let open Type in
  let tvar = unlink_w_alias tvar in
  match tvar_deref tvar with
  | Content (TFn ((_, arg), _lset, (_, ret))) ->
      let arg = Ir_layout.layout_of_tvar ctx arg in
      let ret = Ir_layout.layout_of_tvar ctx ret in
      let args = [ erased_captures_lay (); arg ] in
      (args, ret)
  | _ ->
      let ret = Ir_layout.layout_of_tvar ctx tvar in
      ([], ret)

let equiv_specialization specialization ~name ~args ~ret =
  if specialization.name <> name then false
  else if List.length specialization.args <> List.length args then false
  else if not @@ List.for_all2 Ir_layout.is_lay_equiv specialization.args args
  then false
  else if not @@ Ir_layout.is_lay_equiv specialization.ret ret then false
  else true

let add_specialization ~(ctx : ctx) { specializations } name tvar :
    symbol * [ `New | `Existing ] =
  let args, ret = determine_specialization ~ctx tvar in
  let specialization =
    List.find_opt (equiv_specialization ~name ~args ~ret) !specializations
  in
  match specialization with
  | Some specialization -> (specialization.specialization_symbol, `Existing)
  | None ->
      let specialization_symbol =
        ctx.symbols.fresh_symbol_named @@ Symbol.syn_of ctx.symbols name
      in
      specializations :=
        { name; args; ret; specialization_symbol } :: !specializations;
      (specialization_symbol, `New)

let make : unit -> t = fun () -> { specializations = ref [] }
