open Symbol
open Ir
open Type

type specialization = {
  name : symbol;
  args : layout list;
  ret : layout;
  specialization_symbol : symbol;
}

type ctx = {
  symbols : Symbol.t;
  cache : layout_cache;
  fresh_rec_id : fresh_rec_id;
  fresh_tvar : fresh_tvar;
  specializations : specialization list ref;
  toplevel_functions : symbol list ref;
}

let new_ctx symbols fresh_tvar =
  let cache = ref [] in
  let next_id = ref 0 in
  let fresh_rec_id () =
    let id = !next_id in
    next_id := id + 1;
    `Rec id
  in
  {
    symbols;
    cache;
    fresh_rec_id;
    fresh_tvar;
    specializations = ref [];
    toplevel_functions = ref [];
  }

let add_toplevel_function ctx f =
  ctx.toplevel_functions := f :: !(ctx.toplevel_functions)

let is_toplevel_function ctx f = List.mem f !(ctx.toplevel_functions)
