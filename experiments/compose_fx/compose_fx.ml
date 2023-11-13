open Language
open Syntax

let string_of_position ({ pos_lnum; pos_cnum; pos_bol; _ } : Lexing.position) =
  Printf.sprintf "%d:%d" pos_lnum (pos_cnum - pos_bol + 1)

let fresh_parse_ctx () : parse_ctx =
  let n = ref 0 in
  let fresh_int () =
    incr n;
    !n
  in
  let fresh_tvar : fresh_tvar =
   fun ty -> { ty = ref ty; var = `Var (fresh_int ()) }
  in
  { fresh_tvar }

let solve _p = failwith "todo"
let lower _ctx _p = failwith "todo"
let eval (_ty, _program) = failwith "todo"

module Compose_fx : LANGUAGE = struct
  let name = "compose_fx"

  type ty = Syntax.ty
  type parsed_program = { fresh_tvar : fresh_tvar; syn : Syntax.program }

  type canonicalized_program = {
    fresh_tvar : fresh_tvar;
    syn : Syntax.program;
    can : Canonical.program;
  }

  type solved_program = unit
  type ir_program = unit
  type evaled_program = unit

  let parse s =
    let lexbuf = Lexer.from_string s in
    let lex = Lexer.provider lexbuf in
    let parse =
      MenhirLib.Convert.Simplified.traditional2revised Parser.toplevel
    in
    let parse_ctx = fresh_parse_ctx () in
    try
      let syn = parse lex parse_ctx in
      Ok { syn; fresh_tvar = parse_ctx.fresh_tvar }
    with
    | Lexer.SyntaxError what ->
        Error
          (Printf.sprintf "Syntax error: %s at %s" what
             (string_of_position (Lexer.position lexbuf)))
    | Parser.Error ->
        Error
          (Printf.sprintf "Parse error at %s"
             (string_of_position (Lexer.position lexbuf)))

  let canonicalize ({ syn; fresh_tvar } : parsed_program) =
    try
      let can = Canonical.canonicalize { fresh_tvar } syn in
      Ok { fresh_tvar; syn; can }
    with Canonical.Can_error e -> Error e

  let solve _p = failwith "todo"
  let ir _ = failwith "todo"
  let eval _ = failwith "todo"

  let print_parsed ?(width = default_width) ({ syn; _ } : parsed_program) =
    string_of_program ~width syn

  let print_canonicalized ?(width = default_width)
      ({ syn; _ } : canonicalized_program) =
    string_of_program ~width syn

  let print_solved ?(width = default_width) _ =
    let _ = width in
    failwith "todo"

  let print_ir ?(width = default_width) _ =
    let _ = width in
    failwith "todo"

  let print_evaled ?(width = default_width) _ =
    let _ = width in
    failwith "todo"

  let print_type ?(width = default_width) _ =
    let _ = width in
    failwith "todo"

  let types_at _ _ = failwith "todo"
  let hover_info _ _ = failwith "todo"
end
