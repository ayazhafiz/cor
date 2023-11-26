open Language
open Syntax

let string_of_position ({ pos_lnum; pos_cnum; pos_bol; _ } : Lexing.position) =
  Printf.sprintf "%d:%d" pos_lnum (pos_cnum - pos_bol + 1)

let fresh_parse_ctx () : parse_ctx =
  let n = ref Type.min_var in
  let fresh_int () =
    incr n;
    !n
  in
  let fresh_tvar : Type.fresh_tvar =
   fun ty -> { ty = ref ty; var = `Var (fresh_int ()); recur = ref false }
  in
  let symbols = Symbol.make () in
  { fresh_tvar; symbols }

module Compose_fx : LANGUAGE = struct
  let name = "compose_fx"

  type ty = { symbols : Symbol.t; names : Type.named_vars; tvar : Type.tvar }

  type parsed_program = {
    symbols : Symbol.t;
    fresh_tvar : Type.fresh_tvar;
    syn : Syntax.program;
  }

  type canonicalized_program = {
    symbols : Symbol.t;
    fresh_tvar : Type.fresh_tvar;
    syn : Syntax.program;
    can : Can.program;
  }

  type solved_program = {
    symbols : Symbol.t;
    fresh_tvar : Type.fresh_tvar;
    syn : Syntax.program;
    can : Can.program;
  }

  type ir_program = { symbols : Symbol.t; program : Ir.program }
  type evaled_program = { symbols : Symbol.t; evaled : Eval.evaled list }

  let parse s =
    let lexbuf = Lexer.from_string s in
    let lex = Lexer.provider lexbuf in
    let parse =
      MenhirLib.Convert.Simplified.traditional2revised Parser.toplevel
    in
    let parse_ctx = fresh_parse_ctx () in
    try
      let syn = parse lex parse_ctx in
      let program : parsed_program =
        { symbols = parse_ctx.symbols; syn; fresh_tvar = parse_ctx.fresh_tvar }
      in
      Ok program
    with
    | Lexer.SyntaxError what ->
        Error
          (Printf.sprintf "Syntax error: %s at %s" what
             (string_of_position (Lexer.position lexbuf)))
    | Parser.Error ->
        Error
          (Printf.sprintf "Parse error at %s"
             (string_of_position (Lexer.position lexbuf)))

  let canonicalize ({ symbols; syn; fresh_tvar } : parsed_program) =
    try
      let can = Can_lower.canonicalize { symbols; fresh_tvar } syn in
      let program : canonicalized_program = { symbols; fresh_tvar; syn; can } in
      Ok program
    with Can_lower.Can_error e -> Error e

  let solve ({ symbols; syn; can; fresh_tvar } : canonicalized_program) =
    try
      Solve.infer_program { symbols; fresh_tvar } can;
      Ok { symbols; fresh_tvar; syn; can }
    with Solve.Solve_err e -> Error e

  let ir ({ symbols; fresh_tvar; syn = _; can } : solved_program) =
    let ctx = Ir.new_ctx symbols fresh_tvar in
    let specialized = Mono_lower.specialize ctx can in
    let compiled = Ir_lower.compile ~ctx specialized in
    Ir_check.check compiled;
    Ok { symbols; program = compiled }

  let eval ({ program; symbols } : ir_program) =
    let evaled = Eval.eval_program program in
    Ok { symbols; evaled }

  let print_parsed ?(width = default_width)
      ({ symbols; syn; _ } : parsed_program) =
    string_of_program ~width symbols syn

  let print_canonicalized ?(width = default_width)
      ({ symbols; syn; _ } : canonicalized_program) =
    string_of_program ~width symbols syn

  let print_solved ?(width = default_width)
      ({ symbols; syn; _ } : solved_program) =
    string_of_program ~width symbols syn

  let print_ir ?(width = 80) ({ program; _ } : ir_program) =
    Ir.string_of_program ~width program

  let print_evaled ?(width = default_width)
      ({ evaled; symbols } : evaled_program) =
    Eval.string_of_evaled ~width symbols evaled

  let print_type ?(width = default_width) (_, { symbols; names; tvar }) =
    Type.string_of_tvar width symbols names tvar

  let types_at locs ({ symbols; syn; _ } : solved_program) =
    let add_names ty = { symbols; names = Type.name_vars [ ty ]; tvar = ty } in
    let type_and_names l = type_at l syn |> Option.map add_names in
    List.map (fun l -> (l, type_and_names l)) locs

  let hover_info loc ({ symbols; syn; _ } : solved_program) =
    hover_info loc syn symbols
end
