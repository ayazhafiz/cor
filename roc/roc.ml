open Language
open Syntax

let string_of_position ({ pos_lnum; pos_cnum; pos_bol; _ } : Lexing.position) =
  Printf.sprintf "%d:%d" pos_lnum (pos_cnum - pos_bol + 1)

let parse s =
  let lexbuf = Lexer.from_string s in
  let lex = Lexer.provider lexbuf in
  let parse =
    MenhirLib.Convert.Simplified.traditional2revised Parser.toplevel
  in
  try
    let parsed = parse lex in
    Ok parsed
  with
  | Lexer.SyntaxError what ->
      Error
        (Printf.sprintf "Syntax error: %s at %s" what
           (string_of_position (Lexer.position lexbuf)))
  | Parser.Error ->
      Error
        (Printf.sprintf "Parse error at %s"
           (string_of_position (Lexer.position lexbuf)))

module Roc : LANGUAGE = struct
  let name = "roc"

  type parsed_program = loc_expr
  type solved_program = loc_expr
  type mono_program = loc_expr
  type evaled_program = loc_expr

  let parse = parse
  let solve _ = failwith "unimplemented"
  let mono _ = failwith "unimplemented"
  let eval _ = failwith "unimplemented"
  let print_parsed = string_of_expr
  let print_solved = string_of_expr
  let print_mono = string_of_expr
  let print_evaled = string_of_expr
  let type_at _ = failwith "unimplemented"
end
