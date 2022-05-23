open Language
open Syntax

let string_of_position ({ pos_lnum; pos_cnum; pos_bol; _ } : Lexing.position) =
  Printf.sprintf "%d:%d" pos_lnum (pos_cnum - pos_bol + 1)

let fresh_int_generator () =
  let n = ref 0 in
  fun () ->
    incr n;
    !n

let fresh_parse_ctx () : parse_ctx =
  {
    fresh_var = fresh_int_generator ();
    fresh_clos_name = fresh_int_generator ();
  }

let parse s =
  let lexbuf = Lexer.from_string s in
  let lex = Lexer.provider lexbuf in
  let parse =
    MenhirLib.Convert.Simplified.traditional2revised Parser.toplevel
  in
  let parse_ctx = fresh_parse_ctx () in
  try
    let parsed = parse lex parse_ctx in
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

module Uls : LANGUAGE = struct
  let name = "uls"

  type program = Syntax.program

  let parse = parse
  let print = string_of_program
  let type_at = type_at
end
