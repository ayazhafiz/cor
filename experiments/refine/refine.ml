open Language
open Syntax
open Solve

let string_of_position ({ pos_lnum; pos_cnum; pos_bol; _ } : Lexing.position) =
  Printf.sprintf "%d:%d" pos_lnum (pos_cnum - pos_bol + 1)

let fresh_int_generator () =
  let n = ref 0 in
  fun () ->
    incr n;
    !n

type fresh_var = unit -> int

let fresh_parse_ctx () : parse_ctx = { fresh_var = fresh_int_generator () }

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

let solve p =
  try
    (* let _ty = infer_program p in *)
    let _ty = infer_program p in
    Ok p
  with Solve_err e -> Error e

module Refine : LANGUAGE = struct
  let name = "refine"

  type parsed_program = Syntax.program
  type solved_program = Syntax.program
  type mono_program = Syntax.program
  type evaled_program = Syntax.program

  let parse = parse
  let solve p = solve p
  let mono _p = failwith "unimplemented"
  let eval _p = failwith "unimplemented"
  let print_parsed ?(width = default_width) p = string_of_program ~width p
  let print_solved ?(width = default_width) p = string_of_program ~width p
  let print_mono ?(width = default_width) p = string_of_program ~width p
  let print_evaled ?(width = default_width) p = string_of_program ~width p
  let type_at loc p = type_at loc p
  let hover_info loc p = hover_info loc p
end
