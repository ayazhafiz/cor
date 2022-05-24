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
    Ok (parsed, parse_ctx.fresh_var)
  with
  | Lexer.SyntaxError what ->
      Error
        (Printf.sprintf "Syntax error: %s at %s" what
           (string_of_position (Lexer.position lexbuf)))
  | Parser.Error ->
      Error
        (Printf.sprintf "Parse error at %s"
           (string_of_position (Lexer.position lexbuf)))

let solve p fresh_var =
  let fresh_ty () = TVar (ref (Unbd (fresh_var ()))) in
  try
    infer_program fresh_ty p;
    Ok (p, fresh_var)
  with Solve_err e -> Error e

module Uls : LANGUAGE = struct
  let name = "uls"

  type program = Syntax.program * fresh_var

  let parse = parse
  let solve (p, fresh_var) = solve p fresh_var
  let print ?(width = default_width) (p, _) = string_of_program ~width p
  let type_at loc (p, _) = type_at loc p
end
