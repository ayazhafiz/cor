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

let lower ctx p =
  let ty = xty p in
  let ir = Lower.ir_of_expr ctx p in
  Ok (ty, ir)

let eval (ty, program) =
  let var, memory = Eval.eval program in
  Ok (ty, var, memory)

module Refine : LANGUAGE = struct
  let name = "refine"

  type ty = Syntax.ty
  type parsed_program = Syntax.program
  type canonicalized_program = parsed_program
  type solved_program = Syntax.program * Ir.ctx
  type ir_program = Syntax.ty * Ir.program
  type evaled_program = Syntax.ty * Ir.var * Eval.memory

  let parse = parse
  let canonicalize = Result.ok
  let solve p = solve p |> Result.map (fun res -> (res, Ir.new_ctx ()))
  let ir (p, ctx) = lower ctx p
  let eval p = eval p
  let print_parsed ?(width = default_width) p = string_of_program ~width p
  let print_canonicalized = print_parsed
  let print_solved ?(width = default_width) (p, _) = string_of_program ~width p
  let print_ir ?(width = default_width) (_, p) = Ir.string_of_program ~width p

  let print_evaled ?(width = default_width) (ty, var, memory) =
    Eval.print_back width ty var memory

  let print_type ?(width = default_width) (_, ty) = Syntax.string_of_ty width ty
  let types_at locs (p, _) = List.map (fun l -> (l, type_at l p)) locs
  let hover_info loc (p, _) = hover_info loc p
end
