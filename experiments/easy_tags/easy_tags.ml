open Language
open Syntax
open Solve

let string_of_position ({ pos_lnum; pos_cnum; pos_bol; _ } : Lexing.position) =
  Printf.sprintf "%d:%d" pos_lnum (pos_cnum - pos_bol + 1)

let fresh_var_generator () =
  let n = ref 0 in
  fun () ->
    incr n;
    ref (Unbd !n)

let fresh_parse_ctx () : parse_ctx = { fresh_var = fresh_var_generator () }

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

let solve (p, fresh_var) =
  try
    (* let _ty = infer_program p in *)
    let _ty = infer_program fresh_var p in
    Ok p
  with Solve_err e -> Error e

module Easy_tags : LANGUAGE = struct
  let name = "easy_tags"

  type ty = named_vars * Syntax.ty
  type parsed_program = Syntax.program * fresh_var
  type solved_program = Syntax.program
  type ir_program = unit
  type evaled_program = unit

  let parse = parse
  let solve p = solve p
  let ir _ = failwith "unimplemented"
  let eval _ = failwith "unimplemented"
  let print_parsed ?(width = default_width) (p, _) = string_of_program ~width p
  let print_solved ?(width = default_width) p = string_of_program ~width p

  let print_ir ?(width = default_width) _ =
    let _ = width in
    failwith "unimplemented"

  let print_evaled ?(width = default_width) _ =
    let _ = width in
    failwith "unimplemented"

  let print_type ?(width = default_width) (_, (names, t)) =
    string_of_ty width names t

  let types_at locs p =
    let tys =
      List.map
        (fun l ->
          let res =
            match type_at l p with
            | Some t -> Some (name_vars [ t ], t)
            | None -> None
          in
          (l, res))
        locs
    in
    tys

  let hover_info loc p = hover_info loc p
end
