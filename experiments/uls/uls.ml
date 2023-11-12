open Language
open Syntax
open Solve
open Ir
open Eval
open Util

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
    let spec_table = infer_program fresh_ty p in
    Ok (p, spec_table)
  with Solve_err e -> Error e

type tctx = (int * string) list

module Uls : LANGUAGE = struct
  let name = "uls"

  type ty = tctx * Syntax.ty
  type parsed_program = Syntax.program * fresh_var
  type canonicalized_program = parsed_program
  type solved_program = Syntax.program * spec_table

  type ir_program = {
    defs : (string * e_expr) list;
    entry_points : string list;
  }

  type evaled_program = (string * expr list) list

  let parse = parse
  let canonicalize = Result.ok
  let solve (p, fresh_var) = solve p fresh_var

  let ir (p, spec_table) =
    try
      let defs, entry_points = ir p spec_table in
      Ok { defs; entry_points }
    with Ir_error e -> Error e

  let eval { defs; entry_points } =
    try Ok (eval defs entry_points) with Eval_error e -> Error e

  let print_parsed ?(width = default_width) (p, _) = string_of_program ~width p
  let print_canonicalized = print_parsed
  let print_solved ?(width = default_width) (p, _) = string_of_program ~width p

  let print_ir ?(width = default_width) { defs; entry_points } =
    string_of_program ~width
      (List.map
         (fun (x, e) -> Def ((noloc, x), e, List.mem x entry_points))
         defs)

  let print_evaled ?(width = default_width) evaled =
    let open Format in
    with_buffer
      (fun f ->
        fprintf f "@[<v 0>";
        List.iteri
          (fun i (s, es) ->
            if i > 0 then fprintf f "@,@,";
            fprintf f "@[<hov 2>%s =" s;
            List.iteri
              (fun i e ->
                fprintf f "@ ";
                if i > 0 then fprintf f "| ";
                fprintf f "@[";
                pp_expr f (noloc, TVal "?", e);
                fprintf f "@]")
              es;
            fprintf f "@]")
          evaled;
        fprintf f "@]")
      width

  let print_type ?(width = default_width) (_, (tctx, t)) =
    string_of_ty width tctx t

  let types_at locs (p, _) = List.map (fun l -> (l, type_at l p)) locs
  let hover_info loc (p, _) = hover_info loc p
end
