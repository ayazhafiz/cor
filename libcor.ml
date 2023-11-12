open Language

(*** All languages ***)
let lang_mods : (module LANGUAGE) list =
  [
    (module Roc.Roc);
    (module Uls.Uls);
    (module Refine.Refine);
    (module Easy_tags.Easy_tags);
    (module Compose_fx.Compose_fx);
  ]

let languages = List.map (fun (module M : LANGUAGE) -> M.name) lang_mods

(* Driver *)
type phase = Parse | Solve | Ir | Eval
type emit = Print | Elab

let assoc_flip l = List.map (fun (a, b) -> (b, a)) l

let phase_list =
  [ (Parse, "parse"); (Solve, "solve"); (Ir, "ir"); (Eval, "eval") ]

let emit_list = [ (Print, "print"); (Elab, "elab"); (Elab, "elaborate") ]
let phase_of_string s = List.assoc_opt s @@ assoc_flip phase_list
let string_of_phase p = List.assoc p phase_list
let emit_of_string s = List.assoc_opt s @@ assoc_flip emit_list
let string_of_emit e = List.assoc e emit_list
let unlines = String.concat "\n"

let phases =
  List.map string_of_phase @@ List.sort_uniq compare @@ List.map fst phase_list

let emits =
  List.map string_of_emit @@ List.sort_uniq compare @@ List.map fst emit_list

type command = phase * emit
type command_err = string * [ `InvalidPhase | `InvalidEmit | `Unparseable ]

let string_of_command_err (s, e) =
  s ^ ": "
  ^
  match e with
  | `InvalidPhase -> "invalid phase"
  | `InvalidEmit -> "invalid emit"
  | `Unparseable -> "cannot parse this command"

type raw_program = string list

let raw_program_of_string = String.split_on_char '\n'
let raw_program_of_lines = Fun.id

type queries = loc list
type program = string list * queries

type preprocessed = {
  raw_program : raw_program;
  program : program;
  commands : (command, command_err) result list;
}

let re_cmds = Str.regexp {|# cor \+\([a-z]+\) -\([a-z]+\)|}
let re_query = Str.regexp {|\(\^+\)|}
let starts_command = String.starts_with ~prefix:"# cor "
let starts_out = String.starts_with ~prefix:"> "

let parse_command line =
  if Str.string_match re_cmds line 0 then
    let phase = Str.matched_group 1 line in
    let emit = Str.matched_group 2 line in
    match (phase_of_string phase, emit_of_string emit) with
    | Some p, Some e -> Ok (p, e)
    | None, _ -> Error (line, `InvalidPhase)
    | _, None -> Error (line, `InvalidEmit)
  else Error (line, `Unparseable)

let program_without_output =
  let rec go = function
    | [] -> []
    | "" :: line :: _ when starts_out line -> []
    | l :: rest -> l :: go rest
  in
  go

let program_without_commands =
  let rec go = function
    | [] -> []
    | line :: rest -> if starts_command line then go rest else line :: rest
  in
  go

let user_ann_program (lines : raw_program) : string =
  unlines @@ program_without_commands @@ program_without_output lines

let preprocess (lines : raw_program) : preprocessed =
  (* commands in the header *)
  let commands =
    let rec parse = function
      | [] -> []
      | line :: rest ->
          if starts_command line then parse_command line :: parse rest else []
    in
    parse lines
  in
  (* raw user input including commands and queries but before the output; we
     need this for printing back *)
  let raw_program = program_without_output lines in
  (* parse N queries on a single line *)
  let parse_line_queries lineno line : loc list =
    let rec search start =
      try
        let start = Str.search_forward re_query line start in
        let fin = start + (String.length @@ Str.matched_string line) in
        (* + 1 because positions are 1-indexed *)
        (start + 1, fin + 1) :: search fin
      with Not_found -> []
    in
    let ranges = search 0 in
    List.map (fun (start, fin) -> ((lineno, start), (lineno, fin))) ranges
    |> List.rev
    (* reverse because we want the last query to be processed first, and printed on the first line *)
  in
  (* program ignoring commands and removing query lines *)
  let program_lines, queries =
    let rec parse lineno = function
      | [] -> ([], [])
      | l :: rest when starts_command l -> parse lineno rest
      | l :: _ when starts_out l -> ([], [])
      | line :: rest ->
          let queries = parse_line_queries (lineno - 1) line in
          if List.length queries == 0 then
            (* no queries, include this line *)
            let rest_lines, rest_queries = parse (lineno + 1) rest in
            (line :: rest_lines, rest_queries)
          else
            (* queries - return them and throw away the line *)
            let rest_lines, rest_queries = parse lineno rest in
            (rest_lines, queries @ rest_queries)
    in
    parse 1 lines
  in
  { raw_program; program = (program_lines, queries); commands }

type processed_command = command * string

let postprocess (raw_program : raw_program) (commands : processed_command list)
    : string =
  let reflow_out s =
    unlines @@ List.map (fun s -> "> " ^ s) @@ String.split_on_char '\n' s
  in
  let cmd_out =
    List.map
      (fun ((phase, emit), str) ->
        [
          "";
          Printf.sprintf "> cor-out +%s -%s" (string_of_phase phase)
            (string_of_emit emit);
          reflow_out str;
        ])
      commands
  in
  String.concat "\n" @@ raw_program @ List.flatten cmd_out

module type LANGUAGE = LANGUAGE

let find_language lang : (module LANGUAGE) option =
  List.find_opt (fun (module M : LANGUAGE) -> M.name = lang) lang_mods

type compile_output = string

let string_of_compile_output = Fun.id

type compile_err =
  | ParseErr of string
  | SolveErr of string
  | IrErr of string
  | EvalErr of string
  | ElabErr of [ `NoQueries | `TypeNotFound of loc ]
  | BadEmit of phase * emit
  | NoHover

let string_of_compile_err = function
  | ParseErr s -> "Parse error: " ^ s
  | SolveErr s -> "Solve error: " ^ s
  | IrErr s -> "Ir error: " ^ s
  | EvalErr s -> "Eval error: " ^ s
  | ElabErr e -> (
      "Elab error: "
      ^
      match e with
      | `NoQueries -> "no queries given!"
      | `TypeNotFound loc -> "Type not found at " ^ string_of_loc loc)
  | BadEmit (p, e) ->
      "Commit do " ^ string_of_emit e ^ " for phase " ^ string_of_phase p
  | NoHover -> "No hover location found"

type compile_result = (compile_output, compile_err) result

let ( >>= ) = Result.bind

let process_one (module Lang : LANGUAGE) (lines, queries) (phase, emit) :
    compile_result =
  let input = unlines lines in
  let open Lang in
  let parse s = Result.map_error (fun s -> ParseErr s) @@ Lang.parse s in
  let solve s = Result.map_error (fun s -> SolveErr s) @@ Lang.solve s in
  let ir s = Result.map_error (fun s -> IrErr s) @@ Lang.ir s in
  let eval s = Result.map_error (fun s -> EvalErr s) @@ Lang.eval s in
  let elab p =
    if List.length queries = 0 then Error (ElabErr `NoQueries)
    else
      let open Either in
      let queries = Lang.types_at queries p in
      let one_query (((_, cstart), (_, cend)) as loc) =
        let num_caret = cend - cstart in
        let prefix =
          "#"
          (* - 1 because positions are 1-indexed *)
          (* - 1 to make room for the starting `#` *)
          ^ String.init (cstart - 1 - 1) (fun _ -> ' ')
          ^ String.init num_caret (fun _ -> '^')
          ^ " "
        in
        match List.assoc loc queries with
        | None -> Right (ElabErr (`TypeNotFound loc))
        | Some ty ->
            let s_ty = Lang.print_type (p, ty) in
            Left (reflow_lines prefix s_ty)
      in
      let rec recreate lineno lines =
        let queries =
          List.filter (fun (((l, _), _), _) -> l == lineno) queries
        in
        match (lines, queries) with
        | [], _ -> []
        | l :: rest, [] -> Left l :: recreate (lineno + 1) rest
        | l :: rest, queries ->
            let rest = recreate (lineno + 1) rest in
            let queries = queries |> List.map fst |> List.map one_query in
            Left l :: (queries @ rest)
      in
      let oks, errs = List.partition_map Fun.id @@ recreate 1 lines in
      match errs with e :: _ -> Error e | [] -> Ok (unlines oks)
  in

  let ( &> ) a b = Result.map b a in
  match (phase, emit) with
  | Parse, Print -> input |> parse &> print_parsed
  | Solve, Print -> input |> parse >>= solve &> print_solved
  | Solve, Elab -> input |> parse >>= solve >>= elab
  | Ir, Print -> input |> parse >>= solve >>= ir &> print_ir
  | Eval, Print -> input |> parse >>= solve >>= ir >>= eval &> print_evaled
  | phase, emit -> Error (BadEmit (phase, emit))

let hover_info (module Lang : LANGUAGE) lines lineco =
  let parse s = Result.map_error (fun s -> ParseErr s) @@ Lang.parse s in
  let solve s = Result.map_error (fun s -> SolveErr s) @@ Lang.solve s in
  let hover s = Lang.hover_info lineco s |> Option.to_result ~none:NoHover in
  let hover_info = unlines lines |> parse >>= solve >>= hover in
  hover_info
