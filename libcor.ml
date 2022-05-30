open Language

(*** All languages ***)
let languages : (module LANGUAGE) list = [ (module Roc.Roc); (module Uls.Uls) ]

(* Driver *)
type phase = Parse | Solve | Mono | Eval
type emit = Print | Elab

let assoc_flip l = List.map (fun (a, b) -> (b, a)) l

let phase_list =
  [ (Parse, "parse"); (Solve, "solve"); (Mono, "mono"); (Eval, "eval") ]

let emit_list = [ (Print, "print"); (Elab, "elab"); (Elab, "elaborate") ]

let phase_of_string s =
  match List.assoc_opt s @@ assoc_flip phase_list with
  | Some e -> e
  | _ -> failwith ("Invalid phase " ^ s)

let string_of_phase p = List.assoc p phase_list

let emit_of_string s =
  match List.assoc_opt s @@ assoc_flip emit_list with
  | Some e -> e
  | _ -> failwith ("Invalid emit " ^ s)

let string_of_emit e = List.assoc e emit_list
let unlines = String.concat "\n"

type raw_program = string
type program_lines = string list
type queries = loc list
type command = phase * emit

type preprocessed = {
  raw_program : raw_program;
  program_lines : program_lines;
  queries : queries;
  commands : command list;
}

let preprocess lines : preprocessed =
  let re_cmds = Str.regexp {|# cor \+\([a-z]+\) -\([a-z]+\)|} in
  let re_query = Str.regexp {|\(\^+\)|} in
  let starts_command = String.starts_with ~prefix:"# cor " in
  let starts_out = String.starts_with ~prefix:"> " in
  (* commands in the header *)
  let commands =
    let rec parse = function
      | [] -> []
      | line :: rest ->
          if starts_command line then
            if Str.string_match re_cmds line 0 then
              let phase = Str.matched_group 1 line in
              let emit = Str.matched_group 2 line in
              (phase_of_string phase, emit_of_string emit) :: parse rest
            else failwith ("Invalid command line `" ^ line ^ "`")
          else []
    in
    parse lines
  in
  (* raw user input including commands and queries but before the output; we
     need this for printing back *)
  let raw_program =
    let rec go = function
      | [] -> []
      | "" :: line :: _ when starts_out line -> []
      | l :: rest -> l :: go rest
    in
    unlines (go lines)
  in
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
  { raw_program; program_lines; queries; commands }

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
  String.concat "\n" @@ (raw_program :: List.flatten cmd_out)

module type LANGUAGE = LANGUAGE

let find_opt_lang lang : (module LANGUAGE) option =
  List.find_opt (fun (module M : LANGUAGE) -> M.name = lang) languages

let process_one (module Lang : LANGUAGE) input_lines queries (phase, emit) :
    processed_command =
  let input = unlines input_lines in
  let parse s = match Lang.parse s with Ok p -> p | Error e -> failwith e in
  let solve s = match Lang.solve s with Ok p -> p | Error e -> failwith e in
  let mono s = match Lang.mono s with Ok p -> p | Error e -> failwith e in
  let eval s = match Lang.eval s with Ok p -> p | Error e -> failwith e in
  let elab p =
    if List.length queries = 0 then
      failwith "Asked for elaboration, but there are no queries";
    let one_query program (((_, cstart), (_, cend)) as loc) =
      let num_caret = cend - cstart in
      let prefix =
        "#"
        (* - 1 because positions are 1-indexed *)
        (* - 1 to make room for the starting `#` *)
        ^ String.init (cstart - 1 - 1) (fun _ -> ' ')
        ^ String.init num_caret (fun _ -> '^')
      in
      match Lang.type_at loc program with
      | None -> failwith ("Elaborated type not found at " ^ string_of_loc loc)
      | Some ty -> prefix ^ " " ^ ty
    in
    let rec recreate lineno lines =
      let queries = List.filter (fun ((l, _), _) -> l == lineno) queries in
      match (lines, queries) with
      | [], _ -> []
      | l :: rest, [] -> l :: recreate (lineno + 1) rest
      | l :: rest, queries ->
          let rest = recreate (lineno + 1) rest in
          let queries =
            List.rev queries
            (* reverse because we want the last on the top of the output lines *)
            |> List.map (one_query p)
          in
          l :: (queries @ rest)
    in
    unlines @@ recreate 1 input_lines
  in
  let output =
    match phase with
    | Parse -> (
        let program = parse input in
        match emit with
        | Print -> Lang.print_parsed program
        | Elab -> failwith "Cannot elaborate parsed")
    | Solve -> (
        let program = solve @@ parse input in
        match emit with
        | Print -> Lang.print_solved program
        | Elab -> elab program)
    | Mono -> (
        let program = mono @@ solve @@ parse input in
        match emit with
        | Print -> Lang.print_mono program
        | Elab -> failwith "Cannot elaborate mono")
    | Eval -> (
        let program = eval @@ mono @@ solve @@ parse input in
        match emit with
        | Print -> Lang.print_evaled program
        | Elab -> failwith "Cannot elaborate eval")
  in
  ((phase, emit), output)
