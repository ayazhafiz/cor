open Language

(*** All languages ***)
let languages : (module LANGUAGE) list = [ (module Roc.Roc); (module Uls.Uls) ]

(* Driver *)
type phase = Parse
type emit = Print | Elab

let assoc_flip l = List.map (fun (a, b) -> (b, a)) l
let phase_list = [ (Parse, "parse") ]
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

let preprocess lines =
  let re_cmds = Str.regexp {|# cor \+\([a-z]+\) -\([a-z]+\)|} in
  let commands =
    let rec parse = function
      | [] -> []
      | line :: rest ->
          if String.starts_with ~prefix:"# cor " line then
            if Str.string_match re_cmds line 0 then
              let phase = Str.matched_group 1 line in
              let emit = Str.matched_group 2 line in
              (phase_of_string phase, emit_of_string emit) :: parse rest
            else failwith ("Invalid command line `" ^ line ^ "`")
          else []
    in
    parse lines
  in
  let real_program =
    let rec parse = function
      | [] -> []
      | "" :: line :: _ when String.starts_with ~prefix:"# cor-out" line -> []
      | line :: rest -> line :: parse rest
    in
    parse lines
  in
  (String.concat "\n" real_program, commands)

let postprocess program commands =
  let cmd_out =
    List.map
      (fun (phase, emit, str) ->
        [
          "";
          Printf.sprintf "# cor-out +%s -%s" (string_of_phase phase)
            (string_of_emit emit);
          str;
        ])
      commands
  in
  String.concat "\n" @@ (program :: List.flatten cmd_out)

let read_chan chan =
  let lines = ref [] in
  (try
     while true do
       lines := input_line chan :: !lines
     done
   with End_of_file -> close_in chan);
  List.rev !lines

let read_file f = read_chan @@ open_in f
let read_stdin () = read_chan stdin

(**)
let infile = ref None
let lang = ref None
let inplace = ref false

let handle_anon arg =
  match !lang with
  | None -> lang := Some arg
  | Some _ -> (
      match !infile with
      | None -> infile := Some arg
      | Some _ -> raise (Arg.Bad ("Too many args! Found " ^ arg)))

let parse_args () =
  Arg.parse
    [
      ("-i", Arg.Set inplace, "Write output in-place. Not relevant for stdin.");
    ]
    handle_anon ""

let find_lang () : (module LANGUAGE) =
  match !lang with
  | Some lang -> (
      let lang_mod =
        List.find_opt (fun (module M : LANGUAGE) -> M.name = lang) languages
      in
      match lang_mod with
      | Some m -> m
      | None -> failwith ("No language " ^ lang))
  | None -> failwith "No language specified!"

let process_one (module Lang : LANGUAGE) program (phase, emit) =
  let parse s = match Lang.parse s with Ok p -> p | Error e -> failwith e in
  let output =
    match phase with
    | Parse -> (
        let parsed = parse program in
        match emit with
        | Print -> Lang.print parsed
        | Elab -> failwith "Cannot elab parsed")
  in
  (phase, emit, output)

let main () =
  parse_args ();
  let input_lines =
    match !infile with Some f -> read_file f | None -> read_stdin ()
  in
  let lang = find_lang () in
  let program, cmds = preprocess input_lines in
  let cmd_out = List.map (process_one lang program) cmds in
  let output = postprocess program cmd_out in
  match (!inplace, !infile) with
  | false, _ | true, None -> print_endline output
  | true, Some file ->
      let chan = open_out file in
      output_string chan output;
      close_out chan

let () = try main () with Failure msg -> prerr_endline ("Error: " ^ msg)
