open Libcor

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

type input = File of string | Stdin

let input_lines = function Stdin -> read_stdin () | File f -> read_file f
let infiles = ref []
let lang = ref None
let inplace = ref false

let handle_anon arg =
  match !lang with
  | None -> lang := Some arg
  | Some _ -> infiles := arg :: !infiles

let parse_args () =
  Arg.parse
    [
      ("-i", Arg.Set inplace, "Write output in-place. Not relevant for stdin.");
    ]
    handle_anon ""

let find_lang () =
  match !lang with
  | Some lang -> (
      let lang_mod = find_opt_lang lang in
      match lang_mod with
      | Some m -> m
      | None -> failwith ("No language " ^ lang))
  | None -> failwith "No language specified!"

let main () =
  parse_args ();
  let inputs =
    match !infiles with
    | [] -> [ Stdin ]
    | files -> List.map (fun f -> File f) files
  in
  let lang = find_lang () in
  let do1 input_source =
    let input_lines = input_lines input_source in
    let { raw_program; program_lines; queries; commands } =
      preprocess input_lines
    in
    let cmd_out = List.map (process_one lang program_lines queries) commands in
    let output = postprocess raw_program cmd_out in
    match (!inplace, input_source) with
    | _, Stdin -> print_endline output
    | false, File f ->
        print_string ("# " ^ f ^ "\n");
        print_endline output
    | true, File file ->
        let chan = open_out file in
        output_string chan output;
        close_out chan
  in
  List.iter do1 inputs

let () =
  try main ()
  with Failure msg ->
    prerr_endline ("Error: " ^ msg);
    flush_all ()
