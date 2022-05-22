open Language

(*** All languages ***)
let languages : (module LANGUAGE) list = [ (module Roc.Roc); (module Uls.Uls) ]

(* Driver *)
let phase : [ `None | `Parse ] ref = ref `None
let emit : [ `None | `Print | `Elab ] ref = ref `None
let lang = ref None
let infile = ref None
let set_phase p = phase := p
let set_emit e = Arg.Unit (fun () -> emit := e)

let speclist =
  [
    ("-print", set_emit `Print, "Emit printed program");
    ("-elab", set_emit `Elab, "Emit elaborated file");
  ]

let handle_anon arg =
  match arg with
  | "+parse" -> set_phase `Parse
  | a when String.get a 1 == '+' -> raise (Arg.Bad ("Unknown emit " ^ arg))
  | _ -> (
      match !lang with
      | None -> lang := Some arg
      | Some _ -> (
          match !infile with
          | None -> infile := Some arg
          | Some _ -> raise (Arg.Bad ("Too many args! Found " ^ arg))))

let parse_args () = Arg.parse speclist handle_anon ""

let read_chan chan =
  let lines = ref [] in
  (try
     while true do
       lines := input_line chan :: !lines
     done
   with End_of_file -> close_in chan);
  List.rev !lines |> String.concat "\n"

let read_file f = read_chan @@ open_in f
let read_stdin () = read_chan stdin

let main () =
  parse_args ();
  let (module Lang : LANGUAGE) =
    match !lang with
    | Some lang -> (
        let lang_mod =
          List.find_opt (fun (module M : LANGUAGE) -> M.name = lang) languages
        in
        match lang_mod with
        | Some m -> m
        | None -> failwith ("No language " ^ lang))
    | None -> failwith "No language specified!"
  in
  let input =
    match !infile with Some f -> read_file f | None -> read_stdin ()
  in
  let parse s = match Lang.parse s with Ok p -> p | Error e -> failwith e in
  let output =
    match !phase with
    | `Parse -> (
        let parsed = parse input in
        match !emit with
        | `Print -> Lang.print parsed
        | `Elab -> failwith "Cannot elab parsed"
        | `None -> failwith "Missing emit!")
    | `None -> failwith "Missing phase!"
  in
  print_endline output

let () = try main () with Failure msg -> prerr_endline ("Error: " ^ msg)
