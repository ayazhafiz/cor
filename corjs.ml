open Libcor
open Js_of_ocaml

let wrap doit =
  Printexc.record_backtrace true;
  try doit () with
  | Failure s -> Error s
  | e ->
      Error
        (Printexc.record_backtrace false;
         "Internal error. Please report this.\n\n" ^ Printexc.to_string e ^ "\n"
         ^ Printexc.get_backtrace ())

let ok s =
  object%js
    val result = Js.(some @@ string s)
    val error = Js.null
  end

let err s =
  object%js
    val result = Js.null
    val error = Js.(some @@ string s)
  end

let ret = function Ok s -> ok s | Error s -> err s

let _ =
  Js.export "languages"
    ((Js.array @@ Array.of_list
     @@ List.map Js.string languages)
     [@jsdoc {|Target languages|}])

let _ =
  Js.export "phases"
    ((Js.array @@ Array.of_list @@ List.map Js.string phases)
     [@jsdoc {|Compiler target phases|}])

let _ =
  Js.export "emits"
    ((Js.array @@ Array.of_list @@ List.map Js.string emits)
     [@jsdoc {|Compiler target emits|}])

let _ =
  Js.export "userProgram" (fun [@jsdoc {|Gets raw user program|}] prog ->
      Js.string @@ user_ann_program @@ raw_program_of_string
      @@ Js.to_string prog)

let find_language l =
  find_language l |> Option.to_result ~none:("No language " ^ l)

let phase_of_string s =
  phase_of_string s |> Option.to_result ~none:("No phase " ^ s)

let emit_of_string s =
  emit_of_string s |> Option.to_result ~none:("No emit " ^ s)

let compile prog lang phase emit =
  let ( >>= ) = Result.bind in
  let raw_program = raw_program_of_string @@ prog in

  find_language lang >>= fun lang_mod ->
  phase_of_string phase >>= fun phase ->
  emit_of_string emit >>= fun emit ->
  let { program; _ } = preprocess raw_program in

  process_one lang_mod program (phase, emit)
  |> Result.map_error string_of_compile_err
  |> Result.map string_of_compile_output

let _ =
  Js.export "compile"
    (fun
      [@jsdoc
        {|Compiles a program under a given language to a given phase, and returns the give emit|}] 
      ~prog
      ~lang
      ~phase
      ~emit
    ->
      let prog, lang, phase, emit =
        ( Js.to_string prog,
          Js.to_string lang,
          Js.to_string phase,
          Js.to_string emit )
      in
      ret @@ wrap (fun () -> compile prog lang phase emit))
