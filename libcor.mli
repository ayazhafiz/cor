module type LANGUAGE

val languages : string list

val find_language : string -> (module LANGUAGE) option
(** Returns the [LANGUAGE] module given a string of the language name. Is
    [None] if no such language exists. *)

type phase
type emit

val phases : string list
val emits : string list

val phase_of_string : string -> phase option
(** Returns the phase given a string of the same name. Is [None] if no
    such phase exists. *)

val emit_of_string : string -> emit option
(** Returns the emit given a string of the same name. Is [None] if no
    such emit exists. *)

type command = phase * emit
type command_err

val string_of_command_err : command_err -> string

type raw_program
(** Raw user program. Use [raw_program_of_string] to create. *)

val raw_program_of_string : string -> raw_program
val raw_program_of_lines : string list -> raw_program

val user_ann_program : raw_program -> string
(** User annotated program: with queries, but without commands and outputs. *)

type program
(** Processed program. *)

type preprocessed = {
  raw_program : raw_program;
  program : program;
  commands : (command, command_err) result list;
}

val preprocess : raw_program -> preprocessed
(** Pre-processes a raw program. *)

type compile_output
type compile_err
type compile_result = (compile_output, compile_err) result

val process_one : (module LANGUAGE) -> program -> command -> compile_result
(** Processes a program with one command, returning the output. *)

val string_of_compile_err : compile_err -> string
(** Converts a [compile_err] to a string. *)

val string_of_compile_output : compile_output -> string
(** Converts a [compile_output] to a string. *)

val postprocess : raw_program -> (command * compile_output) list -> string
(** Pretty-prints the raw program, all commands, and their output to a buffer.
    [postprocess] guarantees the invariant its output will be idempotent under
    [preprocess] and [process_one] of the commands in order. *)

val hover_info :
  (module LANGUAGE) ->
  raw_program ->
  Language.lineco ->
  Language.hover_info option
