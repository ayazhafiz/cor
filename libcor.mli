module type LANGUAGE

val find_opt_lang : string -> (module LANGUAGE) option

type raw_program
type program_lines
type queries
type command

type preprocessed = {
  raw_program : raw_program;
  program_lines : program_lines;
  queries : queries;
  commands : command list;
}

val preprocess : string list -> preprocessed

type processed_command

val process_one :
  (module LANGUAGE) -> program_lines -> queries -> command -> processed_command

val postprocess : raw_program -> processed_command list -> string
