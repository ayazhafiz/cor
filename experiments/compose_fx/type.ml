open Loc
open Symbol

type variable = [ `Var of int ] [@@deriving show]

type loc_tvar = loc * tvar
and ty_tag = string * loc_tvar list

(** Concrete type content *)
and ty_content =
  | TFn of loc_tvar * loc_tvar
  | TTag of { tags : ty_tag list; ext : loc_tvar }
  | TTagEmpty
  | TPrim of [ `Str | `Int | `Unit ]

and ty_alias_content = { alias : loc_symbol * loc_tvar list; real : tvar }

and ty =
  | Link of tvar  (** Link to a type *)
  | Unbd of string option
  | ForA of string option  (** generalized type *)
  | Content of ty_content
  | Alias of ty_alias_content

and tvar = { ty : ty ref; var : variable; recur : bool ref } [@@deriving show]
(** Mutable type cell *)

let tvar_deref tvar = !(tvar.ty)
let tvar_set tvar ty = tvar.ty := ty

let tvar_set_recur tvar recur =
  if !(tvar.recur) && not recur then failwith "recursive type variable";
  tvar.recur := recur

let tvar_recurs tvar = !(tvar.recur)
let tvar_v tvar = tvar.var

let tvar_int =
  { ty = ref (Content (TPrim `Int)); var = `Var 0; recur = ref false }

let tvar_str =
  { ty = ref (Content (TPrim `Str)); var = `Var 1; recur = ref false }

let min_var = 1000

let rec unlink tvar =
  match tvar_deref tvar with Link t -> unlink t | _ -> tvar

let rec unlink_w_alias tvar =
  match tvar_deref tvar with
  | Link t -> unlink_w_alias t
  | Alias { real; _ } -> unlink_w_alias real
  | _ -> tvar

let chase_tags tags ext : ty_tag list * tvar =
  let rec go : ty_tag list -> tvar -> _ =
   fun all_tags ext ->
    match tvar_deref @@ unlink ext with
    | Link _ -> failwith "unreachable"
    | Unbd _ -> (all_tags, ext)
    | ForA _ -> (all_tags, ext)
    | Content TTagEmpty -> (all_tags, ext)
    | Content (TTag { tags; ext }) -> go (all_tags @ tags) (snd ext)
    | Content (TFn _) -> failwith "not a tag"
    | Content (TPrim _) -> failwith "not a tag"
    | Alias { real; _ } -> go all_tags real
  in
  go tags ext
