open Syntax
open Util
open Language

type ctx = { fresh_var : unit -> string }

let new_ctx () =
  let fresh_var =
    let i = ref 0 in
    function
    | () ->
        incr i;
        Printf.sprintf "%%%d" !i
  in
  { fresh_var }

type layout =
  | Void  (** unreachable layout *)
  | Int
  | Struct of layout list  (** { layout_1, .., layout_n } *)
  | Union of layout list list
      (** { tag, Struct { ...layout_1 } | ... | Struct { ...layout_n } } *)
[@@deriving show]

type var = layout * string [@@deriving show]

type expr =
  | Var of var
  | GetTagId of var
  | BuildTag of layout * int * var
  | BuildStruct of var list
  | GetStructField of int * var

type stmt =
  | Let of var * expr
  | Switch of {
      cond : var;
      branches : (int * (stmt list * var)) list;
      join : var;
    }

type program = Program of stmt list * var

let tag_id ctor ty =
  match unlink ty with
  | TTag tags -> index_of (fun (name, _) -> name = ctor) !tags
  | _ -> failwith "unreachable"

let layout_of_type =
  let rec go t =
    let t = unlink t in
    match t with
    | TVar v -> (
        match !v with
        | Unbd _ -> Void (* unused, so we can compile as void *)
        | Link _ -> failwith "unreachable")
    | TTag tags -> (
        let tags = !tags in
        let tag_layouts = List.map (fun (_, args) -> List.map go args) tags in
        match tag_layouts with
        | [] -> Void
        (*
        | [ [ one ] ] -> one
        | [ struct' ] -> Struct struct'
        *)
        | many -> Union many)
  in
  go

(* fmt *)

let pp_layout f =
  let open Format in
  let rec go = function
    | Void -> fprintf f "void"
    | Int -> fprintf f "int"
    | Struct layouts ->
        if layouts = [] then fprintf f "{}"
        else (
          fprintf f "{ ";
          intersperse f ", " (fun _ _ lay -> go lay) layouts;
          fprintf f " }")
    | Union variants ->
        fprintf f "[ ";
        intersperse f ", "
          (fun f i payloads ->
            fprintf f "`%d" i;
            List.iter
              (fun l ->
                fprintf f " ";
                go l)
              payloads)
          variants;
        fprintf f " ]"
  in
  go

let pp_var f (layout, s) =
  let open Format in
  fprintf f "%s : " s;
  pp_layout f layout

let pp_vs f (_, s) =
  let open Format in
  fprintf f "%s" s

let pp_expr f =
  let open Format in
  function
  | Var var -> pp_var f var
  | GetTagId v ->
      fprintf f "@get_tag_id ";
      pp_vs f v
  | BuildTag (_, id, var) ->
      fprintf f "@build_tag %d " id;
      pp_vs f var
  | BuildStruct vars ->
      fprintf f "@build_struct";
      List.iter
        (fun v ->
          fprintf f " ";
          pp_vs f v)
        vars
  | GetStructField (i, var) ->
      fprintf f "@get_field %d " i;
      pp_vs f var

let pp_stmt f =
  let open Format in
  let rec go = function
    | Let (var, expr) ->
        fprintf f "let ";
        pp_var f var;
        fprintf f " = ";
        pp_expr f expr;
        fprintf f ";"
    | Switch { cond; branches; join } ->
        fprintf f "@[<v 0>@[<v 2>switch ";
        pp_vs f cond;
        fprintf f " {";
        List.iter
          (fun (i, (stmts, last)) ->
            fprintf f "@,@[<v 0>@[<v 2>%d: {" i;
            List.iter
              (fun s ->
                fprintf f "@,";
                go s)
              stmts;
            fprintf f "@,feed ";
            pp_vs f last;
            fprintf f "@]@,}@]")
          branches;
        fprintf f "@]@,} in join ";
        pp_var f join;
        fprintf f "@]"
  in
  go

let pp_prog f =
  let open Format in
  function
  | Program (stmts, var) ->
      fprintf f "@[<v 0>";
      List.iter
        (fun stmt ->
          pp_stmt f stmt;
          fprintf f "@,")
        stmts;
      fprintf f "ret ";
      pp_vs f var;
      fprintf f "@]"

let string_of_program ?(width = default_width) p =
  with_buffer (fun f -> pp_prog f p) width
