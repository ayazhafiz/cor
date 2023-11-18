open Util
open Language

type function_name = [ `Fn of string ]
type rec_id = [ `Rec of int ]

type layout_repr =
  | Str
  | Struct of layout list
  | Union of layout list
  | Box of layout * rec_id option
  | Erased
  | FunctionPointer

and layout = layout_repr ref

type var_name = [ `Var of string ] [@@deriving show]
type var = layout * var_name

type expr =
  | Var of var
  | MakeUnion of int * var
  | GetUnionId of var
  | GetUnionStruct of var
  | MakeStruct of var list
  | GetStructField of var * int
  | CallIndirect of var * var list
  | CallDirect of function_name * var list
  | MakeBox of var
  | GetBoxed of var
  | PtrCast of var * layout
  | MakeFnPtr of function_name

type stmt = Let of var * expr

type proc = {
  name : function_name;
  args : var list;
  body : stmt list;
  ret : var;
}

type global = { name : var_name; layout : layout; init : expr }
type definition = Proc of proc | Global of global
type program = { definitions : definition list; entry_points : var_name list }

let pp_rec_id : Format.formatter -> rec_id -> unit =
 fun f (`Rec i) -> Format.fprintf f "%%type_%d" i

let rec pp_layout : Format.formatter -> layout -> unit =
 fun f l ->
  let open Format in
  let seen_recs : rec_id list ref = ref [] in
  match !l with
  | Str -> fprintf f "str"
  | Struct [] -> fprintf f "{}"
  | Struct layouts ->
      (* format as { lay1, lay2, lay3 } *)
      (* or
         {
           lay1,
           lay2,
           lay3,
         }
         if a break is required
      *)
      fprintf f "@[<hv 0>{@[<hv 0>@ ";
      List.iteri
        (fun i lay ->
          pp_layout f lay;
          if i < List.length layouts - 1 then fprintf f ",@, ")
        layouts;
      fprintf f "@ @]%t}@]"
        (pp_print_custom_break ~fits:("", 0, "") ~breaks:(",", 0, ""))
  | Union [] -> fprintf f "[]"
  | Union variants ->
      (* format as [ lay1, lay2, lay3 ] *)
      (* or
         [
           lay1,
           lay2,
           lay3,
         ]
         if a break is required
      *)
      fprintf f "@[<hv 0>[@[<hv 0>@ ";
      List.iteri
        (fun i lay ->
          fprintf f "`%d %a" i pp_layout lay;
          if i < List.length variants - 1 then fprintf f ",@, ")
        variants;
      fprintf f "@ @]%t]@]"
        (pp_print_custom_break ~fits:("", 0, "") ~breaks:(",", 0, ""))
  | Box (_, Some r) when List.mem r !seen_recs ->
      fprintf f "@[<hv 2>box<%a>@]" pp_rec_id r
  | Box (lay, Some r) ->
      fprintf f "@[<hv 2>box<@,%a =@ %a>@]" pp_rec_id r pp_layout lay
  | Box (lay, None) -> fprintf f "@[<hv 2>box<@,%a>@]" pp_layout lay
  | Erased -> fprintf f "erased"
  | FunctionPointer -> fprintf f "*fn"

let show_layout = Format.asprintf "%a" pp_layout

let pp_var : Format.formatter -> var -> unit =
 fun f (lay, `Var name) ->
  Format.fprintf f "@[<hv 2>%s:@ %a@]" name pp_layout lay

let pp_v_name : Format.formatter -> var -> unit =
 fun f (_, `Var name) -> Format.fprintf f "%s" name

let pp_v_names : Format.formatter -> var list -> unit =
 fun f vs ->
  List.iteri
    (fun i (_, `Var name) ->
      Format.fprintf f "%s" name;
      if i < List.length vs - 1 then Format.fprintf f ",@, ")
    vs

let pp_expr : Format.formatter -> expr -> unit =
  let open Format in
  fun f -> function
    | Var v -> fprintf f "%a" pp_v_name v
    | MakeUnion (i, v) ->
        fprintf f "@[<hv 2>@make_union<@,%d,@ %a>@]" i pp_v_name v
    | GetUnionId v -> fprintf f "@[<hv 2>@get_union_id<@,%a>@]" pp_v_name v
    | GetUnionStruct v ->
        fprintf f "@[<hv 2>@get_union_struct<@,%a>@]" pp_v_name v
    | MakeStruct vs ->
        let pp_vs f = function
          | [] -> ()
          | vs -> fprintf f "@ %a@ " pp_v_names vs
        in
        fprintf f "@[<hov 0>@make_struct{%a%t}@]" pp_vs vs
          (pp_print_custom_break ~fits:("", 0, "") ~breaks:(";", 0, ""))
    | GetStructField (v, i) ->
        fprintf f "@[<hv 2>@get_struct_field<@,%a,@ %d>@]" pp_v_name v i
    | CallIndirect (var, args) ->
        let pp_args f = function
          | [] -> ()
          | args -> fprintf f ",@ %a" pp_v_names args
        in
        fprintf f "@[<hv 2>@call_indirect(@,%a%a)@]" pp_v_name var pp_args args
    | CallDirect (`Fn name, args) ->
        let pp_args f = function
          | [] -> ()
          | args -> fprintf f ",@ %a" pp_v_names args
        in
        fprintf f "@[<hv 2>@call_direct(@,%s%a)@]" name pp_args args
    | MakeBox v -> fprintf f "@[<hv 2>@make_box(@,%a)@]" pp_v_name v
    | GetBoxed v -> fprintf f "@[<hv 2>@get_boxed<@,%a>@]" pp_v_name v
    | PtrCast (v, lay) ->
        fprintf f "@[<hv 2>@ptr_cast(@,%a as@ %a)@]" pp_v_name v pp_layout lay
    | MakeFnPtr (`Fn name) -> fprintf f "@[<hv 2>@make_fn_ptr<@,%s>@]" name

let pp_stmt : Format.formatter -> stmt -> unit =
  let open Format in
  fun f -> function
    | Let (v, e) -> fprintf f "@[<hv 2>let %a =@ %a;@]" pp_var v pp_expr e

let pp_proc : Format.formatter -> proc -> unit =
  let open Format in
  fun f { name = `Fn name; args; body; ret = ret_lay, `Var ret_x } ->
    let pp_args f = function
      | [] -> ()
      | args ->
          List.iteri
            (fun i v ->
              fprintf f "%a" pp_var v;
              if i < List.length args - 1 then fprintf f ",@, ")
            args
    in

    fprintf f
      "@[<hov 0>@[<hv 2>@[<hv 2>proc %s(@,%a)@]:@ %a@]@ @[{@;<0 2>@[<v 0>" name
      pp_args args pp_layout ret_lay;
    List.iter (fun s -> fprintf f "%a@," pp_stmt s) body;
    fprintf f "return %s;@]@,@]}@]" ret_x

let pp_global : Format.formatter -> global -> unit =
  let open Format in
  fun f { name = `Var name; layout; init } ->
    fprintf f "@[<hv 2>global %s:@ %a@ = %a;@]" name pp_layout layout pp_expr
      init

let pp_definition : Format.formatter -> definition -> unit =
 fun f -> function Proc p -> pp_proc f p | Global g -> pp_global f g

let pp_program : Format.formatter -> program -> unit =
  let open Format in
  fun f { definitions; entry_points } ->
    fprintf f "@[<v 0>";
    List.iter (fun p -> fprintf f "%a@,@," pp_definition p) definitions;
    List.iteri
      (fun i (`Var name) ->
        fprintf f "@[entry %s;@]" name;
        if i < List.length entry_points - 1 then fprintf f "@,")
      entry_points;
    fprintf f "@]"

let string_of_program ?(width = default_width) p =
  with_buffer (fun f -> pp_program f p) width
