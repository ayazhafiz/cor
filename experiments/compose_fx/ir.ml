open Util
open Language

type function_name = [ `Fn of string ]

type layout =
  | Str
  | Struct of layout list
  | Union of layout list list
  | Box of layout
  | FunctionPointer

type var = layout * string

type expr =
  | Var of var
  | MakeUnion of int * var
  | GetUnionId of var
  | GetUnionStruct of var
  | MakeStruct of var list
  | GetStructField of int * var
  | CallIndirect of var * var
  | Box of var
  | Unbox of var
  | MakeErased of function_name * var
  | GetErasedFn of var
  | GetErasedData of var

type stmt = Let of var * expr | Return of expr
type proc = { name : string; args : var list; body : stmt list; ret : layout }
type entry_point = { name : string; body : stmt list }
type program = { procs : proc list; entry_points : entry_point list }

let rec pp_layout : Format.formatter -> layout -> unit =
 fun f l ->
  let open Format in
  let rec go = function
    | Str -> fprintf f "str"
    | Struct [] -> fprintf f "{}"
    | Struct layouts ->
        fprintf f "@[<v 0>{@;<0 2>@[<v 0>";
        intersperse f ",@ " (fun _ _ lay -> go lay) layouts;
        fprintf f "@]%t}@]"
          (pp_print_custom_break ~fits:("", 0, "") ~breaks:(",", 0, ""))
    | Union [] -> fprintf f "[]"
    | Union variants ->
        fprintf f "@[<v 0>[@;<0 2>@[<v 0>";
        intersperse f ",@ "
          (fun f i payloads ->
            fprintf f "`%d " i;
            go (Struct payloads);
            fprintf f "@,")
          variants;
        fprintf f "@]%t]@]"
          (pp_print_custom_break ~fits:("", 0, "") ~breaks:(",", 0, ""))
    | Box lay -> fprintf f "@[<hv 2>box<@,%a>@]" pp_layout lay
    | FunctionPointer -> fprintf f "*fn"
  in
  go l

let pp_var : Format.formatter -> var -> unit =
 fun f (lay, name) -> Format.fprintf f "@[<hv 2>%s :@ %a@]" name pp_layout lay

let pp_vs : Format.formatter -> var list -> unit =
 fun f vs ->
  Format.fprintf f "@[<v 2>";
  List.iter (fun v -> Format.fprintf f "%a,@ " pp_var v) vs;
  Format.fprintf f "@]"

let pp_expr : Format.formatter -> expr -> unit =
  let open Format in
  fun f -> function
    | Var v -> fprintf f "%a" pp_var v
    | MakeUnion (i, v) ->
        fprintf f "@[<hv 2>@make_union<@,%d,@ %a>@]" i pp_var v
    | GetUnionId v -> fprintf f "@[<hv 2>@get_union_id<@,%a>@]" pp_var v
    | GetUnionStruct v -> fprintf f "@[<hv 2>@get_union_struct<@,%a>@]" pp_var v
    | MakeStruct vs -> fprintf f "@[<hv 2>@make_struct<@,%a>@]" pp_vs vs
    | GetStructField (i, v) ->
        fprintf f "@[<hv 2>@get_struct_field<@,%d,@ %a>@]" i pp_var v
    | CallIndirect (v1, v2) ->
        fprintf f "@[<hv 2>@call_indirect<@,%a,@ %a>@]" pp_var v1 pp_var v2
    | Box v -> fprintf f "@[<hv 2>@box<@,%a>@]" pp_var v
    | Unbox v -> fprintf f "@[<hv 2>@unbox<@,%a>@]" pp_var v
    | MakeErased (`Fn name, v) ->
        fprintf f "@[<hv 2>@make_erased<@,%s,@ %a>@]" name pp_var v
    | GetErasedFn v -> fprintf f "@[<hv 2>@get_erased_fn<@,%a>@]" pp_var v
    | GetErasedData v -> fprintf f "@[<hv 2>@get_erased_data<@,%a>@]" pp_var v

let pp_stmt : Format.formatter -> stmt -> unit =
  let open Format in
  fun f -> function
    | Let (v, e) -> fprintf f "@[<hv 2>let %a =@ %a;@]" pp_var v pp_expr e
    | Return e -> fprintf f "@[<hv 2>return@ %a;@]" pp_expr e

let pp_proc : Format.formatter -> proc -> unit =
  let open Format in
  fun f { name; args; body; ret } ->
    fprintf f "@[<v 2>proc %s %a :@ %a@,{@;<0 2>@[<v 0>" name pp_vs args
      pp_layout ret;
    intersperse f "@," (fun _ _ stmt -> pp_stmt f stmt) body;
    fprintf f "@]@,}@]"

let pp_entry_point : Format.formatter -> entry_point -> unit =
  let open Format in
  fun f { name; body } ->
    fprintf f "@[<v 2>entry_point %s@,{@;<0 2>@[<v 0>" name;
    intersperse f "@," (fun _ _ stmt -> pp_stmt f stmt) body;
    fprintf f "@]@,}@]"

let pp_program : Format.formatter -> program -> unit =
  let open Format in
  fun f { procs; entry_points } ->
    fprintf f "@[<v 0>";
    List.iter (fun p -> fprintf f "%a@," pp_proc p) procs;
    List.iter (fun p -> fprintf f "%a@," pp_entry_point p) entry_points;
    fprintf f "@]"

let string_of_program ?(width = default_width) p =
  with_buffer (fun f -> pp_program f p) width
