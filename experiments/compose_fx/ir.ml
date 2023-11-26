open Util
open Language
open Type
open Symbol

type rec_id = [ `Rec of int ] [@@deriving show]

type layout_repr =
  | Str
  | Int
  | Struct of layout list
  | Union of layout list
  | Box of layout * rec_id option
  | Erased
  | FunctionPointer

and layout = layout_repr ref

let layout_str = ref Str
let layout_int = ref Int

type var = layout * symbol
type lit = [ `Int of int | `String of string ]

type expr =
  | Var of var
  | Lit of lit
  | MakeUnion of int * var
  | GetUnionId of var
  | GetUnionStruct of var
  | MakeStruct of var list
  | GetStructField of var * int
  | CallIndirect of var * var list
  | CallDirect of symbol * var list
  | CallKFn of Syntax.kernelfn * var list
  | MakeBox of var
  | GetBoxed of var
  | PtrCast of var * layout
  | MakeFnPtr of symbol

type stmt =
  | Let of var * expr
  | Switch of {
      cond : var;
      branches : (int * (stmt list * expr)) list;
      join : var;
    }

type proc = { name : symbol; args : var list; body : stmt list; ret : var }
type global = { name : symbol; layout : layout; init : expr }
type definition = Proc of proc | Global of global

type program = {
  definitions : definition list;
  entry_points : (symbol * tvar) list;
}

type fresh_rec_id = unit -> rec_id
type layout_cache = (variable * layout) list ref

type ctx = {
  symbols : Symbol.t;
  cache : layout_cache;
  fresh_rec_id : fresh_rec_id;
  fresh_tvar : Syntax.fresh_tvar;
}

let new_ctx symbols fresh_tvar =
  let cache = ref [] in
  let next_id = ref 0 in
  let fresh_rec_id () =
    let id = !next_id in
    next_id := id + 1;
    `Rec id
  in
  { symbols; cache; fresh_rec_id; fresh_tvar }

let pp_rec_id : Format.formatter -> rec_id -> unit =
 fun f (`Rec i) -> Format.fprintf f "%%type_%d" i

let pp_layout : ?max_depth:int -> Format.formatter -> layout -> unit =
 fun ?(max_depth = 100) f l ->
  let seen_recs : rec_id list ref = ref [] in
  let rec go ?(max_depth = 100) f l =
    let go = go ~max_depth:(max_depth - 1) in
    let open Format in
    if max_depth <= 0 then fprintf f "..."
    else
      match !l with
      | Str -> fprintf f "str"
      | Int -> fprintf f "int"
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
              go f lay;
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
          fprintf f "@[<hv 0>[@[<hv 2>";
          List.iteri
            (fun i lay ->
              fprintf f "@ `%d %a" i go lay;
              if i < List.length variants - 1 then fprintf f ",")
            variants;
          fprintf f "@]@ ]@]"
      | Box (_, Some r) when List.mem r !seen_recs ->
          fprintf f "@[<hv 2>box<%a>@]" pp_rec_id r
      | Box (lay, Some r) ->
          seen_recs := r :: !seen_recs;
          fprintf f "@[<hv 2>box<@,%a =@ %a>@]" pp_rec_id r go lay
      | Box (lay, None) -> fprintf f "@[<hv 2>box<@,%a>@]" go lay
      | Erased -> fprintf f "erased"
      | FunctionPointer -> fprintf f "*fn"
  in
  go ~max_depth f l

let pp_layout_top = pp_layout ~max_depth:100
let show_layout ?(max_depth = 100) = Format.asprintf "%a" (pp_layout ~max_depth)

let rec show_layout_head l =
  match !l with
  | Str -> "str"
  | Int -> "int"
  | Struct [] -> "{}"
  | Struct layouts -> Format.sprintf "{%d}" (List.length layouts)
  | Union variants -> Format.sprintf "[%d]" (List.length variants)
  | Box (l, None) -> Format.sprintf "box<%s>" (show_layout_head l)
  | Box (l, Some r) ->
      Format.sprintf "box<%s = %s>" (show_rec_id r) (show_layout_head l)
  | Erased -> "erased"
  | FunctionPointer -> "*fn"

let pp_symbol : Format.formatter -> symbol -> unit =
 fun f s -> Format.fprintf f "%s" (Symbol.norm_of s)

let pp_var : Format.formatter -> var -> unit =
 fun f (lay, symbol) ->
  Format.fprintf f "@[<hov 2>%a:@ %a@]" pp_symbol symbol pp_layout_top lay

let pp_vars : Format.formatter -> var list -> unit =
 fun f vs ->
  List.iteri
    (fun i (lay, symbol) ->
      Format.fprintf f "%a:@ %a" pp_symbol symbol pp_layout_top lay;
      if i < List.length vs - 1 then Format.fprintf f ",@, ")
    vs

let pp_v_name : Format.formatter -> var -> unit =
 fun f (_, symbol) -> pp_symbol f symbol

let pp_v_names : Format.formatter -> var list -> unit =
 fun f vs ->
  List.iteri
    (fun i (_, symbol) ->
      Format.fprintf f "%a" pp_symbol symbol;
      if i < List.length vs - 1 then Format.fprintf f ",@, ")
    vs

let pp_expr : Format.formatter -> expr -> unit =
  let open Format in
  fun f -> function
    | Var v -> fprintf f "%a" pp_v_name v
    | Lit l -> (
        match l with
        | `Int i -> fprintf f "%d" i
        | `String s -> fprintf f "\"%s\"" @@ String.escaped s)
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
    | CallDirect (fn, args) ->
        let pp_args f = function
          | [] -> ()
          | args -> fprintf f ",@ %a" pp_v_names args
        in
        fprintf f "@[<hv 2>@call_direct(@,%a%a)@]" pp_symbol fn pp_args args
    | CallKFn (kfn, args) ->
        let pp_args f = function
          | [] -> ()
          | args -> fprintf f ",@ %a" pp_v_names args
        in
        fprintf f "@[<hv 2>@call_kfn(@,%s%a)@]"
          (List.assoc kfn Syntax.string_of_kernelfn)
          pp_args args
    | MakeBox v -> fprintf f "@[<hv 2>@make_box(@,%a)@]" pp_v_name v
    | GetBoxed v -> fprintf f "@[<hv 2>@get_boxed<@,%a>@]" pp_v_name v
    | PtrCast (v, lay) ->
        fprintf f "@[<hv 2>@ptr_cast(@,%a as@ %a)@]" pp_v_name v pp_layout_top
          lay
    | MakeFnPtr fn -> fprintf f "@[<hv 2>@make_fn_ptr<@,%a>@]" pp_symbol fn

let rec pp_stmt : Format.formatter -> stmt -> unit =
  let open Format in
  fun f -> function
    | Let (v, e) -> fprintf f "@[<hv 2>let %a@ = %a;@]" pp_var v pp_expr e
    | Switch { cond; branches; join } ->
        let pp_branch f (i, (lets, ret)) =
          fprintf f "@[<hv 0>@[<hv 2>%d -> {@,%a@,%a@]@,}@]" i
            (pp_print_list pp_stmt) lets pp_expr ret
        in
        fprintf f "@[<v 0>switch %a {@,%a@,} in join %a;@]" pp_v_name cond
          (pp_print_list pp_branch) branches pp_v_name join

let show_stmts stmts = Format.asprintf "%a" (Format.pp_print_list pp_stmt) stmts

let pp_proc : Format.formatter -> proc -> unit =
  let open Format in
  fun f { name; args; body; ret = ret_lay, ret_x } ->
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
      "@[<hov 0>@[<hv 2>@[<hv 2>proc %a(@,%a)@]:@ %a@]@ @[{@;<0 2>@[<v 0>"
      pp_symbol name pp_args args pp_layout_top ret_lay;
    List.iter (fun s -> fprintf f "%a@," pp_stmt s) body;
    fprintf f "return %a;@]@,@]}@]" pp_symbol ret_x

let pp_global : Format.formatter -> global -> unit =
  let open Format in
  fun f { name; layout; init } ->
    fprintf f "@[<hv 2>global %a:@ %a@ = %a;@]" pp_symbol name pp_layout_top
      layout pp_expr init

let pp_definition : Format.formatter -> definition -> unit =
 fun f -> function Proc p -> pp_proc f p | Global g -> pp_global f g

let pp_program : Format.formatter -> program -> unit =
  let open Format in
  fun f { definitions; entry_points } ->
    fprintf f "@[<v 0>";
    List.iter (fun p -> fprintf f "%a@,@," pp_definition p) definitions;
    List.iteri
      (fun i (name, _) ->
        fprintf f "@[entry %a;@]" pp_symbol name;
        if i < List.length entry_points - 1 then fprintf f "@,")
      entry_points;
    fprintf f "@]"

let string_of_program ?(width = default_width) p =
  with_buffer (fun f -> pp_program f p) width
