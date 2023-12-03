open Can
open Symbol
open Type

type ready_specialization =
  [ `Letval of letval | `Letfn of letfn * bool (* true=leave witness *) ]

type specialized = {
  specializations : ready_specialization list;
  entry_points : (symbol * tvar) list;
}

let pp_specialized : Format.formatter -> specialized -> unit =
 fun f { specializations; entry_points } ->
  let pp_entry_point f (sym, _) =
    Format.fprintf f "@[<hov 2>%s@]" (Symbol.norm_of sym)
  in
  let pp_specialization f = function
    | `Letval letval -> Format.fprintf f "@[%a@]" Can.pp_letval letval
    | `Letfn (letfn, _) -> Format.fprintf f "@[%a@]" Can.pp_letfn letfn
  in
  Format.fprintf f "@[<v 2>specializations:@,";
  List.iter
    (fun s ->
      pp_specialization f s;
      Format.fprintf f "@,@,")
    specializations;
  Format.fprintf f "@]@.";
  Format.fprintf f "@[<v 2>entry_points:@,";
  List.iteri
    (fun i ep ->
      pp_entry_point f ep;
      if i < List.length entry_points - 1 then Format.fprintf f "@.")
    entry_points;
  Format.fprintf f "@]"

let string_of_specialized ~width specialized =
  Util.with_buffer (fun f -> pp_specialized f specialized) width

let show_specialized specialized = string_of_specialized ~width:80 specialized
