open Can
open Symbol
open Type

type ready_specialization = [ `Letval of letval | `Letfn of letfn ]

type specialized = {
  specializations : ready_specialization list;
  entry_points : (symbol * tvar) list;
}

let pp_specialized : Format.formatter -> specialized -> unit =
 fun f { specializations; entry_points } ->
  let pp_entry_point f (sym, _) =
    Format.fprintf f "@[<hov 2>%s@]@." (Symbol.norm_of sym)
  in
  let pp_specialization f = function
    | `Letval letval -> Format.fprintf f "@[%a@]" Can.pp_letval letval
    | `Letfn letfn -> Format.fprintf f "@[%a@]" Can.pp_letfn letfn
  in
  Format.fprintf f "@[<v 2>entry_points:@,";
  List.iter (pp_entry_point f) entry_points;
  Format.fprintf f "@]@.";
  Format.fprintf f "@[<v 2>specializations:@,";
  List.iter
    (fun s ->
      pp_specialization f s;
      Format.fprintf f "@,")
    specializations;
  Format.fprintf f "@]@."

let show_specialized specialized =
  Util.with_buffer (fun f -> pp_specialized f specialized) 80
