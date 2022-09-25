let with_buffer cb width =
  let open Format in
  let b = Buffer.create 32 in
  let f = formatter_of_buffer b in
  pp_set_margin f width;
  cb f;
  pp_print_flush f ();
  Buffer.to_seq b |> String.of_seq

module StringMap = Map.Make (struct
  type t = string

  let compare = compare
end)

let index_of pred l =
  let rec help n = function
    | [] -> raise Not_found
    | c :: rest -> if pred c then n else help (n + 1) rest
  in
  help 0 l

let intersperse f between fn iter =
  List.iteri
    (fun i elt ->
      if i <> 0 then Format.fprintf f "%s" between;
      fn f i elt)
    iter
