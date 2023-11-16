open Ir
module S = Syntax

let layout_of_tvar : S.tvar -> layout = function
  | tvar ->
      let visited = ref [] in
      let go tvar =
        let tvar = S.unlink tvar in
        let var = S.tvar_v tvar in
        match List.assoc_opt var !visited with
        | Some layout -> layout
        | None -> failwith ""
      in
      go tvar
