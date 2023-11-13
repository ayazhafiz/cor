open Syntax

let inst : fresh_tvar -> tvar -> tvar =
 fun fresh_tvar tvar ->
  let tenv : (variable * tvar) list ref = ref [] in
  let rec go : tvar -> tvar =
   fun t ->
    let var = tvar_v t in
    match List.assoc_opt var !tenv with
    | Some t -> t
    | None ->
        let t' =
          match tvar_deref t with
          | Unbd _ -> t
          | Link t -> go t
          | ForA x -> fresh_tvar (Unbd x)
          | Content (TPrim (`Str | `Unit)) | Content TTagEmpty -> t
          | Content (TTag { tags; ext = _, ext }) ->
              let map_tag : ty_tag -> ty_tag =
               fun (tag, args) ->
                let args = List.map (fun (_, t) -> (noloc, go t)) args in
                (tag, args)
              in
              let tags = List.map map_tag tags in
              let ext = (noloc, go ext) in
              fresh_tvar @@ Content (TTag { tags; ext })
          | Content (TFn ((_, t1), (_, t2))) ->
              let t1 = (noloc, go t1) in
              let t2 = (noloc, go t2) in
              fresh_tvar @@ Content (TFn (t1, t2))
          | Alias { alias = name, args; real } ->
              let args = List.map (fun (_, t) -> (noloc, go t)) args in
              let real = go real in
              fresh_tvar @@ Alias { alias = (name, args); real }
        in
        tenv := (var, t') :: !tenv;
        t'
  in

  go tvar
