open Ir
open Type

let erased_captures_lay = ref @@ Box (ref @@ Erased, None)
let closure_repr = Struct [ ref @@ FunctionPointer; erased_captures_lay ]

let layout_of_tvar : ctx -> tvar -> layout =
 fun { cache; fresh_rec_id; _ } tvar ->
  let rec go tvar : layout =
    let tvar = unlink_w_alias tvar in
    let var = tvar_v tvar in
    match List.assoc_opt var !cache with
    | Some layout ->
        if !layout = Union [] then
          (* NB: late recursion-setting. If we failed to find a recursion point
             earlier on, we opportunistically set it now. *)
          tvar_set_recur tvar true;
        layout
    | None ->
        let lay = ref @@ Union [] in
        cache := (var, lay) :: !cache;
        let repr =
          match tvar_deref tvar with
          | Link _ -> failwith "impossible"
          | Alias _ -> failwith "impossible"
          | Unbd _ -> Union []
          | ForA _ -> failwith "impossible after monomorphization"
          | Content (TPrim `Str) -> Str
          | Content (TPrim `Int) -> Int
          | Content (TPrim `Unit) -> Struct []
          | Content TTagEmpty -> Union []
          | Content (TTag { tags; ext = _, ext }) ->
              let tags, _ext = chase_tags tags ext in
              let translate_tag : ty_tag -> layout =
               fun (_, args) ->
                let struct' = List.map go @@ List.map snd @@ args in
                ref @@ Struct struct'
              in
              let tags = List.map translate_tag tags in
              let union = Union tags in
              union
          | Content (TFn (_, _)) -> closure_repr
        in
        let recurs = tvar_recurs tvar in
        let repr =
          if recurs then Box (ref @@ repr, Some (fresh_rec_id ())) else repr
        in
        lay := repr;
        lay
  in
  go tvar

let tag_id ctor ty =
  match tvar_deref @@ unlink_w_alias ty with
  | Content (TTag { tags; ext = _ }) ->
      Util.index_of (fun (name, _) -> name = ctor) tags
  | _ -> failwith "unreachable"
