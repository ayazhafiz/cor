open Ir
module S = Syntax

let erased_captures_lay = ref @@ Box (ref @@ Erased, None)
let closure_repr = Struct [ ref @@ FunctionPointer; erased_captures_lay ]

let layout_of_tvar : ctx -> S.tvar -> layout =
 fun { cache; fresh_rec_id; _ } tvar ->
  let rec go tvar : layout =
    let tvar = S.unlink_w_alias tvar in
    let var = S.tvar_v tvar in
    match List.assoc_opt var !cache with
    | Some layout -> layout
    | None ->
        let lay = ref @@ Union [] in
        cache := (var, lay) :: !cache;
        let repr =
          match S.tvar_deref tvar with
          | S.Link _ -> failwith "impossible"
          | S.Alias _ -> failwith "impossible"
          | S.Unbd _ -> Union []
          | S.ForA _ -> Union [] (* TODO monomorphize *)
          | S.Content (S.TPrim `Str) -> Str
          | S.Content (S.TPrim `Int) -> Int
          | S.Content (S.TPrim `Unit) -> Struct []
          | S.Content S.TTagEmpty -> Union []
          | S.Content (S.TTag { tags; ext = _, ext }) ->
              let tags, _ext = S.chase_tags tags ext in
              let translate_tag : S.ty_tag -> layout =
               fun (_, args) ->
                let struct' = List.map go @@ List.map snd @@ args in
                ref @@ Struct struct'
              in
              let tags = List.map translate_tag tags in
              let union = Union tags in
              union
          | S.Content (S.TFn (_, _)) -> closure_repr
        in
        let recurs = S.tvar_recurs tvar in
        let repr =
          if recurs then Box (ref @@ repr, Some (fresh_rec_id ())) else repr
        in
        lay := repr;
        lay
  in
  go tvar

let tag_id ctor ty =
  match S.tvar_deref @@ S.unlink_w_alias ty with
  | S.Content (S.TTag { tags; ext = _ }) ->
      Util.index_of (fun (name, _) -> name = ctor) tags
  | _ -> failwith "unreachable"
