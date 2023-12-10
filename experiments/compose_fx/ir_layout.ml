open Ir
open Ir_ctx
open Type

let unlink_tvar tvar =
  let rec go tvar =
    match tvar_deref tvar with
    | Link tvar -> go tvar
    | Content (TFn (_, ls, _)) -> go ls
    | Alias { real; _ } -> go real
    | _ -> tvar
  in
  go tvar

let layout_of_tvar : ctx -> tvar -> layout =
 fun { cache; fresh_rec_id; _ } tvar ->
  let rec go tvar : layout =
    let tvar = unlink_tvar tvar in
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
          | Content (TFn _) -> failwith "impossible"
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
          | Content (TLambdaSet { lambdas; ambient_fn = _ }) ->
              let translate_lam : ty_lambda -> layout =
               fun { lambda = _; captures } ->
                let args = List.map go captures in
                ref @@ Struct args
              in
              let lams = List.map translate_lam lambdas in
              let union = Union lams in
              union
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
  | _ -> failwith "unreachable: not a tag"

let unpack_lambda_set ty =
  let rec go ty =
    match tvar_deref @@ unlink_w_alias ty with
    | Content (TFn (_, lset, _)) -> go lset
    | Content (TLambdaSet lset) -> lset
    | _ -> failwith "unreachable: not a lambda set"
  in
  go ty

let is_lay_equiv : layout -> layout -> bool =
 fun l1 l2 ->
  let visited_recs = ref [] in
  let rec go l1 l2 =
    match (!l1, !l2) with
    | Str, Str -> true
    | Int, Int -> true
    | Struct ls1, Struct ls2 ->
        if List.length ls1 <> List.length ls2 then false
        else List.for_all2 go ls1 ls2
    | Union ls1, Union ls2 ->
        if List.length ls1 <> List.length ls2 then false
        else List.for_all2 go ls1 ls2
    | Box (l1, Some x1), Box (l2, Some x2) ->
        if x1 = x2 then true
        else if List.mem (x1, x2) !visited_recs then true
        else (
          visited_recs := (x1, x2) :: !visited_recs;
          go l1 l2)
    | Box (l1, None), Box (l2, None) -> go l1 l2
    | Box (_, Some _), Box (_, None) -> false
    | Box (_, None), Box (_, Some _) -> false
    | Erased, Erased -> true
    | FunctionPointer, FunctionPointer -> true
    | _ -> false
  in
  go l1 l2
