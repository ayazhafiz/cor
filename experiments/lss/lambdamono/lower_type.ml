open Symbol
open Type
module T = Lambdasolved.Type
module P = Lambdasolved.Type_print

type mono_cache = (T.variable * tvar) list ref

let fresh_mono_cache () : mono_cache = ref []

let extract_fn ty =
  match T.tvar_deref @@ T.unlink ty with
  | T.Content (T.TFn (in', lset, out')) -> (in', lset, out')
  | _ -> failwith @@ "expected function type, got " ^ P.show_ty ty

let lambda_tag_name s =
  match Symbol.show_symbol_raw s |> String.to_seq |> List.of_seq with
  | c :: rest -> Char.uppercase_ascii c :: rest |> List.to_seq |> String.of_seq
  | _ -> assert false

let ty_unfilled () = TTag [ ("__unfilled_lambdamono", []) ]

let rec unlink_to_lset : T.tvar -> T.tvar =
 fun tvar ->
  match T.tvar_deref tvar with
  | T.Link tvar -> unlink_to_lset tvar
  | T.Content (T.TFn (_, lset, _)) -> unlink_to_lset lset
  | _ -> tvar

let lower_type : mono_cache -> fresh_tvar -> T.tvar -> tvar =
 fun cache fresh_tvar ty ->
  let rec lower_lambda_set (lambdas : T.lambda_set) : ty_content =
    let bindings = SymbolMap.bindings lambdas in
    let bindings =
      List.map
        (fun (name, captures) ->
          ( lambda_tag_name name,
            if SymbolMap.is_empty captures then []
            else [ fresh_tvar @@ lower_captures captures ] ))
        bindings
    in
    TTag bindings
  and lower_captures (captures : T.captures) : ty_content =
    let bindings = SymbolMap.bindings captures in
    let bindings =
      List.map
        (fun (name, ty) -> (Symbol.show_symbol_raw name, lower_tvar ty))
        bindings
    in
    TRecord bindings
  and lower_tag (tag, args) = (tag, List.map lower_tvar args)
  and lower_field (field, ty) = (field, lower_tvar ty)
  and lower_tvar tvar : tvar =
    let tvar = unlink_to_lset tvar in
    let var = T.tvar_v tvar in
    match List.assoc_opt var !cache with
    | Some ty -> ty
    | None ->
        let ty = fresh_tvar (ty_unfilled ()) in
        cache := (var, ty) :: !cache;
        let content =
          match T.tvar_deref tvar with
          | T.Link _ -> failwith "unexpected link"
          | T.ForA -> failwith "unexpected generalized type"
          | T.Unbd -> TTag []
          | T.Content (T.LSet lset) -> lower_lambda_set lset
          | T.Content (T.TFn _) -> failwith "unexpected function"
          | T.Content (T.TTag tags) -> TTag (List.map lower_tag tags)
          | T.Content (T.TRecord fields) ->
              TRecord (List.map lower_field fields)
          | T.Content (T.TPrim p) -> TPrim p
        in
        tvar_set ty content;
        ty
  in
  let ty = lower_tvar ty in
  ty

type extracted_closure_captures = { captures : (symbol * tvar) list; ty : tvar }

let extract_lambda_set ty =
  let _in, lset, _out = extract_fn ty in
  let lset = T.unlink lset in
  match T.tvar_deref @@ lset with
  | T.Content (LSet lset) -> lset
  | _ ->
      failwith @@ "expected lambda set type, got " ^ P.show_ty lset ^ "\n"
      ^ P.show_ty ty

let extract_lambda_capture_types ty lambda =
  let lset = extract_lambda_set ty in
  let captures = SymbolMap.find lambda lset in
  SymbolMap.bindings captures

let extract_closure_captures :
    mono_cache ->
    fresh_tvar ->
    T.tvar ->
    symbol ->
    extracted_closure_captures option =
 fun mono_cache fresh_tvar ty name ->
  let t_lset = lower_type mono_cache fresh_tvar ty in
  match tvar_deref t_lset with
  | TTag bindings ->
      let captures_list =
        match List.assoc_opt (lambda_tag_name name) bindings with
        | Some binding -> binding
        | None ->
            failwith @@ "expected tag " ^ lambda_tag_name name
            ^ " to be available in " ^ P.show_ty ty
      in
      if List.length captures_list = 0 then None
      else (
        assert (List.length captures_list = 1);
        let t_captures = List.hd captures_list in
        match tvar_deref t_captures with
        | TRecord bindings ->
            let captures =
              List.map (fun (k, v) -> (Symbol.unsafe_from_string k, v)) bindings
            in
            Some { captures; ty = t_captures }
        | _ -> failwith "expected record")
  | _ -> failwith "expected tag"
