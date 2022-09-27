open Syntax
open Language

module IntMap = struct
  include Map.Make (struct
    type t = int

    let compare = compare
  end)
end

exception Solve_err of string

let failsolve s = raise (Solve_err s)

let occurs x =
  let rec go t =
    match !t with
    | Unbd n -> n = x
    | Link t -> go t
    | Content (TTag tags) ->
        List.exists (fun (_, tys) -> List.exists go tys) tags
  in
  go

let deep_copy =
  let rec go t =
    match !t with
    | Unbd _ -> failsolve "cannot deep copy unbound type"
    | Link t -> go t
    | Content (TTag tags) ->
        let tags = List.map (fun (s, pay) -> (s, List.map go pay)) tags in
        ref (Content (TTag tags))
  in
  go

let unify a b =
  let error prefix =
    failsolve
      ("Unify error: " ^ prefix ^ " at "
      ^ string_of_ty default_width a
      ^ " ~ "
      ^ string_of_ty default_width b)
  in
  let sort_tags tags =
    List.sort (fun (tag1, _) (tag2, _) -> compare tag1 tag2) tags
  in
  let rec unify_tags all = function
    | [], [] -> all
    | [], r :: rest -> unify_tags (r :: all) ([], rest)
    | l :: rest, [] -> unify_tags (l :: all) (rest, [])
    | l :: l_rest, r :: r_rest ->
        let (l_name, l_pay), (r_name, r_pay) = (l, r) in
        if l_name < r_name then unify_tags (l :: all) (l_rest, r :: r_rest)
        else if l_name > r_name then unify_tags (r :: all) (l :: l_rest, r_rest)
        else (
          (try List.iter2 unify l_pay r_pay
           with Invalid_argument _ -> error "tags have different sizes");
          unify_tags (l :: all) (l_rest, r_rest))
  and unify a b =
    let a, b = (unlink a, unlink b) in
    if a != b then
      match (!a, !b) with
      | Link _, _ | _, Link _ -> failwith "found a link where none was expected"
      | Unbd n, _ -> if occurs n b then error "occurs" else a := Link b
      | _, Unbd n -> if occurs n a then error "occurs" else b := Link a
      | Content l_content, Content r_content ->
          let unified_content =
            match (l_content, r_content) with
            | TTag l_tags, TTag r_tags ->
                let sorted_l_tags = sort_tags l_tags in
                let sorted_r_tags = sort_tags r_tags in
                let combined_tags =
                  List.rev @@ unify_tags [] (sorted_l_tags, sorted_r_tags)
                in
                TTag combined_tags
          in
          a := Content unified_content;
          b := Link a
  in
  unify a b

let infer =
  let rec infer_pat (_, t, p) : ty =
    let ty =
      match p with
      | PWild -> t
      | PTag ((_, name), atoms) ->
          let payload = List.map infer_pat atoms in
          ref @@ Content (TTag [ (name, payload) ])
    in
    unify t ty;
    ty
  in
  let infer_atoms atoms =
    Option.get
    @@ List.fold_left
         (fun total atom ->
           let t' = infer_pat atom in
           match total with
           | None -> Some t'
           | Some t ->
               unify t t';
               Some t)
         None atoms
  in
  let infer_top_pat (_, t, p) =
    let ty, adjust =
      match p with
      | PAtom atoms -> (infer_atoms atoms, [])
      | PAs (atoms, (_, t_as, x)) ->
          let atom_type = infer_atoms atoms in
          let raw_atom_type = deep_copy atom_type in
          unify t_as raw_atom_type;
          (atom_type, [ (x, t_as) ])
    in
    unify t ty;
    (ty, adjust)
  in
  let rec infer venv (_, t, e) : ty =
    let ty =
      match e with
      | Var x -> (
          match List.assoc_opt x venv with
          | Some t -> t
          | None -> failsolve ("Variable " ^ x ^ " not in scope"))
      | Tag (name, pay) ->
          let payload_types = List.map (infer venv) pay in
          ref @@ Content (TTag [ (name, payload_types) ])
      | Let ((_, t_x, x), e, b) ->
          let t_x' = infer venv e in
          unify t_x t_x';
          infer ((x, t_x) :: venv) b
      | When (cond, branches) ->
          let t_cond = infer venv cond in
          let t_body =
            List.fold_left
              (fun body_ty (pat, body) ->
                let pat_type, venv_adjust = infer_top_pat pat in
                let venv' = venv_adjust @ venv in
                let body_type = infer venv' body in
                unify t_cond pat_type;
                match body_ty with
                | None -> Some body_type
                | Some b' ->
                    unify b' body_type;
                    Some body_type)
              None branches
          in
          Option.get t_body
    in
    unify t ty;
    ty
  in
  infer

let infer_program program = infer [] program
