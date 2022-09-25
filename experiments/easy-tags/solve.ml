open Syntax

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
    | Content (TTag { tags; ext }) ->
        List.exists (fun (_, tys) -> List.exists go tys) tags || go ext
    | Content TTagEmpty -> false
  in
  go

let sort_tags tags =
  List.sort (fun (tag1, _) (tag2, _) -> compare tag1 tag2) tags

type separate_tags = {
  shared : (tag * tag) list;
  only1 : tag list;
  only2 : tag list;
}
[@@deriving show]

let separate_tags tags1 ext1 tags2 ext2 =
  let tags1, ext1 = chase_tags tags1 ext1 in
  let tags2, ext2 = chase_tags tags2 ext2 in
  let tags1, tags2 = (sort_tags tags1, sort_tags tags2) in
  let rec walk shared only1 only2 = function
    | [], [] -> { shared; only1 = List.rev only1; only2 = List.rev only2 }
    | o :: rest, [] -> walk shared (o :: only1) only2 (rest, [])
    | [], o :: rest -> walk shared only1 (o :: only2) ([], rest)
    | t1 :: rest1, t2 :: rest2 ->
        if fst t1 < fst t2 then
          walk shared (t1 :: only1) only2 (rest1, t2 :: rest2)
        else if fst t2 < fst t1 then
          walk shared only1 (t2 :: only2) (t1 :: rest1, rest2)
        else walk ((t1, t2) :: shared) only1 only2 (rest1, rest2)
  in
  let result = walk [] [] [] (tags1, tags2) in
  (result, ext1, ext2)

let unify fresh a b =
  let error prefix =
    failsolve
      ("Unify error: " ^ prefix ^ " at " ^ string_of_ty a ^ " ~ "
     ^ string_of_ty b)
  in
  let merge a b content =
    a := Content content;
    b := Link a
  in
  let rec unify a b =
    let a, b = (unlink a, unlink b) in
    if a != b then
      match (!a, !b) with
      | Link _, _ | _, Link _ -> failwith "found a link where none was expected"
      | Unbd n, _ -> if occurs n b then error "occurs" else a := Link b
      | _, Unbd n -> if occurs n a then error "occurs" else b := Link a
      | Content l_content, Content r_content -> (
          match (l_content, r_content) with
          | ( TTag { tags = l_tags; ext = l_ext },
              TTag { tags = r_tags; ext = r_ext } ) -> (
              let { shared; only1 = only_l; only2 = only_r }, l_ext, r_ext =
                separate_tags l_tags l_ext r_tags r_ext
              in
              List.iter
                (fun ((t1, args1), (t2, args2)) ->
                  assert (t1 = t2);
                  if List.length args1 != List.length args2 then
                    error "tags differ in size";
                  List.iter2 unify args1 args2)
                shared;

              let sorted_shared_tags = sort_tags @@ List.map fst shared in

              match ((only_l, l_ext), (only_r, r_ext)) with
              | ([], ext), ([], _) ->
                  merge a b (TTag { tags = sorted_shared_tags; ext })
              | (others, ext), ([], o_ext) | ([], o_ext), (others, ext) ->
                  unify o_ext (ref (Content (TTag { tags = others; ext })));
                  let tags = sort_tags @@ sorted_shared_tags @ others in
                  merge a b (TTag { tags; ext })
              | (others1, ext1), (others2, ext2) ->
                  let new_ext = fresh () in
                  let sub_1 =
                    ref (Content (TTag { tags = others1; ext = new_ext }))
                  in
                  let sub_2 =
                    ref (Content (TTag { tags = others2; ext = new_ext }))
                  in
                  unify ext1 sub_2;
                  unify ext2 sub_1;

                  let all_tags =
                    sort_tags @@ sorted_shared_tags @ others1 @ others2
                  in
                  merge a b (TTag { tags = all_tags; ext = new_ext }))
          | TTagEmpty, TTagEmpty -> ()
          | TTagEmpty, TTag { tags; ext } ->
              if tags = [] then unify a ext else error "tags not empty"
          | TTag { tags; ext }, TTagEmpty ->
              if tags = [] then unify ext b else error "tags not empty")
  in
  unify a b

let close_type =
  let rec go t =
    match !t with
    | Unbd _ -> ()
    | Link t -> go t
    | Content TTagEmpty -> ()
    | Content (TTag { tags; ext }) ->
        let tags, ext = chase_tags tags ext in
        ext := Content TTagEmpty;
        List.iter (fun (_, args) -> List.iter go args) tags
  in
  go

let open_type fresh_var =
  let rec go t =
    match !t with
    | Unbd _ -> ()
    | Link t -> go t
    | Content TTagEmpty -> t := !(fresh_var ())
    | Content (TTag { tags; ext }) ->
        let _, ext = chase_tags tags ext in
        ext := !(fresh_var ())
  in
  go

type adjust = Bind of string * ty | Open of ty

let infer fresh_var =
  let unify = unify fresh_var in
  let rec infer_pat (_, t, p) : ty * adjust list =
    let ty, adjust =
      match p with
      | PWild -> (t, [ Open t ])
      | PVar x -> (t, [ Bind (x, t); Open t ])
      | PTag ((_, name), atoms) ->
          let payload, adjusts = List.split @@ List.map infer_pat atoms in
          let ty =
            ref
            @@ Content (TTag { tags = [ (name, payload) ]; ext = fresh_var () })
          in
          (ty, List.concat adjusts)
    in
    unify t ty;
    (ty, adjust)
  in
  let infer_atoms atoms =
    Option.get
    @@ List.fold_left
         (fun total atom ->
           let t', adjusts' = infer_pat atom in
           match total with
           | None -> Some (t', adjusts')
           | Some (t, adjusts) ->
               unify t t';
               Some (t, adjusts @ adjusts'))
         None atoms
  in
  let infer_top_pat (_, t, ps) =
    let ty, adjusts = infer_atoms ps in
    unify t ty;
    (ty, adjusts)
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
          ref
          @@ Content
               (TTag { tags = [ (name, payload_types) ]; ext = fresh_var () })
      | Let ((_, t_x, x), e, b) ->
          let t_x' = infer venv e in
          unify t_x t_x';
          infer ((x, t_x) :: venv) b
      | When (cond, branches) ->
          let t_cond = infer venv cond in
          let solved_types, open_adjusts =
            List.fold_left
              (fun (opt_tys, open_adjusts) (pat, body) ->
                let pat_type, adjusts = infer_top_pat pat in
                let var_adjusts =
                  List.filter_map
                    (function Bind (x, t) -> Some (x, t) | _ -> None)
                    adjusts
                in
                let open_adjusts' =
                  List.filter_map
                    (function Open t -> Some t | _ -> None)
                    adjusts
                in
                let venv' = var_adjusts @ venv in
                let body_type = infer venv' body in
                unify t_cond pat_type;
                let opt_tys =
                  match opt_tys with
                  | None -> Some (pat_type, body_type)
                  | Some (branches, bodies) ->
                      unify bodies body_type;
                      unify branches pat_type;
                      Some (branches, bodies)
                in
                (opt_tys, open_adjusts' @ open_adjusts))
              (None, []) branches
          in
          let t_branches, t_body = Option.get solved_types in
          close_type t_branches;
          List.iter (open_type fresh_var) open_adjusts;
          unify t_branches t_cond;
          t_body
    in
    unify t ty;
    ty
  in
  infer

let infer_program fresh_var program = infer fresh_var [] program
