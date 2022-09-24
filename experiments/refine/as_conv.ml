(**
   Module [As_conv] refines `as`-cast values to their specified type.
   The conversion is the meat of this experiment, but actually follows a very
   simple procedure.

   In short, we want to take

   let x : [B, C, D, E] in
   when x is
     | B | C as y -> y
     | D | E -> A

   to

   let x : [B, C, D, E] in
   when x is
     | B | C ->
         let y : [A, B, C] = when x is
               | B -> B
               | C -> C
               | _ -> @proven_unreachable
         in y
     | D | E -> A

   and the rest will be compiled as it normally would.

   Idea: say we need to convert [A [T, U], B [T, U], C] to [A [T], B [T, U]].
   We only need to unpack and repack the constructors that differ between the two
   types.
   So we can build
   A T -> A T
   B x -> B x
   and we're done.

   Or, say we need to convert [A [T, U, V], B [T, U]] to [A [T, U]]. Now we just
   do
   A T -> A T
   A U -> A U
*)

open Syntax

let rec conv_help as_type o_type : (loc_pat_atom * e_expr) list =
  let as_tags, o_tags =
    match (!(unlink as_type), !(unlink o_type)) with
    | Content (TTag as_tags), Content (TTag o_tags) -> (as_tags, o_tags)
    | _ -> failwith "unreachable"
  in
  let convert_tag (as_tag, as_tag_types) =
    let o_tag_types = List.assoc as_tag o_tags in
    (* For each payload type, figure out how to convert it.
       I.e. if we are currently moving A [B, C] [D, E, F] to A [B] [D, E],
       we need to know all the branches to match on to move into the right-hand
       definition.

       First, we build the options for each payload type. So below we get
       [[B -> B]; [D -> D; E -> E]]
    *)
    let options_for_each_payload =
      List.map2 conv_help as_tag_types o_tag_types
    in
    (* Now, we need to build the argument table for this tag, so convert the
       above list into
       [B D -> B D; B E -> B E]
    *)
    let match_row_options =
      List.fold_left
        (fun building_rows payload_options ->
          (* add each option to each row in the pattern match *)
          let add_to_each_row (payload_pat, payload_expr) =
            List.map
              (fun (row_pats, row_exprs) ->
                (row_pats @ [ payload_pat ], row_exprs @ [ payload_expr ]))
              building_rows
          in
          List.concat_map add_to_each_row payload_options)
        (* initially start with one option, of no payloads *)
        [ ([], []) ]
        options_for_each_payload
    in
    let concretize_row (payload_pats, payload_exprs) =
      let pat : loc_pat_atom =
        (noloc, o_type, PTag ((noloc, as_tag), payload_pats))
      in
      let body : e_expr = (noloc, as_type, Tag (as_tag, payload_exprs)) in
      (pat, body)
    in
    List.map concretize_row match_row_options
  in
  (* Drop the tags in the "as" type that don't appear in the source type, since
     we'll never need to convert those in this branch *)
  List.filter (fun (tag, _) -> List.mem_assoc tag o_tags) as_tags
  (* Now convert the tags *)
  |> List.concat_map convert_tag

let conv ~as_var ~o_var rest =
  let as_ty, as_var = as_var in
  let o_ty, o_var = o_var in
  let concretize_branch (pat_atom, body) : branch =
    ((noloc, o_ty, PAtom [ pat_atom ]), body)
  in
  let branches = List.map concretize_branch @@ conv_help as_ty o_ty in
  let when_expr = When ((noloc, o_ty, Var o_var), branches) in
  let total_expr =
    Let ((noloc, as_ty, as_var), (noloc, as_ty, when_expr), rest)
  in
  (noloc, xty rest, total_expr)
