open Syntax

exception Eval_error of string

let error s = raise (Eval_error s)

let eval_e ctx =
  let rec eval venv (_, _, e) =
    match e with
    | Val v -> [ Val v ]
    | Var x -> [ xv @@ List.assoc x venv ]
    | Let ((_, x), e, b) -> eval ((x, e) :: venv) b
    | Call (f, a) ->
        let f' = eval venv f in
        let a' = eval venv a in
        List.concat_map
          (function
            | Clos ((_, _, pat), _, body) ->
                let handle_arg =
                  match pat with
                  | PVal v -> (
                      function
                      | Val u when v = u -> eval venv body
                      | _ -> error "bad application")
                  | PVar x ->
                      fun a ->
                        (* naive: does a name-capturing substitution which is ofc incorrect *)
                        let subst = (x, (noloc, TVal "?", a)) in
                        eval (subst :: venv) body
                in
                List.flatten @@ List.map handle_arg a'
            | _ -> error "application to non-function")
          f'
    | Clos (arg, lam, body) -> [ Clos (arg, lam, body) ]
    | Choice splits -> List.flatten @@ List.map (eval venv) splits
  in
  eval ctx

let eval ctx entry_points =
  List.map
    (fun entry ->
      let e = List.assoc entry ctx in
      let e' = eval_e ctx e in
      (entry, e'))
    entry_points
