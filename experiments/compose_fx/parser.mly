%{
open Loc
open Syntax

let range: loc -> loc -> loc = fun (start, _) (_, fin) -> (start, fin)

let l_range x l = range (x (List.hd l)) (x (List.hd (List.rev l)))

let add_scoped_def_sym ctx (l, n) =
  let sym = ctx.symbols.fresh_symbol_named n in
  Symbol.enter_scope ctx.symbols n sym;
  (l, sym)

let lookup_sym ctx (l, n) =
  let sym = Symbol.scoped_name ctx.symbols n in
  (l, sym)

let exit_scope ctx sym =
  Symbol.exit_scope ctx.symbols @@ Symbol.syn_of ctx.symbols sym

let xloc = Syntax.xloc
let xty = Syntax.xty
let xv = Syntax.xv
%}


%token <Loc.loc * string> LOWER
%token <Loc.loc * string> UPPER
%token <Loc.loc * int> NUMBER
%token <Loc.loc * string> STRING
%token <Loc.loc * string> KERNELFN

%token <Loc.loc> LET
%token <Loc.loc> SIG
%token <Loc.loc> RUN
%token <Loc.loc> WHEN
%token <Loc.loc> IS
%token <Loc.loc> END
%token <Loc.loc> STR
%token <Loc.loc> INT
%token <Loc.loc> UNIT
%token <Loc.loc> IN
%token <Loc.loc> COMMA
%token <Loc.loc> LPAREN
%token <Loc.loc> RPAREN
%token <Loc.loc> LBRACKET
%token <Loc.loc> RBRACKET
%token <Loc.loc> EQ
%token <Loc.loc> COLON
%token <Loc.loc> SEMI
%token <Loc.loc> ARROW
%token <Loc.loc> STAR
%token <Loc.loc> PIPE
%token <Loc.loc> LAMBDA
%token EOF

%start toplevel
%type <Syntax.parse_ctx -> Syntax.program> toplevel
%type <Syntax.parse_ctx -> Syntax.e_def list> def
%type <Syntax.parse_ctx -> Syntax.e_expr> expr
%type <Syntax.parse_ctx -> Syntax.e_expr list> expr_atom_list
%type <Syntax.parse_ctx -> Type.loc_tvar> ty
%type <Syntax.parse_ctx -> Type.loc_tvar> ty_atom
%%

toplevel:
  | EOF { fun _ -> [] }
  | d=def rest=toplevel { fun ctx ->
      let d = d ctx in
      d @ (rest ctx)
  }

def:
  | loc_t=UPPER vars=alias_vars COLON ty=ty { fun ctx ->
      let vars = vars ctx in
      let loc_sym_t = add_scoped_def_sym ctx loc_t in
      let ty = ty ctx in
      let loc = range (fst loc_t) (fst ty) in
      [ (loc, ctx.fresh_tvar @@ Unbd None, TyAlias(loc_sym_t, vars, ty)) ]
  }
  | sig_=sig_ lr=let_or_run { fun ctx ->
      let (s, (loc_x, name_x), t) = sig_ in
      let (kind, l, (loc_y, name_y), e, loc_semi) = lr in
      let t = t ctx in
      let loc_sig = range s (fst t) in
      let loc_sym_x = add_scoped_def_sym ctx (loc_x, name_x) in
      let e_sig = (loc_sig, ctx.fresh_tvar @@ Unbd None, Sig(loc_sym_x, t)) in

      let loc_sym_y = if name_x = name_y then (loc_y, snd loc_sym_x) else add_scoped_def_sym ctx (loc_y, name_y) in
      let e = e ctx in
      let loc_lr = range l loc_semi in
      let def = match kind with
        | `Let -> Def(loc_sym_y, e)
        | `Run -> Run(loc_sym_y, e)
      in
      [ e_sig; (loc_lr, ctx.fresh_tvar @@ Unbd None, def) ]
  }
  | sig_=sig_ { fun ctx ->
      let (s, loc_x, t) = sig_ in
      let t = t ctx in
      let loc = range s (fst t) in
      let loc_sym_x = add_scoped_def_sym ctx loc_x in
      [ (loc, ctx.fresh_tvar @@ Unbd None, Sig(loc_sym_x, t)) ]
  }
  | lr=let_or_run { fun ctx ->
      let (kind, l, x, e, loc_semi) = lr in
      let e = e ctx in
      let loc = range l loc_semi in
      let loc_sym_x = add_scoped_def_sym ctx x in
      let def = match kind with
        | `Let -> Def(loc_sym_x, e)
        | `Run -> Run(loc_sym_x, e)
      in
      [ (loc, ctx.fresh_tvar @@ Unbd None, def) ]
  }

sig_:
  s=SIG loc_x=LOWER COLON t=ty {
    (s, loc_x, t)
  }

let_or_run:
  | l=LET loc_x=LOWER EQ e=expr SEMI s=SEMI {
      (`Let, l, loc_x, e, s)
  }
  | r=RUN loc_x=LOWER EQ e=expr SEMI s=SEMI {
      (`Run, r, loc_x, e, s)
  }

alias_vars:
  | vars=alias_vars var=LOWER { fun ctx -> (vars ctx)@[(fst var, ctx.fresh_tvar @@ ForA(Some (snd var)))] }
  | var=LOWER { fun ctx -> [(fst var, ctx.fresh_tvar @@ ForA(Some (snd var)))] }

expr:
  | app=expr_app { app }
  | e=expr_lets { fun c -> e c }
  | lam=LAMBDA arg=LOWER ARROW body=expr { fun ctx ->
      let (loc_arg, sym_arg) = add_scoped_def_sym ctx arg in
      let body = body ctx in
      exit_scope ctx sym_arg;
      let loc = range lam (xloc body) in
      let arg = (loc_arg, (noloc, ctx.fresh_tvar @@ Unbd None), sym_arg) in
      (loc, ctx.fresh_tvar @@ Unbd None, Clos{arg; body})
  }
  | w=WHEN e=expr IS branches=branch_seq { fun ctx ->
      let e = e ctx in
      let branches, loc_end = branches ctx in
      let loc = range w loc_end in
      (loc, ctx.fresh_tvar @@ Unbd None, When(e, branches))
  }

expr_app:
  | e=expr_atom { e }
  | head=UPPER atom_list=expr_atom_list { fun ctx ->
      let atom_list = atom_list ctx in
      let loc = range (fst head) (l_range xloc atom_list) in
      (loc, ctx.fresh_tvar @@ Unbd None, Tag(snd head, atom_list))
  }
  | head=LOWER atom_list=expr_atom_list { fun ctx ->
      let (loc_head, sym_head) = lookup_sym ctx head in
      let head = (loc_head, ctx.fresh_tvar @@ Unbd None, Var sym_head) in
      let atom_list = atom_list ctx in
      List.fold_left (fun whole e ->
        let loc = (range (xloc whole) (xloc e)) in
        (loc, ctx.fresh_tvar @@ Unbd None, Call(whole, e))
      ) head atom_list
  }
  | head=KERNELFN atom_list=expr_atom_list { fun ctx ->
      let atom_list = atom_list ctx in
      let kernelfn = List.assoc (snd head) Syntax.kernelfn_of_string in
      let loc = range (fst head) (l_range xloc atom_list) in
      (loc, ctx.fresh_tvar @@ Unbd None, KCall(kernelfn, atom_list))
  }

expr_atom_list:
  | e=expr_atom { fun ctx -> [e ctx] }
  | e=expr_atom rest=expr_atom_list { fun ctx -> (e ctx)::(rest ctx) }

expr_lets:
  | l=LET loc_x=LOWER EQ e=expr IN body=expr { fun c ->
      let (loc_x, sym_x) = add_scoped_def_sym c loc_x in
      let e = e c in
      let body = body c in
      exit_scope c sym_x;
      let loc = range l (xloc body) in
      let x = (loc_x, (noloc, c.fresh_tvar @@ Unbd None), sym_x) in
      (loc, c.fresh_tvar @@ Unbd None, Let{recursive=ref false; bind=x; expr=e; body})
  }
  | l=LET loc_x=LOWER COLON t=ty EQ e=expr IN body=expr { fun c ->
      let (loc_x, sym_x) = add_scoped_def_sym c loc_x in
      let e = e c in
      let ty = t c in
      let body = body c in
      exit_scope c sym_x;
      let loc = range l (xloc body) in
      let x = (loc_x, ty, sym_x) in
      (loc, c.fresh_tvar @@ Unbd None, Let{recursive=ref false; bind=x; expr=e; body})
  }

expr_atom:
  | x=LOWER { fun ctx ->
      let (loc_x, sym_x) = lookup_sym ctx x in
      (loc_x, ctx.fresh_tvar @@ Unbd None, Var sym_x)
  }
  | l=LPAREN e=expr r=RPAREN { fun ctx -> 
      let e = e ctx in
      (range l r, xty e, xv e)
  }
  | head=UPPER { fun ctx -> (fst head, ctx.fresh_tvar @@ Unbd None, Tag(snd head, [])) }
  | s=STRING { fun ctx ->
      let loc = fst s in
      let sym = ctx.fresh_tvar @@ Unbd None in
      (loc, sym, Str (snd s))
  }
  | n=NUMBER { fun ctx ->
      let loc = fst n in
      let sym = ctx.fresh_tvar @@ Unbd None in
      (loc, sym, Int (snd n))
  }
  | loc=UNIT { fun ctx ->
      let tvar = ctx.fresh_tvar @@ Unbd None in
      (loc, tvar, Unit)
  }

branch_seq:
  | e=END { fun _ -> ([], e) }
  | PIPE pat=pat ARROW body=expr rest=branch_seq { fun ctx ->
      let pat, syms = pat ctx in
      let body = body ctx in
      List.iter (exit_scope ctx) syms;
      let rest, e = rest ctx in
      ((pat, body)::rest, e)
  }

pat:
  | p=pat_atom { fun ctx -> p ctx }
  | hd=UPPER args=pat_apply { fun ctx ->
      let args, syms = args ctx in
      let loc = range (fst hd) (xloc (List.hd (List.rev args))) in
      (loc, ctx.fresh_tvar @@ Unbd None, PTag(hd, args)), syms
  }

pat_apply:
  | p=pat_atom rest=pat_apply { fun ctx ->
      let pa, pa_syms = p ctx in
      let rest, rest_syms = rest ctx in
      (pa::rest, pa_syms@rest_syms)
  }
  | p=pat_atom { fun ctx ->
      let pa, pa_syms = p ctx in
      ([pa], pa_syms)
  }

pat_atom:
  | x=LOWER { fun ctx ->
      let (loc_x, sym_x) = add_scoped_def_sym ctx x in
      (loc_x, ctx.fresh_tvar @@ Unbd None, PVar (loc_x, sym_x)), [sym_x]
  }
  | l=LPAREN p=pat r=RPAREN { fun ctx ->
      let p, syms = p ctx in
      (range l r, xty p, xv p), syms
  }
  | hd=UPPER { fun ctx -> (fst hd, ctx.fresh_tvar @@ Unbd None, PTag(hd, [])), [] }

ty:
  | arrow=ty_arrow { fun ctx -> arrow ctx }

ty_arrow:
  | e=ty_app { fun ctx -> e ctx }
  | head=ty_app ARROW e=ty_arrow { fun ctx ->
      let head = head ctx in
      let e = e ctx in
      let t = ctx.fresh_tvar @@ Content (TFn(head, e)) in
      let l = range (fst head) (fst e) in
      (l, t)
  }

ty_app:
  | t=ty_atom { fun ctx -> t ctx }
  | h=UPPER vars=ty_alias_app { fun ctx -> 
      let vars = vars ctx in
      let t = ctx.fresh_tvar @@ Alias {
        alias = (lookup_sym ctx h, vars);
        real = ctx.fresh_tvar @@ Unbd None;
      } in
      let last_var = List.nth_opt (List.rev vars) 0 in
      let last_var_loc = Option.map fst last_var in
      let last_loc = Option.value last_var_loc ~default:(fst h) in
      let l = range (fst h) last_loc in
      (l, t)
  }

ty_alias_app:
  | vars=ty_alias_app var=ty_atom { fun ctx -> (vars ctx)@[var ctx] }
  | var=ty_atom { fun ctx -> [var ctx] }

ty_atom:
  | LPAREN t=ty RPAREN { fun ctx -> t ctx }
  | lb=LBRACKET tags=ty_tags RBRACKET ext=ty_atom { fun ctx ->
      let tags = tags ctx in
      let ext: Type.loc_tvar = ext ctx in
      let t = ctx.fresh_tvar @@ Content (TTag {tags; ext}) in
      let l = range lb (fst ext) in
      (l, t)
  }
  | lb=LBRACKET tags=ty_tags rb=RBRACKET { fun ctx ->
      let tags = tags ctx in
      let ext = (noloc, ctx.fresh_tvar @@ Content TTagEmpty) in
      let t = ctx.fresh_tvar @@ Content (TTag {tags; ext}) in
      let l = range lb rb in
      (l, t)
  }
  | u=LOWER { fun ctx ->
      (fst u, ctx.fresh_tvar @@ ForA (Some (snd u)))
  }
  | s=STAR { fun ctx ->
      (s, ctx.fresh_tvar @@ ForA None)
  }
  | s=STR { fun ctx ->
      (s, ctx.fresh_tvar @@ Content (TPrim `Str))
  }
  | s=INT { fun ctx ->
      (s, ctx.fresh_tvar @@ Content (TPrim `Int))
  }
  | s=UNIT { fun ctx ->
      (s, ctx.fresh_tvar @@ Content (TPrim `Unit))
  }

ty_tags:
  | t=ty_tag { fun ctx -> [t ctx] }
  | t=ty_tag COMMA { fun ctx -> [t ctx] }
  | t=ty_tag COMMA rest=ty_tags { fun ctx -> (t ctx)::(rest ctx) }

ty_tag:
  | t=UPPER payloads=ty_list { fun ctx ->
      let payloads = payloads ctx in
      (snd t, payloads)
  }
  | t=UPPER { fun _ -> (snd t, []) }

ty_list:
  | t=ty { fun ctx -> [t ctx] }
  | t=ty rest=ty_list { fun ctx -> (t ctx)::(rest ctx) }
