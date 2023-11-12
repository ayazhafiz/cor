%{
open Syntax

let range: loc -> loc -> loc = fun (start, _) (_, fin) -> (start, fin)

let l_range x l = range (x (List.hd l)) (x (List.hd (List.rev l)))

let xloc = Syntax.xloc
let xty = Syntax.xty
let xv = Syntax.xv
%}


%token <Syntax.loc * string> LOWER
%token <Syntax.loc * string> UPPER

%token <Syntax.loc> LET
%token <Syntax.loc> SIG
%token <Syntax.loc> RUN
%token <Syntax.loc> IN
%token <Syntax.loc> COMMA
%token <Syntax.loc> LPAREN
%token <Syntax.loc> RPAREN
%token <Syntax.loc> LBRACKET
%token <Syntax.loc> RBRACKET
%token <Syntax.loc> EQ
%token <Syntax.loc> COLON
%token <Syntax.loc> SEMI
%token <Syntax.loc> ARROW
%token <Syntax.loc> WILD
%token <Syntax.loc> STAR
%token <Syntax.loc> LAMBDA
%token EOF

%start toplevel
%type <Syntax.parse_ctx -> Syntax.program> toplevel
%type <Syntax.parse_ctx -> Syntax.e_def> def
%type <Syntax.parse_ctx -> Syntax.e_expr> expr
%type <Syntax.parse_ctx -> Syntax.e_expr list> expr_atom_list
%type <Syntax.parse_ctx -> Syntax.loc_ty> ty
%type <Syntax.parse_ctx -> Syntax.loc_ty> ty_atom
%%

toplevel:
  | EOF { fun _ -> [] }
  | d=def rest=toplevel { fun ctx -> (d ctx)::(rest ctx) }

def:
  | loc_t=UPPER vars=alias_vars COLON ty=ty { fun ctx ->
      let vars = vars ctx in
      let ty = ty ctx in
      let loc = range (fst loc_t) (fst ty) in
      (loc, ctx.fresh_var (), TyAlias(loc_t, vars, ty))
  }
  | l=LET loc_x=LOWER EQ e=expr SEMI s=SEMI { fun ctx ->
      let e = e ctx in
      let loc = range l s in
      (loc, ctx.fresh_var (), Def(loc_x, e))
  }
  | s=SIG loc_x=LOWER COLON t=ty { fun ctx ->
      let t = t ctx in
      let loc = range s (fst t) in
      (loc, ctx.fresh_var (), Sig(loc_x, t))
  }
  | r=RUN loc_x=LOWER EQ e=expr SEMI s=SEMI { fun ctx ->
      let e = e ctx in
      let loc = range r s in
      (loc, ctx.fresh_var (), Run(loc_x, e))
  }

alias_vars:
  | vars=alias_vars var=LOWER { fun ctx -> (vars ctx)@[var] }
  | var=LOWER { fun _ -> [var] }

expr:
  | app=expr_app { app }
  | e=expr_lets { fun c -> e c }
  | lam=LAMBDA arg=LOWER ARROW body=expr { fun ctx ->
      let body = body ctx in
      let loc = range lam (xloc body) in
      let arg = (fst arg, (noloc, ctx.fresh_var ()), snd arg) in
      (loc, ctx.fresh_var (), Clos(arg, body))
  }

expr_app:
  | e=expr_atom { e }
  | head=UPPER atom_list=expr_atom_list { fun ctx ->
      let atom_list = atom_list ctx in
      let loc = range (fst head) (l_range xloc atom_list) in
      (loc, ctx.fresh_var (), Tag(snd head, atom_list))
  }
  | head=LOWER atom_list=expr_atom_list { fun ctx ->
      let head = (fst head, ctx.fresh_var (), Var (snd head)) in
      let atom_list = atom_list ctx in
      List.fold_left (fun whole e ->
        let loc = (range (xloc whole) (xloc e)) in
        (loc, ctx.fresh_var (), Call(whole, e))
      ) head atom_list
  }

expr_atom_list:
  | e=expr_atom { fun ctx -> [e ctx] }
  | e=expr_atom rest=expr_atom_list { fun ctx -> (e ctx)::(rest ctx) }

expr_lets:
  | l=LET loc_x=LOWER EQ e=expr IN body=expr { fun c ->
      let body = body c in
      let loc = range l (xloc body) in
      let x = (fst loc_x, (noloc, c.fresh_var ()), snd loc_x) in
      (loc, c.fresh_var (), Let(x, e c, body))
  }
  | l=LET loc_x=LOWER COLON t=ty EQ e=expr IN body=expr { fun c ->
      let body = body c in
      let ty = t c in
      let loc = range l (xloc body) in
      let x = (fst loc_x, ty, snd loc_x) in
      (loc, c.fresh_var (), Let(x, e c, body))
  }

expr_atom:
  | x=LOWER { fun ctx -> (fst x, ctx.fresh_var (), Var (snd x)) }
  | l=LPAREN e=expr r=RPAREN { fun ctx -> 
      let e = e ctx in
      (range l r, xty e, xv e)
  }
  | head=UPPER { fun ctx -> (fst head, ctx.fresh_var (), Tag(snd head, [])) }

ty:
  | arrow=ty_arrow { fun ctx -> arrow ctx }

ty_arrow:
  | e=ty_app { fun ctx -> e ctx }
  | head=ty_app ARROW e=ty_arrow { fun ctx ->
      let head = head ctx in
      let e = e ctx in
      let t = ref @@ Content (TFn(head, e)) in
      let l = range (fst head) (fst e) in
      (l, t)
  }

ty_app:
  | t=ty_atom { fun ctx -> t ctx }
  | h=UPPER vars=ty_alias_app { fun ctx -> 
      let vars = vars ctx in
      let t = ref @@ Alias {
        alias = (h, vars);
        real = ctx.fresh_var ();
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
  | w=WILD { fun ctx -> (w, ctx.fresh_var ()) }
  | lb=LBRACKET tags=ty_tags RBRACKET ext=ty_atom { fun ctx ->
      let tags = tags ctx in
      let ext: loc_ty = ext ctx in
      let t = ref @@ Content (TTag {tags; ext}) in
      let l = range lb (fst ext) in
      (l, t)
  }
  | lb=LBRACKET tags=ty_tags rb=RBRACKET { fun ctx ->
      let tags = tags ctx in
      let ext = (noloc, ref @@ Content TTagEmpty) in
      let t = ref @@ Content (TTag {tags; ext}) in
      let l = range lb rb in
      (l, t)
  }
  | u=LOWER { fun ctx ->
      (fst u, ctx.fresh_fora @@ Some (snd u))
  }
  | s=STAR { fun ctx ->
      (s, ctx.fresh_fora @@ None)
  }
  | h=UPPER { fun ctx -> 
      let t = ref @@ Alias {
        alias = (h, []);
        real = ctx.fresh_var ();
      } in
      let l = fst h in
      (l, t)
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
