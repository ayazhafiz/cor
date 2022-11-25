%{
open Syntax

let range (start, _) (_, fin) = (start, fin)

let l_range x l = range (x (List.hd l)) (x (List.hd (List.rev l)))

let fresh_var ctx = ref (Unbd (ctx.fresh_var ()))

let xloc = Syntax.xloc
let xty = Syntax.xty
let xv = Syntax.xv
%}


%token <Syntax.loc * string> LOWER
%token <Syntax.loc * string> UPPER

%token <Syntax.loc> LET
%token <Syntax.loc> IN
%token <Syntax.loc> MATCH
%token <Syntax.loc> WITH
%token <Syntax.loc> COMMA
%token <Syntax.loc> AS
%token <Syntax.loc> LPAREN
%token <Syntax.loc> RPAREN
%token <Syntax.loc> LBRACKET
%token <Syntax.loc> RBRACKET
%token <Syntax.loc> PIPE
%token <Syntax.loc> EQ
%token <Syntax.loc> COLON
%token <Syntax.loc> ARROW
%token <Syntax.loc> WILD
%token EOF

%start toplevel
%type <Syntax.parse_ctx -> Syntax.program> toplevel
%type <Syntax.parse_ctx -> Syntax.e_expr> expr
%type <Syntax.parse_ctx -> Syntax.e_expr list> expr_atom_list
%type <Syntax.parse_ctx -> Syntax.loc_pat_atom> pat
%type <Syntax.parse_ctx -> Syntax.branch list> branch_seq
%%

toplevel:
  | e=expr EOF { fun ctx -> e ctx }

expr:
  | app=expr_app { app }
  | e=expr_lets { fun c -> e c }
  | w=MATCH cond=expr WITH rev_branches=branch_seq { fun ctx ->
      let cond = cond ctx in
      let branches = List.rev @@ rev_branches ctx in
      let loc: Syntax.loc = range w (l_range (fun (_, e) -> xloc e) branches) in
      (loc, fresh_var ctx, Match(cond, branches))
  }

expr_app:
  | e=expr_atom { e }
  | head=UPPER atom_list=expr_atom_list { fun ctx ->
      let atom_list = atom_list ctx in
      let loc = range (fst head) (l_range xloc atom_list) in
      (loc, fresh_var ctx, Tag(snd head, atom_list))
  }

expr_atom_list:
  | e=expr_atom { fun ctx -> [e ctx] }
  | e=expr_atom rest=expr_atom_list { fun ctx -> (e ctx)::(rest ctx) }

expr_lets:
  | l=LET loc_x=LOWER EQ e=expr IN body=expr { fun c ->
      let body = body c in
      let loc = range l (xloc body) in
      let x = (fst loc_x, fresh_var c, snd loc_x) in
      (loc, fresh_var c, Let(x, e c, body))
  }
  | l=LET loc_x=LOWER COLON t=ty EQ e=expr IN body=expr { fun c ->
      let body = body c in
      let ty = t c in
      let loc = range l (xloc body) in
      let x = (fst loc_x, ty, snd loc_x) in
      (loc, fresh_var c, Let(x, e c, body))
  }

branch_seq:
  | PIPE pats=branch_pats body=expr { fun ctx -> [(pats ctx, body ctx)] }
  | rest=branch_seq PIPE pats=branch_pats body=expr { fun ctx -> (pats ctx, body ctx)::(rest ctx) }

branch_pats:
  | atoms=pat_list AS v=LOWER ARROW { fun ctx ->
      let atoms = atoms ctx in
      let loc = range (xloc (List.hd atoms)) (fst v) in
      (loc, fresh_var ctx, PAs(atoms, (fst v, fresh_var ctx, snd v)))
  }
  | atoms=pat_list ARROW { fun ctx ->
      let atoms = atoms ctx in
      let loc = l_range xloc atoms in
      (loc, fresh_var ctx, PAtom atoms)
  }

expr_atom:
  | x=LOWER { fun ctx -> (fst x, fresh_var ctx, Var (snd x)) }
  | l=LPAREN e=expr r=RPAREN { fun ctx -> 
      let e = e ctx in
      (range l r, xty e, xv e)
  }
  | head=UPPER { fun ctx -> (fst head, fresh_var ctx, Tag(snd head, [])) }

pat_list:
  | p=pat PIPE rest=pat_list { fun ctx ->
      (p ctx)::(rest ctx)
  }
  | p=pat { fun ctx -> [p ctx] }

pat:
  | p=pat_atom { fun ctx -> p ctx }
  | hd=UPPER args=pat_apply { fun ctx ->
      let args = args ctx in
      let loc = range (fst hd) (xloc (List.hd (List.rev args))) in
      (loc, fresh_var ctx, PTag(hd, args))
  }

pat_apply:
  | p=pat_atom rest=pat_apply { fun ctx -> (p ctx)::(rest ctx) }
  | p=pat_atom { fun ctx -> [p ctx] }

pat_atom:
  | w=WILD { fun ctx -> (w, fresh_var ctx, PWild) }
  | l=LPAREN p=pat r=RPAREN { fun ctx ->
      let p = p ctx in
      (range l r, xty p, xv p)
  }
  | hd=UPPER { fun ctx -> (fst hd, fresh_var ctx, PTag(hd, [])) }

ty:
  | LBRACKET tags=ty_tags RBRACKET { fun ctx ->
      let tags = tags ctx in
      ref @@ Content (TTag tags)
  }

ty_tags:
  | t=ty_tag { fun ctx -> [t ctx] }
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
