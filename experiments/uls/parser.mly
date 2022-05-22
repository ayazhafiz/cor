%{
open Syntax

let range (start, _) (_, fin) = (start, fin)

type proto_ctx = {
  name: string;
  uty: (string * ty);
  fresh_region: unit -> int;
}
%}


%token <Syntax.loc * string> LOWER
%token <Syntax.loc * string> UPPER

%token <Syntax.loc> LET
%token <Syntax.loc> IN
%token <Syntax.loc> LAM
%token <Syntax.loc> UNIT
%token <Syntax.loc> LPAREN
%token <Syntax.loc> RPAREN
%token <Syntax.loc> EQ
%token <Syntax.loc> COLON
%token <Syntax.loc> ARROW
%token <Syntax.loc> CHOICE
%token <Syntax.loc> PROTO
%token EOF

%start toplevel
%type <Syntax.parse_ctx -> Syntax.program> toplevel
%type <Syntax.parse_ctx -> Syntax.loc_expr> expr
%%

toplevel:
  | EOF { fun _ -> [] }
  | d=decl rest=toplevel { fun ctx -> (d ctx)::(rest ctx) }

decl:
  | PROTO name=LOWER arg=LOWER COLON ty=ty { fun ctx ->
      let arg = snd arg in
      let aty = ctx.fresh_var () in
      let uty = (arg, UVar aty) in
      let fresh_region = let n = ref 0 in fun () -> incr n; !n in
      let ty = ty { name=snd name; uty; fresh_region } in
      Proto(name, (aty, arg), ty)
  }
  | LET name=LOWER EQ e=expr { fun ctx ->
      Def(name, e ctx)
  }

expr:
  | app=expr_app { app }
  | e=expr_lets { fun c -> e c }
  | lam=LAM arg=pat ARROW body=expr { fun c ->
      let body = body c in
      let loc = range lam (fst body) in
      (loc, Clos(arg, Lam (c.fresh_clos_name ()), body))
  }
  | c=CHOICE rev_branches=branches { fun ctx ->
      let rev_branches = rev_branches ctx in
      let loc = range c (fst @@ fst @@ List.hd rev_branches) in
      (loc, Choice(List.rev rev_branches))
  }

expr_app:
  | e=expr_atom { e }
  | head=expr_app e=expr_atom { fun c ->
      let head = head c in
      let e = e c in
      (range (fst head) (fst e), Call(head, e))
  }

expr_lets:
  | l=LET loc_x=LOWER EQ e=expr IN body=expr { fun c ->
      let body = body c in
      let loc = range l (fst body) in
      (loc, Let(loc_x, e c, body))
  }

branches:
  | pat=pat ARROW body=expr { fun ctx -> [(pat, body ctx)] }
  | rest=branches pat=pat ARROW body=expr { fun ctx -> (pat, body ctx)::(rest ctx) }

expr_atom:
  | x=LOWER { fun _ -> (fst x, Var (snd x)) }
  | v=UPPER { fun _ -> (fst v, Val (snd v)) }
  | v=UNIT  { fun _ -> (v, Val "Unit") }
  | l=LPAREN e=expr r=RPAREN { fun ctx -> (range l r, snd (e ctx)) }

pat:
  | x=LOWER { (fst x, PVar (snd x)) }
  | u=UNIT { (u, PVal("Unit")) }
  | hd=UPPER { (fst hd, PVal(snd hd)) }

ty:
  | arrow=ty_arrow { fun ctx -> arrow ctx }

ty_arrow:
  | e=ty_atom { fun ctx -> e ctx }
  | head=ty_atom ARROW e=ty_arrow { fun ctx ->
      let head = head ctx in
      let e = e ctx in
      let uls = TUls {
        region = ctx.fresh_region ();
        var = snd ctx.uty;
        proto = ctx.name;
      } in
      (range (fst head) (fst e), TFn(head, uls, e))
  }

ty_atom:
  | u=UNIT { fun _ -> (u, TVal("Unit")) }
  | u=UPPER { fun _ -> (fst u, TVal(snd u)) }
  | u=LOWER { fun {uty; _} ->
      assert (snd u = fst uty);
      (fst u, snd uty)
  }
