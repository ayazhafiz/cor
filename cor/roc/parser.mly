%{
open Syntax

let range (start, _) (_, fin) = (start, fin)
%}


%token <Syntax.loc * string> IDENT
%token <Syntax.loc * int>    NUM

%token <Syntax.loc> LET
%token <Syntax.loc> AND
%token <Syntax.loc> LAM
%token <Syntax.loc> LPAREN
%token <Syntax.loc> RPAREN
%token <Syntax.loc> EQ
%token <Syntax.loc> COMMA
%token <Syntax.loc> ARROW
%token <Syntax.loc> WHEN
%token <Syntax.loc> IS
%token <Syntax.loc> IF
%token <Syntax.loc> THEN
%token <Syntax.loc> ELSE
%token EOF

%start toplevel
%type <Syntax.loc_expr> toplevel
%%

toplevel:
  | e=expr EOF { e }

expr:
  | rev_e=expr_app { 
      let e = List.rev rev_e in
      let head = List.hd e in
      let args = List.tl e in
      if List.length args == 0
      then head
      else (range (fst head) (fst (List.hd rev_e)), Call(head, args))
  }
  | e=expr_lets { e }
  | lam=LAM params=param_chain ARROW body=expr {
      let loc = range lam (fst body) in
      (loc, Clos(params, body))
  }
  | w=WHEN e=expr IS rev_branches=branches {
      let loc = range w (fst @@ fst @@ List.hd rev_branches) in
      (loc, When(e, List.rev rev_branches))
  }

expr_app:
  | e=expr_atom { [e] }
  | head=expr_app e=expr_atom { e::head }

expr_lets:
  | loc_x=IDENT EQ e=expr chain=and_chain {
      let (rest, body) = chain in
      let loc = range (fst loc_x) (fst body) in
      let e =
        if List.length rest == 0
        then Let(loc_x, e, body)
        else LetRec((loc_x, e)::rest, body)
      in (loc, e)
  }

and_chain:
  | body=expr { ([], body) }
  | AND loc_x=IDENT EQ e=expr chain=and_chain {
      let (rest, body) = chain in
      ((loc_x, e)::rest, body)
  }

param_chain:
  | p=IDENT COMMA rest=param_chain { p::rest }
  | p=IDENT { [p] }

branches:
  | pat=expr_atom ARROW body=expr_atom { [(pat, body)] }
  | rest=branches pat=expr_atom ARROW body=expr_atom { (pat, body)::rest }

expr_atom:
  | x=IDENT { (fst x, Var (snd x)) }
  | n=NUM   { (fst n, Int (snd n)) }
