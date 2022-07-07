%{
open Syntax

let range (start, _) (_, fin) = (start, fin)

type proto_ctx = {
  name: string;
  var_of_named_ty: string -> int;
  proto_arg: string;
  fresh_region: unit -> int;
}

let fresh_var ctx = TVar (ref (Unbd (ctx.fresh_var ()))) 

let xloc = Syntax.xloc
let xty = Syntax.xty
let xv = Syntax.xv
%}


%token <Syntax.loc * string> LOWER
%token <Syntax.loc * string> UPPER

%token <Syntax.loc> ENTRY
%token <Syntax.loc> LET
%token <Syntax.loc> IN
%token <Syntax.loc> LAM
%token <Syntax.loc> UNIT
%token <Syntax.loc> LPAREN
%token <Syntax.loc> RPAREN
%token <Syntax.loc> LBRACE
%token <Syntax.loc> RBRACE
%token <Syntax.loc> PIPE
%token <Syntax.loc> EQ
%token <Syntax.loc> COLON
%token <Syntax.loc> ARROW
%token <Syntax.loc> CHOICE
%token <Syntax.loc> PROTO
%token EOF

%start toplevel
%type <Syntax.parse_ctx -> Syntax.program> toplevel
%type <Syntax.parse_ctx -> Syntax.e_expr> expr
%%

toplevel:
  | EOF { fun _ -> [] }
  | d=decl rest=toplevel { fun ctx -> (d ctx)::(rest ctx) }

decl:
  | PROTO name=LOWER arg=LOWER COLON ty=ty { fun ctx ->
      let arg = snd arg in
      let var_table = ref [] in
      let var_of_named_ty =
        fun name ->
          (if not (List.mem_assoc name (!var_table)) then
            var_table := ((name, ctx.fresh_var ())::(!var_table))
          );
          List.assoc name (!var_table)
      in
      let fresh_region = let n = ref 0 in fun () -> incr n; !n in
      let ty = ty { name=snd name; var_of_named_ty; proto_arg=arg; fresh_region} in
      Proto{name; arg; bound_vars=(!var_table); sig'=ty}
  }
  | ENTRY name=LOWER EQ e=expr { fun ctx ->
      Def(name, e ctx, true)
  }
  | LET name=LOWER EQ e=expr { fun ctx ->
      Def(name, e ctx, false)
  }

expr:
  | app=expr_app { app }
  | e=expr_lets { fun c -> e c }
  | lam=LAM arg=pat ARROW body=expr { fun ctx ->
      let body = body ctx in
      let loc = range lam (xloc body) in
      (loc, fresh_var ctx, Clos(arg ctx, Lam (ctx.fresh_clos_name ()), body))
  }
  | c=CHOICE LBRACE rev_branches=branches r=RBRACE { fun ctx ->
      let rev_branches = rev_branches ctx in
      let loc = range c r in
      (loc, fresh_var ctx, Choice(List.rev rev_branches))
  }

expr_app:
  | e=expr_atom { e }
  | head=expr_app e=expr_atom { fun c ->
      let head = head c in
      let e = e c in
      (range (xloc head) (xloc e), fresh_var c, Call(head, e))
  }

expr_lets:
  | l=LET loc_x=LOWER EQ e=expr IN body=expr { fun c ->
      let body = body c in
      let loc = range l (xloc body) in
      (loc, fresh_var c, Let(loc_x, e c, body))
  }

branches:
  | PIPE body=expr { fun ctx -> [body ctx] }
  | rest=branches PIPE body=expr { fun ctx -> body ctx::(rest ctx) }

expr_atom:
  | x=LOWER { fun ctx -> (fst x, fresh_var ctx, Var (snd x)) }
  | v=UPPER { fun _ -> (fst v, TVal (snd v), Val (snd v)) }
  | v=UNIT  { fun _ -> (v, TVal "Unit", Val "Unit") }
  | l=LPAREN e=expr r=RPAREN { fun ctx -> 
      let e = e ctx in
      (range l r, xty e, xv e)
  }

pat:
  | x=LOWER { fun ctx -> (fst x, fresh_var ctx, PVar (snd x)) }
  | u=UNIT { fun _ -> (u, TVal("Unit"), PVal("Unit")) }
  | hd=UPPER { fun _ -> (fst hd, TVal(snd hd), PVal(snd hd)) }

ty:
  | arrow=ty_arrow { fun ctx -> arrow ctx }

ty_arrow:
  | e=ty_atom { fun ctx -> e ctx }
  | head=ty_atom ARROW e=ty_arrow { fun ctx ->
      let unspec = (Pending{
        region = ctx.fresh_region ();
        ty = UVar (ctx.var_of_named_ty ctx.proto_arg);
        proto = ctx.name;
      }) in
      let t_fn = ref (TVal "") in
      let uls = TLSet {
        solved = [];
        unspec = [ref unspec];
        ambient = t_fn;
      } in
      let head = head ctx in
      let e = e ctx in
      t_fn := TFn(head, uls, e);
      (range (fst head) (fst e), !t_fn)
  }

ty_atom:
  | u=UNIT { fun _ -> (u, TVal("Unit")) }
  | u=UPPER { fun _ -> (fst u, TVal(snd u)) }
  | u=LOWER { fun {var_of_named_ty; _} ->
      let ty_var = var_of_named_ty (snd u) in
      (fst u, UVar(ty_var))
  }
  | l=LPAREN t=ty r=RPAREN { fun ctx ->
      let t = t ctx in
      (range l r, snd t)
  }
