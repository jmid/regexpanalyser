%{
  let token_var = ref 0
  let token_pp = ref 0

  let find var_tab s = 
    try Hashtbl.find var_tab s 
    with Not_found -> 
      Hashtbl.add var_tab s !token_var;
      let p = !token_var in
	incr token_var;
	p
	  
  let new_pp () = 
    let p = !token_pp in
      incr token_pp;
      p

  let vars_used var_tab = Hashtbl.fold (fun s p l -> p::l) var_tab []
%}

%start prog
%type < Ast.exprog > prog

%%

prog:
 | proc EOF  { [$1] }
 | proc prog { $1::$2 }
 ;

proc:
 | SPAWN IDENT LPAR RPAR block { ($2,$5) }
 ;

opt_semi : 
 | SEMI {}
 |      {}
 ;

instrs : 
 | instr opt_semi       { [$1] }
 | instr SEMI instrs    { ($1::$3) }
 | LBRACE instrs RBRACE { $2 }
 ;

expr:
 | INT            { Ast.Num $1 }
 | LPAR expr RPAR { $2 }
 | QUEST          { Ast.Any }
 | IDENT          { Ast.Var $1}
 | SUB expr       { Ast.Binop (Ast.Num 0,Ast.Minus,$2) }
 | expr ADD expr  { Ast.Binop ($1,Ast.Plus,$3) }
 | expr SUB expr  { Ast.Binop ($1,Ast.Minus,$3) }
 | expr MULT expr { Ast.Binop ($1,Ast.Mult,$3) }
 ;

test:
 | TRUE           { Ast.True }
 | FALSE          { Ast.False }
 | NOT test       { Ast.Not $2 }
 | LPAR test RPAR { $2 }
 | expr comp expr { Ast.Relop ($1,$2,$3) }
 | test AND test  { Ast.Conj ($1,$3) }
/* | test OR test   { Ast.Or ($1,$3) } */
 ;

comp:
 | ASSIGN { Ast.Eq }
 | EQ     { Ast.Eq }
/* | NEQ    { Ast.Neq } */
 | LE     { Ast.Leq }
 | LT     { Ast.Lt }
 ;

instr:
 | IDENT ASSIGN expr              { Ast.ExAssign ($1,$3) }
 | IF test block ELSE block       { Ast.ExIf ($2,$3,$5) }
 | WHILE test block               { Ast.ExWhile ($2,$3) }
/* | FOR LPAR IDENT ASSIGN expr SEMI test SEMI expr RPAR block
      { let init = Ast.ExAssign ($3, $5) in
	let incr = Ast.ExAssign ($3, $9) in	  
	let body = Ast.ExWhile ($7, incr :: $11) in
	[init;body] } */
 | IDENT QUEST IDENT              { Ast.ExChread ($1,$3) }
 | IDENT BANG expr                { Ast.ExChwrite ($1,$3) }
 | CHOOSE LBRACE proc_list RBRACE { Ast.ExChoose $3 }
 | STOP                           { Ast.ExStop }
 ;

proc_list: /* -> exblock list */
 | block                          { [$1] }
 | block BAR proc_list            { ($1::$3) }
 ;

block:  /* -> exblock */
 | instr                { [$1] }
 | LBRACE instrs RBRACE { $2 }
 | LBRACE RBRACE        { [] }
 ;

%%
