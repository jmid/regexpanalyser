/* Separate token specification to make the definition visible
    to both lexer and parameterized parser */

%token FOR ASSERT ENSURE WHILE IF ELSE STOP CHOOSE SPAWN
%token NOT AND OR EOF LPAR RPAR LBRACE RBRACE EQ NEQ LE LT GE GT
%token SEMI ASSIGN QUEST BANG BAR ADD SUB MULT TRUE FALSE
%token COMMA DOT COLON    /* unused */
%token <string> IDENT
%token <int> INT

%left AND OR
%left SUB ADD
%left MULT
%nonassoc NOT

%%
