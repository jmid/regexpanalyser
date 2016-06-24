/***********************************************************/
/* Regular expression parser for interval-valued channels  */
/***********************************************************/

%{ module I = Interval
   module IA = Analyzer.Intanalyzer %}

%token EOF
%token LBRACK RBRACK TILDE
%token DASH STAR DOT PLUS
%token LPAR RPAR
%token INF EPS SEMI EMPTY AND BANG QUEST TOP
%token <string>NUM
%token <int>ID

%start regexp
%type <Analyzer.Intanalyzer.Chandom.elem Regexpdom.rexp> regexp
%%

regexp    :  regexp0 EOF                       { $1 };

regexp0   :  regexp0 PLUS regexp1              { IA.R.union ($1,$3) }
          |  regexp0 AND  regexp1              { IA.R.inter ($1,$3) }
          |  regexp1                           { $1 };

regexp1   :  regexp1 DOT regexp2               { IA.R.concat ($1,$3) }
          |  regexp2                           { $1 };

regexp2   :  TILDE regexp3                     { IA.R.compl $2 }
          |  regexp3                           { $1 };

regexp3   :  regexp4 STAR                      { IA.R.kleene $1 }
          |  regexp4                           { $1 };

regexp4   :  latlit                            { IA.R.letter $1 }
          |  EPS                               { Regexpdom.Eps }
          |  EMPTY                             { Regexpdom.Empty }
          |  TOP                               { IA.R.top }
	  |  LPAR regexp0 RPAR                 { $2 };

latlit    :  ID BANG  interval                 { let wr_pair = IA.WritePair.pair (I.const $1,$3) in
						 IA.Chandom.pair (IA.ReadPair.bot,wr_pair) }
          |  ID QUEST interval                 { let rd_pair = IA.ReadPair.pair (I.const $1,$3) in
						 IA.Chandom.pair (rd_pair,IA.WritePair.bot) };
  
interval  :  LBRACK lbound SEMI ubound RBRACK  { I.interval ($2,$4) };
  
lbound    :  DASH INF                          { I.MInf }
	  |  DASH NUM                          { I.LBound (-(int_of_string $2)) }
	  |  NUM                               { I.LBound (int_of_string $1) };

ubound    :  PLUS INF                          { I.PInf }
	  |  DASH NUM                          { I.UBound (-(int_of_string $2)) }
	  |  NUM                               { I.UBound (int_of_string $1) };
