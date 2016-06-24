(* lexer.mll -*- tuareg -*- *)
{
  module Make (Info : sig val info : Ast.info end) = struct
  open Regexpparser
}

let digit = ['0'-'9']
let numeral = '0' | ['1'-'9'] digit*

let letter = ['a'-'z'] | '_'
let identifier = letter (letter | digit)*

let tab   = '\009'
let cr    = '\013'
let lf    = '\010'
let eol   = cr | lf | cr lf

rule nexttoken = parse
  | eol              { nexttoken lexbuf }
  | (' ' | tab)      { nexttoken lexbuf }
  | "["              { LBRACK }
  | "]"              { RBRACK }
  | "-"              { DASH }
  | "*"              { STAR }
  | "."              { DOT }
  | "("              { LPAR }
  | ")"              { RPAR }
  | "~"              { TILDE }
  | "+"              { PLUS }
  | "&"              { AND }
  | ";"              { SEMI }
  | "!"              { BANG }
  | "?"              { QUEST }
  | "oo"             { INF }
  | "e"              { EPS }
  | "\195\152"       { EMPTY }
  | "Top"            { TOP }
  | numeral as n     { NUM n }
  | identifier as i  { let idnum = Ast.desugar_chname i Info.info in
		       ID idnum }
  | eof              { EOF }

 { end }
