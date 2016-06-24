module A = Ast
module Analyzer = Analyzer.Intanalyzer
module R = Analyzer.R
module I = Interval
  
module WLex = Whilelexer
module WPar = Whileparser
module RELexerInfo = Regexplexer.Make(Ast) (* RE lexer parameterized with Ast *)

let parse_pol s = Regexpparser.regexp RELexerInfo.nexttoken (Lexing.from_string s)
 
(*  calc_pos : Lexing.lexbuf -> int * int  *)
let calc_pos lexbuf =
  let pos  = lexbuf.Lexing.lex_curr_p in
  let line = pos.Lexing.pos_lnum in
  let col  = pos.Lexing.pos_cnum - pos.Lexing.pos_bol in
  (line,col)

(*  parse_lexbuf : -> string -> Lexing.lexbuf -> (unit -> unit) -> Ast.prog  *)
let parse_lexbuf f lexbuf close =
  try WPar.prog WLex.nexttoken lexbuf 
  with Parsing.Parse_error -> 
    let line,col = calc_pos lexbuf in
    begin
      Printf.printf " Parse error in %s line %i, column %i\n" f line col;
      close();
      if !Sys.interactive then raise Parsing.Parse_error else exit(1);
    end

(*  parse_str : string -> Ast.stmt  *)
let parse_str s = parse_lexbuf "input string" (Lexing.from_string s) (fun () -> ())

(*  parse_file : string -> Ast.stmt  *)
let parse_file f =
  let ch  = open_in f in
  let stm = parse_lexbuf f (Lexing.from_channel ch) (fun () -> close_in ch) in
  let ()  = close_in ch in
  stm

(*  parse_one : string -> Ast.stmt  *)
let parse_one str = match parse_str str with
  | (_,stmt)::_ -> stmt
  | _           -> failwith "parse_one did not receive a process"

(*  eval_str : string -> unit  *)
let eval_str ?(pp=true) ?(time=false) str = match parse_str str with
  | (_,s)::_ ->
    let () = Ast.reset_info () in
    let ast = Ast.desugar_proc s in
    let () = if pp then Ast.print_info () else () in
    Analyzer.eval_future_top ~pp ~time ast
  | _ -> failwith "eval_str did not receive a process"

(*  eval_str_policy : string -> string -> unit  *)
let eval_str_policy ?(pp=true) ?(time=false) str pol = match parse_str str with
  | (_,s)::_ ->
    let () = Ast.reset_info () in
    let ast = Ast.desugar_proc s in
    let pol = parse_pol pol in
    let () = if pp then Ast.print_info () else () in
    Analyzer.eval_future_policy ~pp ~time ast pol
  | _ -> failwith "eval_str_policy did not receive a process"

(*  eval_file : string -> unit  *)
let eval_file ?(pp=true) ?(time=false) f = match parse_file f with
  | (_,s)::_ ->
    let () = Ast.reset_info () in
    let ast = Ast.desugar_proc s in
    let () = if pp then Ast.print_info () else () in
    Analyzer.eval_future_top ~pp ~time ast
  | _ -> failwith "eval_file did not receive a process"

(*  eval_file_policy : string -> string -> unit  *)
let eval_file_policy ?(pp=true) ?(time=false) f pol = match parse_file f with
  | (_,s)::_ ->
    let () = Ast.reset_info () in
    let ast = Ast.desugar_proc s in
    let pol = parse_pol pol in
    let () = if pp then Ast.print_info () else () in
    Analyzer.eval_future_policy ~pp ~time ast pol
  | _ -> failwith "eval_file_policy did not receive a process"

(*  eval_proc : exstmt -> unit  *)
let eval_proc_policy ?(pp=true) ?(time=false) s pol =
  let () = Ast.reset_info () in
  let pol = parse_pol pol in
  let ast = Ast.desugar_proc s in
  let () = if pp then Ast.print_info () else () in
  Analyzer.eval_future_policy ~pp ~time ast pol

(*  eval_proc : exstmt -> unit  *)
let eval_proc ?(pp=true) ?(time=false) s =
  eval_proc_policy ~pp ~time s "Top"


let swap (p,p') = (p',p)
let pp = ref true (*false*)
let time = ref false (*true*)
let examples = (* a number of examples with an (optional) list of policies *)
  [ ("Ast.deadlock", fst A.deadlock, [("","ch_b?[-oo;+oo] . ch_a![-oo;+oo]")]);
    ("Ast.cc80const, p2", snd A.cc80const, [("","ch![1;1] . ch![2;2]")]);
    ("Ast.cc80, p1", fst A.cc80, [("","ch0?[-oo;+oo] . (ch1![-oo;+oo] . ch0![-oo;+oo])*")]);
    ("Ast.cc80, p2", snd A.cc80, [("","(ch0![0;10] . ch1?[0;10])*")]);
    ("Ast.counter, p2", snd A.counter, []);
    ("Ast.highscore 0, server", snd (A.highscore 0), (* examples from paper intro *)
                                  [("non-negative", "(ask![0;+oo] + report![0;+oo] + hsc?[-oo;+oo])*");
				   ("no reports",   "(ask![0;+oo] + hsc?[-oo;+oo])*");
				   ("wrong order",  "(ask![0;+oo] + report![0;+oo] . hsc?[-oo;+oo])*";)]); 
    ("Ast.math, server", snd A.math, [("","add![3;3] . add![4;4] . add?[-oo;+oo]")]);
    ("Ast.math_alt, server", snd A.math_alt, [("","add![3;3] . add![4;4] . res?[-oo;+oo]")]);
    ("Ast.math2, server", snd A.math2,
       [("only add",    "add![3;3] . add![4;4] . add?[-oo;+oo]");
        ("only square", "square![3;3] . square?[-oo;+oo]");
        ("both ops",    "(add![3;3] . add![4;4] . add?[-oo;+oo]) + (square![3;3] . square?[-oo;+oo])");]);
    ("Ast.zwrcb80, client", fst A.zwrcb80, []);
    ("Ast.zwrcb80, server", snd A.zwrcb80, []);
    ("Ast.zwrcb80', client", fst A.zwrcb80',
                         [("","(acc_req?[-oo;+oo] + acc_response![0;1] + acc_relinquished?[-oo;+oo])*")]);
    ("Ast.zwrcb80', server", snd A.zwrcb80',
                                          [("no relinquish", "(acc_req![0;+oo] + acc_response?[0;1])*")]);
    ("Ast.simplerclientserver, client", fst (A.simplerclientserver 0 2), []);
    ("Ast.simplerclientserver, server cap 2", snd (A.simplerclientserver 0 2),
      [("only init",           "init![0;0]");
       ("only init,status",    "init![0;0] . status?[-oo;+oo]");
       ("init,status,done",    "init![0;0] . status?[1;1] . done![0;0]");
       ("(init,status,done)*", "(init![0;0] . (status?[0;0] . init![0;0])* . status?[1;1] . done![0;0])*");
      ]);
    ("Ast.clientserver, client", fst (A.clientserver 0 2),
      [("","(init?[0;+oo] + status![0;1] + ask?[0;+oo] + reply![0;1] + done?[0;+oo])*")]);
    (* server is identical to simplerclientserver *)
  ]

let _ =
(*
  let eval_aexp_pp (a,sto) =
    (I.pprint (Intstore.eval_aexp a sto); Format.print_newline()) in
  let eval_bexp_true_pp (b,sto) =
    (Intstore.pprint (Intstore.eval_bexp_true b sto); Format.print_newline()) in
  let eval_bexp_false_pp (b,sto) =
    (Intstore.pprint (Intstore.eval_bexp_false b sto); Format.print_newline()) in
  let store = Intstore.extend
                (Intstore.extend Intstore.empty "x" (I.interval (I.LBound (-2),I.UBound 1)))
		                            "y" (I.interval (I.LBound (-5),I.UBound 3))
  in *)
  if !Sys.interactive then () else
    begin
      List.iter
	(fun (name,p,pols) ->
	  begin
	    Format.printf "%s:\n--------------------------------------------------------\n" name;
	    Format.print_flush ();
	    eval_proc ~pp:!pp ~time:!time p;
	    Format.printf "\n";
	    List.iter (fun (desc,pol) ->
	      begin
		Format.printf "%s %s (with policy):\n\
------------------------------------------------------------------------\n" name desc;
		Format.print_flush ();
		eval_proc_policy ~pp:!pp ~time:!time p pol;
		Format.printf "\n";
	      end) pols;
	    
	end) examples;
(*      
    Format.printf "eval_aexp:\n";
    List.iter eval_aexp_pp
      [(A.Num 42,  Intstore.empty);
       (A.Var "x", Intstore.empty);
       (A.Any,     Intstore.empty);
       (A.Binop (A.Num 3, A.Plus, A.Num 4),      Intstore.empty);
       (A.Binop (A.Num 3, A.Minus, A.Num 4),     Intstore.empty);
       (A.Binop (A.Var "x", A.Plus, A.Var "y"),  store);
       (A.Binop (A.Var "x", A.Minus, A.Var "y"), store);
      ];

    Format.printf "eval_bexp_true:\n";
    List.iter eval_bexp_true_pp
      [(A.True,  store);
       (A.False, store);
       (A.Not A.True, store);
       (A.Not A.False, store);
       (A.Relop (A.Var "x", A.Eq, A.Var "y"),  store);
       (A.Relop (A.Var "y", A.Eq, A.Var "x"),  store);
       (A.Relop (A.Var "x", A.Lt, A.Var "y"),  store);
       (A.Relop (A.Var "y", A.Lt, A.Var "x"),  store);
       (A.Relop (A.Var "x", A.Leq, A.Var "y"), store);
       (A.Relop (A.Var "y", A.Leq, A.Var "x"), store);
       (A.Conj (A.True, A.False),              store);
       (A.Conj (A.Relop (A.Var "x",A.Eq,A.Num 1),
		A.Relop (A.Var "y",A.Leq,A.Num 0)),       store);
       (A.Conj (A.Not (A.Relop (A.Var "x",A.Eq,A.Num 1)),
		A.Relop (A.Var "x",A.Leq,A.Num 0)),       store);
       (A.Conj (A.Not (A.Relop (A.Var "y",A.Eq,A.Num 1)),
		A.Relop (A.Var "y",A.Leq,A.Num 0)),       store); ];

    Format.printf "eval_bexp_false:\n";
    List.iter eval_bexp_false_pp
      [(A.True,        store);
       (A.False,       store);
       (A.Not A.True,  store);
       (A.Not A.False, store);
       (A.Relop (A.Var "x", A.Eq, A.Var "y"),  store);
       (A.Relop (A.Var "y", A.Eq, A.Var "x"),  store);
       (A.Relop (A.Var "x", A.Lt, A.Var "y"),  store);
       (A.Relop (A.Var "y", A.Lt, A.Var "x"),  store);
       (A.Relop (A.Var "x", A.Leq, A.Var "y"), store);
       (A.Relop (A.Var "y", A.Leq, A.Var "x"), store);
       (A.Conj (A.True, A.False), store);
       (A.Conj (A.Relop (A.Var "x",A.Eq,A.Num 1),
    	        A.Relop (A.Var "y",A.Leq,A.Num 0)),       store);
       (A.Conj (A.Not (A.Relop (A.Var "x",A.Eq,A.Num 1)),
    	        A.Relop (A.Var "x",A.Leq,A.Num 0)),       store);
       (A.Conj (A.Not (A.Relop (A.Var "y",A.Eq,A.Num 1)),
		A.Relop (A.Var "y",A.Leq,A.Num 0)),       store); ];
*)
  end
