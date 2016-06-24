type binop = Plus | Minus | Mult (* | ... *)
type relop = Eq | Lt | Leq (* | ... *)
type var   = string
type chan  = int
    
type aexp =
  | Num of int
  | Var of var
  | Any
  | Binop of aexp * binop * aexp

type bexp =
  | True
  | False
  | Not of bexp
  | Relop of aexp * relop * aexp
  | Conj of bexp * bexp

type stmt =
  | Skip
  | Assign of var * aexp
  | Seq of stmt * stmt
  | While of bexp * stmt
  | If of bexp * stmt * stmt
  | Chread of chan * var
  | Chwrite of chan * aexp
  | Choice of stmt * stmt
  | Stop
      
type prog = (var * stmt) list


(** AST pretty printers *)
    
(*  ppaexp : Ast.aexp -> string  *)
let rec ppaexp e = match e with
  | Num n            -> string_of_int n
  | Var x            -> x
  | Any              -> "?"
  | Binop (e1,op,e2) ->
    let str = match op with
      | Plus  -> "+"
      | Minus -> "-"
      | Mult  -> "*" in
    "(" ^ (ppaexp e1) ^ ") " ^ str ^ " (" ^ (ppaexp e2) ^ ")"

(** AST for programs in extended syntax *)

module StrSet = Set.Make(String)

(*  fv : aexp -> var set  *)
let rec fv e = match e with
  | Num _          -> StrSet.empty
  | Var x          -> StrSet.singleton x
  | Any            -> StrSet.empty
  | Binop (e,_,e') -> StrSet.union (fv e) (fv e')
    
(** AST for programs in extended syntax *)

type exchan  = string

type exstmt =
  | ExAssign of var * aexp
  | ExWhile of bexp * exblock
  | ExIf of bexp * exblock * exblock
  | ExChread of exchan * var
  | ExChwrite of exchan * aexp
  | ExChoose of exblock list
  | ExRepeatUntil of exblock * bexp
  | ExStop
and exblock = exstmt list

type exprog = (var * exblock) list

type info = { mutable next : int;
	      orig_chname  : (int,string) Hashtbl.t;
	      int_chname   : (string,int) Hashtbl.t; }

let desugar_chname ch info =
  if Hashtbl.mem info.int_chname ch
  then Hashtbl.find info.int_chname ch
  else
      let num = info.next in
      begin
	info.next <- info.next+1;
	Hashtbl.add info.orig_chname num ch;
	Hashtbl.add info.int_chname ch num;
	num
      end

(*  desugar_exstmt : exstmt -> info -> stmt  *)
let rec desugar_exstmt exs info = match exs with
  | ExAssign (x,e)        -> Assign (x,e)
  | ExWhile (b,exb)       -> While (b,desugar_exblock exb info)
  | ExIf (b,exb,exb')     -> let desb = desugar_exblock exb info in
			     let desb' = desugar_exblock exb' info in
			     If (b, desb, desb')
  | ExChread (ch,x)       -> let chnum = desugar_chname ch info in
			     Chread (chnum, x)
  | ExChwrite (ch,e)      -> let chnum = desugar_chname ch info in
			     Chwrite (chnum,e)
  | ExChoose (exbs)       -> (match exbs with
                               | []          -> Skip
			       | [exb]       -> desugar_exblock exb info
			       | [exb1;exb2] ->
				 let desb1 = desugar_exblock exb1 info in
				 let desb2 = desugar_exblock exb2 info in
				 Choice (desb1, desb2)
			       | exb::exbs   ->
				 let desb = desugar_exblock exb info in
				 let desbs = desugar_exstmt (ExChoose exbs) info in
				 Choice (desb,desbs))
  | ExRepeatUntil (exb,b) -> let s = desugar_exblock exb info in
			     Seq (s,While(Not b,s))
  | ExStop                -> Stop
    
(*  desugar_exblock : exblock -> info -> stmt  *)
and desugar_exblock exb info = match exb with
  | []       -> Skip
  | [exs]    -> desugar_exstmt exs info
  | exs::exb -> let desst = desugar_exstmt exs info in
		let desb = desugar_exblock exb info in
		Seq (desst, desb)

let info = { next = 0;
	     orig_chname = Hashtbl.create 43;
	     int_chname  = Hashtbl.create 43; }

(*  reset_info : unit -> unit  *)
let reset_info () =
  begin
    info.next <- 0;
    Hashtbl.reset info.orig_chname;
    Hashtbl.reset info.int_chname;
  end

let print_info () =
  Hashtbl.iter (fun chname i -> Printf.printf "%s -> %i\n" chname i) info.int_chname

(*  desugar_proc : exblock -> stmt  *)
let desugar_proc p = desugar_exblock p info

(*  desugar_twoproc : exblock*exblock -> stmt  *)
let desugar_twoproc (p1,p2) =
  let p1' = desugar_exblock p1 info in
  let p2' = desugar_exblock p2 info in
  (p1',p2')

  
(** Various example programs in the extended syntax *)

(* basic deadlock example (from Hugo) *)
let deadlock =
  let p1 = [ExChread  ("ch_a","x");
	    ExChwrite ("ch_b",Num 1);] in
  let p2 = [ExChread  ("ch_b","y");
	    ExChwrite ("ch_a",Num 2);] in
  (p1,p2)

(* example from Cousot-Cousot:ICALP80, p.125 *)
let cc80 =
  let p1 = [ExAssign ("x",Num 10);
	    ExWhile (Relop (Num 1,Leq,Var "x"),
		     [ExChwrite ("ch0",Var "x"); (* (was: P2) --- process names adapted to channel names *)
		      ExChread  ("ch1","x");]);
	    ExChwrite ("ch0",Var "x");] in
  let p2 = [ExChread  ("ch0","y");               (* (was: P1) --- process names adapted to channel names *)
	    ExWhile (Not (Relop (Var "y",Eq,Num 0)), (*  y <> 0 *)
		     [ExChwrite ("ch1",Binop (Var "y", Minus, Num 1));
		      ExChread  ("ch0","y");]);] in
  (p1,p2)

(* example from Cousot-Cousot:ICALP80, conclusion p.132 *)
let cc80const =
  let p1 = [ExChwrite ("ch",Num 1); (* (was: P2) --- process names adapted to channel names *)
	    ExChwrite ("ch",Num 2);] in
  let p2 = [ExAssign ("x",Num 1);
	    ExAssign ("y",Num 2);
	    ExChread  ("ch","x");   (* (was: P1) --- process names adapted to channel names *)
	    ExChread  ("ch","y");] in
  (p1,p2)

(* a cyclic counter server (wraps around at value 8) and client (queries thrice per iteration) *)
let counter =
  let p1 = [ExWhile (True,
		     [ExChread ("ch","c1");
		      ExChread ("ch","c2");
		      ExChread ("ch","c3");]);] in
  let p2 = [ExAssign ("cnt",Num 0);
	    ExWhile (True,
		     [ExChwrite ("ch",Var "cnt");
		      ExIf (Relop (Var "cnt",Eq,Num 8),
			    [ExAssign ("cnt",Num 0);],
			    [ExAssign ("cnt",Binop (Var "cnt",Plus,Num 1));]);]);] in
  (p1,p2)

(* high score example from paper implemented with Any *)
let highscore id =
  let cl id = [ExAssign ("best",Num 0);
	       ExWhile (True,
			[ExChwrite ("ask",Num id);
			 ExChread ("hsc","best");
			 ExAssign ("new",Any);
			 ExIf (Relop (Var "best",Lt,Var "new"),
			       [ExAssign ("best",Var "new");
				ExChwrite ("report",Var "best");],
			       []);
			]);] in
  let svr = [ExAssign ("highscore",Num 0);
	     ExWhile (True,
		     [ExChoose
			 ([ [ExChread ("ask","cid");
			     ExChwrite ("hsc",Var "highscore");];
			    [ExChread ("report","new");
			     ExIf (Relop (Var "highscore",Lt,Var "new"),
				   [ExAssign ("highscore",Var "new");],
				   []);];
			  ]);]);] in
  (cl id,svr)

(* simple math server from Vasconcelos-Gay-Ravara:TCS06 *)
let math =
  let client = [ExChwrite ("add",Num 3);
		ExChwrite ("add",Num 4);
		ExChread ("add","result");] in
  let server = [ExWhile (True,
			 [ExChoose
			     ([ [ExChread ("add","n1");
				 ExChread ("add","n2");
				 ExChwrite ("add",Binop (Var "n1",Plus,Var "n2"));];
				]);]);] in
  (client,server)

(* simple math server, with separate add/res channels *)
let math_alt =
  let client = [ExChwrite ("add",Num 3);
		ExChwrite ("add",Num 4);
		ExChread ("res","result");] in
  let server = [ExWhile (True,
			 [ExChoose
			     ([ [ExChread ("add","n1");
				 ExChread ("add","n2");
				 ExChwrite ("res",Binop (Var "n1",Plus,Var "n2"));];
				]);]);] in
  (client,server)

(* another math server inspired by Vasconcelos-Gay-Ravara:TCS06 *)
let math2 =
  let client = [ExChoose
		   ([ [ExChwrite ("add",Num 3);
		       ExChwrite ("add",Num 4);
		       ExChread ("add","result");];
		      [ExChwrite ("square",Num 3);
		       ExChread ("square","result");] ]); ] in
  let server = [ExWhile (True,
			 [ExChoose
			     ([ [ExChread ("add","n1");
				 ExChread ("add","n2");
				 ExChwrite ("add",Binop (Var "n1",Plus,Var "n2"));];
				[ExChread ("square","n");
				 ExChwrite ("square",Binop (Var "n",Mult,Var "n"));];
				]);]);] in
  (client,server)

(* simple auth protocol from Zafiropulo-al:TOC80, Fig.1 *)
let zwrcb80 =
  let client = [ExWhile (True,
			 [ExChwrite ("acc_req",Num 0);
			  ExChoose
			    [ [ExChread ("acc_granted","id");
			       ExChwrite ("acc_relinquished",Num 0);];
			      [ExChread ("acc_refused","id");];
			    ];]);] in
  let server = [ExWhile (True,
			 [ExChread ("acc_req","id");
			  ExChoose
			    ([ [ExChwrite ("acc_refused", Var "id");];
			       [ExChwrite ("acc_granted", Var "id");
				ExChread  ("acc_relinquished", "id");];
			     ]);]);] in
  (client,server)

(* same as above, but with data characterizing the response *)
let zwrcb80' =
  let client = [(*ExAssign ("id", Num 0);*)
		ExWhile (True,
			 [ExChwrite ("acc_req",Num 0);
			  ExChread ("acc_response","response");
			  ExIf (Relop (Var "response",Eq,Num 0),
				[], (* denied *)
				[ExChwrite ("acc_relinquished",Num 0)]);
			 ]);] in
  let server = [ExWhile (True,
			 [ExChread ("acc_req","id");
			  ExChoose
			    ([ [ExChwrite ("acc_response", Num 0);]; (* deny  *)
			       [ExChwrite ("acc_response", Num 1);   (* grant *)
				ExChread  ("acc_relinquished", "id");];
			     ]);]);] in
  (client,server)
    
(* same example as below but with simpler client performing only one ask-reply *)
let simplerclientserver ai cap =
  let ok = 1 in
  let notok = 0 in
  let client = [ExWhile (True,
			 [ ExRepeatUntil
			     ( [ExChwrite ("init",Num ai);
				ExChread ("status","y")],
			       Relop (Var "y",Eq, Num ok) );
			   ExChwrite ("ask",Num ai);
			   ExChread ("reply","res");
			   ExChwrite ("done",Num ai); ])] in
  let server  = [ExAssign ("cardset",Num 0); (* *)
		 ExWhile (True,
			  [ExChoose
			      ([ [ExChread ("init","y");
				  ExIf (Relop (Var "cardset",Leq,Num cap), (* model 'set' by a cardinality  abstraction *)
					[ExAssign ("cardset",Binop (Var "cardset",Plus,Num 1));
					 ExChwrite ("status",Num ok);],
					[ExChwrite ("status",Num notok);]); ];
				 [ExChread ("ask","y");
				  ExChwrite ("reply",Var "y");]; (* in or not in set? *)
				 [ExChread ("done","y");
				  ExAssign ("cardset",Binop (Var "cardset",Minus,Num 1)); ]; (* in or not in set? *)
			       ] ); ]);] in
  (client,server)

(* a more ambitious client/server example with 5 channels ("5 kinds of messages") *)
let clientserver ai cap =
  let ok = 1 in
  let notok = 0 in
  let client =
    [ExWhile (True,
	      [ ExRepeatUntil
		  ( [ExChwrite ("init",Num ai);
		     ExChread ("status","y")],
		    Relop (Var "y",Eq, Num ok) );
		ExWhile (Relop (Num 0,Leq,Any), (* some random condition *)
			 [ExChwrite ("ask",Num ai);
		          ExChread ("reply","res")]);
		ExChwrite ("done",Num ai); ])] in
  let server =
    [ExAssign ("cardset",Num 0); (* *)
     ExWhile (True,
	      [ExChoose
		  ([ [ExChread ("init","y");
		      ExIf (Relop (Var "cardset",Leq,Num cap), (* model 'set' by a cardinality abstraction *)
			    [ExAssign ("cardset",Binop (Var "cardset",Plus,Num 1));
			     ExChwrite ("status",Num ok);],
			    [ExChwrite ("status",Num notok);]); ];
		     [ExChread ("ask","y");
		      ExChwrite ("reply",Var "y");]; (* in or not in set? *)
		     [ExChread ("done","y");
		      ExAssign ("cardset",Binop (Var "cardset",Minus,Num 1)); ]; (* in or not in set? *)
		   ] ); ]);] in
  (client,server)
