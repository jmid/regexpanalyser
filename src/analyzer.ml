module A = Ast
module LA = Last

module Make(Astore :
            sig
	      module Val : sig
		             include Regexpdom.EXTLATTICE
			     val const : int -> elem
	                   end
	      include Absstore.LATTICE
	      val empty           : elem
              val extend          : elem -> Ast.var -> Val.elem -> elem
	      val eval_aexp       : Ast.aexp -> elem -> Val.elem
	      val eval_bexp_true  : Ast.bexp -> elem -> elem
	      val eval_bexp_false : Ast.bexp -> elem -> elem
            end) =
struct
  module Val = Astore.Val
  module Channame = struct
                      include Interval
		      let widening = join (* only finitely many channel names, widening not needed *)
                    end
  module ReadPair = Redpairdom.MakeExt(Channame)(Val)(struct let prefix = "?" end)
  module WritePair = Redpairdom.MakeExt(Channame)(Val)(struct let prefix = "!" end)
  module Chandom = struct
                     include Pairdom.MakeExt(ReadPair)(WritePair)
                     (*  fpprint : Format.formatter -> elem -> unit  *)
		     let fpprint fmt (c1,c2) =
		       if leq top (c1,c2)
		       then
			 Format.fprintf fmt "Top"
		       else
			 let s1 = ReadPair.to_string c1 in
			 let s2 = WritePair.to_string c2 in
 		         match ReadPair.leq c1 ReadPair.bot, WritePair.leq c2 WritePair.bot with
			   | true,false  -> Format.fprintf fmt "%s" s2
			   | false,true  -> Format.fprintf fmt "%s" s1
			   | true,true
			   | false,false -> Format.fprintf fmt "(%s, %s)" s1 s2  

                     (*  pprint : elem -> unit  *)
		     let pprint e =
		       begin
			 fpprint Format.std_formatter e;
			 Format.print_flush ();
		       end
                     (*  to_string : L.elem -> string  *)
		     let to_string e =
		       begin
			 fpprint Format.str_formatter e;
			 Format.flush_str_formatter ();
		       end
  end
  module R = struct
               include Regexpdom.Make(Chandom)
	       let widening = join
             end

  module Proddom = Pairdom.Make(Astore)(R)

  let writetag ch v = Chandom.pair (ReadPair.bot, WritePair.pair(Channame.const ch, v))
  let readtag ch v = Chandom.pair (ReadPair.pair(Channame.const ch, v), WritePair.bot)

  let pp = ref false

  (*  lfp : absstore * R.elem * R.elem -> 
           (absstore * R.elem * R.elem -> absstore * R.elem * R.elem) -> absstore * R.elem * R.elem *)
  let lfp init func =
    let rec fix prev =
      let next = func prev in
      let next' = Proddom.widening prev next in
      let () = if !pp then
	  begin
	    Format.printf "prev: ";
	    Proddom.pprint prev;
            Format.printf "  next: ";
	    Proddom.pprint next;
            Format.printf "  next': ";
	    Proddom.pprint next';
            Format.printf "\n";
	  end else () in
      if Proddom.leq next' prev then prev else fix next'
    in fix init


  (* ************************************************************ *)
  (*              Version with environment policies               *)
  (* ************************************************************ *)

  let tbl = Hashtbl.create 47

  let store s st =
    begin
      Hashtbl.add tbl s.LA.label st;
      st
    end

  let find s = Hashtbl.find tbl s.LA.label
      
  (*  eval_proc : Ast.stmt -> absstore * R.elem -> absstore * R.elem  *)
  let rec eval_future s (sigma,f) = match s.LA.stmt with
    | LA.Skip           -> (sigma,f) |> store s
    | LA.Assign (x,a)   -> (Astore.extend sigma x (Astore.eval_aexp a sigma),f) |> store s
    | LA.Seq (s1,s2)    -> (sigma,f) |> eval_future s1 |> eval_future s2 |> store s
    | LA.If (b,s1,s2)   ->
      (Proddom.join
	 (eval_future s1 (Astore.eval_bexp_true b sigma,f))
     	 (eval_future s2 (Astore.eval_bexp_false b sigma,f))) |> store s
    | LA.While (b,s')    ->
      let (sigma',f') =
	lfp (sigma,f) (fun (sigma,f) -> eval_future s' (Astore.eval_bexp_true b sigma,f)) in
	  (Astore.eval_bexp_false b sigma',f') |> store s
    | LA.Chread (ch,x)  ->
      let rng = R.range f in
      Chandom.fold_partition
	(fun acc eqcl ->
	  match eqcl with
	    | Chandom.FstEqCl _   -> acc (* read *)
	    | Chandom.SndEqCl eq2 ->     (* write *)
	      let chrep,valrep = WritePair.repr eq2 in
	      let chprj,valprj = WritePair.project eq2 in
	      let d_valrep_f = R.d (writetag ch valrep) f in
	      if Channame.leq (Channame.const ch) chprj (* input concerns 'ch' *)
		&& not (R.leq d_valrep_f R.bot) (* and represents a possible future *)
	      then Proddom.join acc (Astore.extend sigma x valprj, d_valrep_f)
	      else acc)
	(Astore.bot,R.bot) rng |> store s
    | LA.Chwrite (ch,a) ->
      let v' = Astore.eval_aexp a sigma in
      let rng = Chandom.overlay_partitions (R.range f) (Chandom.partition (readtag ch v')) in
      Chandom.fold_partition
	(fun acc eqcl ->
	  match eqcl with
	    | Chandom.FstEqCl eq1 ->      (* read *)
	      let chrep,valrep = ReadPair.repr eq1 in
	      let chprj,valprj = ReadPair.project eq1 in
	      let vvmeet = Val.meet valprj v' in
	      let d_valrep_f = R.d (readtag ch valrep) f in
	      if Channame.leq (Channame.const ch) chprj (* output concerns 'ch' *)
	         && not (Val.leq vvmeet Val.bot)
		 && not (R.leq d_valrep_f R.bot) (* and represents a possible future *)
	      then Proddom.join acc (sigma, d_valrep_f)
	      else acc
	    | Chandom.SndEqCl _   -> acc) (* write *)
	(Astore.bot,R.bot) rng |> store s
    | LA.Choice (s1,s2) ->
      (Proddom.join (eval_future s1 (sigma,f)) (eval_future s2 (sigma,f))) |> store s
    | LA.Stop           -> (Astore.bot,f) |> store s

  (*  ppaexp : Formatter -> Ast.aexp -> unit  *)
  let rec ppaexp fmt e paren = match e with
    | A.Num n            -> Format.fprintf fmt "%i" n
    | A.Var x            -> Format.fprintf fmt "%s" x
    | A.Any              -> Format.fprintf fmt "?"
    | A.Binop (e1,op,e2) ->
      let str = match op with
	| A.Plus  -> "+"
	| A.Minus -> "-"
	| A.Mult  -> "*" in
      if paren
      then
	begin
	  Format.fprintf fmt "(";
	  ppaexp fmt e1 false;
	  Format.fprintf fmt " %s " str;
	  ppaexp fmt e2 true;
	  Format.fprintf fmt ")";
	end
      else
	begin
	  ppaexp fmt e1 false;
	  Format.fprintf fmt " %s " str;
	  ppaexp fmt e2 true;
	end

(** ppaexp, ppaterm, and ppafactor implements an expression
    pretty printer following the below BNF grammar *)
(*
   expr ::= term
          | expr + term
          | expr - term
   term ::= factor
          | term * factor |
 factor ::= Var x
          | Num i
          | Any
          | ( expr )
*)
  let rec ppaexp fmt e = match e with
    | A.Binop (e1,A.Plus,e2) ->
      begin
	ppaexp fmt e1;
	Format.fprintf fmt " + ";
	ppaterm fmt e2;
      end
    | A.Binop (e1,A.Minus,e2) ->
      begin
	ppaexp fmt e1;
	Format.fprintf fmt " - ";
	ppaterm fmt e2;
      end
    | _ -> ppaterm fmt e
  and ppaterm fmt e = match e with
    | A.Binop (e1,A.Mult,e2) ->
      begin
	ppaterm fmt e1;
	Format.fprintf fmt " * ";
	ppafactor fmt e2;
      end
    | _ -> ppafactor fmt e
  and ppafactor fmt e = match e with
    | A.Num n -> Format.fprintf fmt "%i" n
    | A.Var x -> Format.fprintf fmt "%s" x
    | A.Any   -> Format.fprintf fmt "?"
    | A.Binop (_,_,_) ->
      begin
	Format.fprintf fmt "(";
	ppaexp fmt e;
	Format.fprintf fmt ")";
      end

  (*  ppbexp : Format.formatter -> Ast.aexp -> unit  *)
  let rec ppbexp fmt e = match e with
    | A.True   -> Format.fprintf fmt "true"
    | A.False  -> Format.fprintf fmt "false"
    | A.Not e' ->
      begin
	Format.fprintf fmt "not (";
	ppbexp fmt e';
	Format.fprintf fmt ")";
      end
    | A.Relop (e1,op,e2) ->
      let str = match op with
	| A.Eq  -> "=="
	| A.Lt  -> "<"
	| A.Leq -> "<=" in
      begin
	ppaexp fmt e1;
	Format.fprintf fmt " %s " str;
	ppaexp fmt e2;
      end
    | A.Conj (e1,e2) ->
      begin
	Format.fprintf fmt "(";
	ppbexp fmt e1;
	Format.fprintf fmt ") and ("; (* conj's are still fully parenthesized though *)
	ppbexp fmt e2;
	Format.fprintf fmt ")";
      end

  let fmt_str : ('a -> 'b -> 'c, Format.formatter, unit) format = "%s%30s"

  (*  ppstmt : Format.formatter -> Ast.aexp -> unit  *)
  let rec ppstmt fmt s = match s.LA.stmt with
    | LA.Skip         ->
(*      let str = Proddom.to_string (Hashtbl.find tbl s) in*)
      begin
	Format.fprintf fmt fmt_str "skip;" "";(*str;*)
	Proddom.fpprint fmt (find s);
      end
    | LA.Assign (x,e) ->
      begin
	Format.fprintf fmt "%s = " x;
	ppaexp fmt e (*false*);
	Format.fprintf fmt fmt_str ";" "";
	Proddom.fpprint fmt (find s);
      end
    | LA.Seq (s1,s2)  ->
      begin
	Format.fprintf fmt "@[<v 0>";
	ppstmt fmt s1;
	Format.pp_print_space fmt ();
	ppstmt fmt s2;
	Format.fprintf fmt "@]";
      end
    | LA.While (e,s')  ->
      begin
	Format.fprintf fmt "@[<v 0>@[<v 2>while (";
	ppbexp fmt e;
	Format.fprintf fmt ") {";
	Format.pp_print_space fmt ();
	ppstmt fmt s';
	Format.fprintf fmt "@]";
	Format.pp_print_space fmt ();
	Format.fprintf fmt fmt_str "}" "";
	Proddom.fpprint fmt (find s);
	(*	Format.pp_print_space fmt (); *)
	Format.fprintf fmt "@]";
      end
    | LA.If (e,s1,s2)  ->
      begin
	Format.fprintf fmt "@[<v 0>if (";
	ppbexp fmt e;
	Format.fprintf fmt ")";
	Format.pp_print_space fmt ();
	Format.fprintf fmt "@[<v 2>then {";
	Format.pp_print_space fmt ();
	ppstmt fmt s1;
	Format.fprintf fmt "@]";
	Format.pp_print_space fmt ();
	Format.fprintf fmt "@[<v 2>} else {";
	Format.pp_print_space fmt ();
	ppstmt fmt s2;
	Format.fprintf fmt "@]";
	Format.pp_print_space fmt ();
	Format.fprintf fmt fmt_str "}" "";
	Proddom.fpprint fmt (find s);
	(*Format.pp_print_space fmt ();*)
	Format.fprintf fmt "@]";
      end
    | LA.Chread (ch,x) ->
      begin
	Format.fprintf fmt "%i? %s;" ch x;
	Format.fprintf fmt fmt_str "" "";
	Proddom.fpprint fmt (find s);
      end
    | LA.Chwrite (ch,e) ->
      begin
	Format.fprintf fmt "%i! " ch;
	ppaexp fmt e (*true*);
	Format.fprintf fmt fmt_str ";" "";
	Proddom.fpprint fmt (find s);
      end
    | LA.Stop         ->
      begin
	Format.fprintf fmt fmt_str "stop;" "";
	Proddom.fpprint fmt (find s);
      end
    | LA.Choice (s1,s2) ->
      begin
	Format.fprintf fmt "@[<v 0>@[<v 2>choose {";
	Format.pp_print_space fmt ();
	ppstmt fmt s1;
	Format.fprintf fmt "@]";
	Format.pp_print_space fmt ();
	Format.fprintf fmt "@[<v 2>} | {";
	Format.pp_print_space fmt ();
	ppstmt fmt s2;
	Format.fprintf fmt "@]";
	Format.pp_print_space fmt ();
	Format.fprintf fmt "}";
(*	Format.pp_print_space fmt (); *)
	Format.fprintf fmt "@]";
      end

  (*  time_apply : ('a -> 'b) -> 'a -> 'b  *)
  let time_apply f x =
    let start = Unix.gettimeofday () in
    let res = f x in
    let stop = Unix.gettimeofday () in
    let () = Printf.printf "Execution time: %fs\n%!" (stop -. start) in
    res

  (*  eval_future_policy : Ast.stmt -> R.elem -> unit  *)
  let eval_future_policy ?(pp=true) ?(time=false) s pol =
    let ls   = LA.label s in
    let apply = if time then time_apply else fun f x -> f x in
    let _res = apply (eval_future ls) (Astore.empty,pol) in
    if pp
    then
      begin
	Format.pp_print_space Format.std_formatter ();
	Format.fprintf Format.std_formatter fmt_str "" "";
	Proddom.fpprint Format.std_formatter (Astore.empty,pol);
	Format.pp_print_newline Format.std_formatter ();
	ppstmt Format.std_formatter ls;
	Format.pp_print_space Format.std_formatter ();
	Format.pp_print_space Format.std_formatter ();
      end
    else ()

  (*  eval_future_top : Ast.stmt -> unit  *)
  let eval_future_top ?(pp=true) ?(time=false) s =
    eval_future_policy ~pp ~time s R.top
end

module Parityanalyzer = Make(Paritystore)
module Signanalyzer = Make(Signstore)
module Constanalyzer = Make(Conststore)
module Modstore = Modstore.Make(struct let n = 8 end)
module Modanalyzer  = Make(Modstore)
module Intanalyzer  = Make(Intstore)
