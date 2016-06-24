open QCheck
open LCheck

module type EXTLATTICE =
sig
  include Regexpdom.EXTLATTICE
  val name  : string
  val arb_elem    : elem Arbitrary.t
  val equiv_pair  : (elem * elem) Arbitrary.t
  val arb_elem_le : elem -> elem Arbitrary.t
end

module type ARB_ARG =
sig
  include ARB_ARG
  val bg_repr : elem
  val succ : elem -> elem
  val compare   : elem -> elem -> int
end

module Arb = Arbitrary

(* Parity domain extended with generators *)
module Parity =
struct
  include Parity
  let name = "parity"
  let arb_elem = Arb.among [Bot; Even; Odd; Top]
  let arb_elem_le e  = match e with
    | Bot   -> Arb.return Bot
    | Even  -> Arb.among [Bot; Even]
    | Odd   -> Arb.among [Bot; Odd]
    | Top   -> arb_elem
  let equiv_pair = Arb.(arb_elem >>= fun r -> match r with
    | Bot  -> return (r,Bot)
    | Even -> return (r,Even)
    | Odd  -> return (r,Odd)
    | Top  -> return (r,Top)) (* Could be refined *)
end

(* Constprop domain extended with generators *)
module Constprop =
struct
  include Constprop
  let name = "constprop"
  let arb_elem = Arb.(choose [return Bot;
		 	      lift (fun i -> Const i) (int 10);
			      return Top])
  let arb_elem_le e  = match e with
    | Bot     -> Arb.return Bot
    | Const c -> Arb.among [Bot; Const c]
    | Top     -> arb_elem
  let equiv_pair = Arb.(arb_elem >>= fun r -> match r with
    | Bot     -> return (r,Bot)
    | Const c -> return (r,Const c)
    | Top     -> return (r,Top)) (* Could be refined *)
end

(* Sign domain extended with generators *)
module Sign =
struct
  include Sign
  let name = "sign"
  let arb_elem = Arb.among (List.map (fun i -> Sign i) [0x00;0x01;0x02;0x03;0x04;0x05;0x06;0x07;])
  let arb_elem_le (Sign i) = match i with
    | 0x00 -> Arb.return bot
    | 0x01 -> Arb.among [bot; Sign 0x01]
    | 0x02 -> Arb.among [bot; Sign 0x02]
    | 0x03 -> Arb.among [bot; Sign 0x01; Sign 0x02; Sign 0x03]
    | 0x04 -> Arb.among [bot; Sign 0x04]
    | 0x05 -> Arb.among [bot; Sign 0x01; Sign 0x04; Sign 0x05]
    | 0x06 -> Arb.among [bot; Sign 0x02; Sign 0x04; Sign 0x06]
    | 0x07 -> arb_elem (* top *)
    | _    ->
      failwith ("redomcheck.ml: found unfamiliar Sign: " ^ (string_of_int i) ^ " in arb_elem_le")
  let equiv_pair = Arb.(arb_elem >>= fun p -> let (Sign i) = p in return (p,Sign i)) (* Could be refined *)
end

(* Modulo domain extended with generators *)
module Modulo =
struct
  module MyMod = struct let n = 8 end
  include Modulo.Make(MyMod)
  let name = "modulo"
  let arb_elem = Arb.(choose [return Bot;
		 	      lift (fun i -> Rem i) (int MyMod.n);
			      return Top])
  let arb_elem_le e  = match e with
    | Bot   -> Arb.return Bot
    | Rem c -> Arb.among [Bot; Rem c]
    | Top   -> arb_elem
  let equiv_pair = Arb.(arb_elem >>= fun r -> match r with
    | Bot   -> return (r,Bot)
    | Rem c -> return (r,Rem c)
    | Top   -> return (r,Top)) (* Could be refined *)
end

(* Intset domain extended with generators *)
module Intset =
struct
  module MyMax = struct let n = 6 end
  include Intset.Make(MyMax)
  let name = "intset"
  let arb_num = Arb.int MyMax.n
  let arb_elem  = Arb.(fix ~base:(return LabelSet.empty) (lift2 LabelSet.add arb_num))

  (*  build_set : 'a Set.t -> ('a -> 'a Set.t) -> ('a Set.t -> 'a Set.t -> 'a Set.t)
                           -> 'a list -> 'a Set.t Arb.t *)
  let rec build_set mt sglton union ls = match ls with
    | []  -> Arb.return mt
    | [l] -> Arb.return (sglton l)
    | _   -> Arb.(int (1 + List.length ls) >>= fun i -> 
		    let ls,rs = split i ls in
		    lift2 union
		      (build_set mt sglton union ls)
		      (build_set mt sglton union rs) )

  let arb_labellist  = Arb.(list ~len:(int 4) arb_num)
  let build_labelset = build_set LabelSet.empty LabelSet.singleton LabelSet.union
  let equiv_pair =
    Arb.(arb_labellist >>= fun ls -> pair (build_labelset ls) (build_labelset ls))

  (*  permute : 'a list -> 'a list Arb.t *)
  let rec permute es = match es with
    | []  -> Arb.return []
    | [e] -> Arb.return [e]
    | _   ->
      let len = List.length es in
      let front,back = split (len/2) es in
      Arb.(permute front >>= fun front' ->
	     permute back  >>= fun back' ->
	       Arb.bool >>= fun b ->
	         if b then return (front' @ back') else return (back' @ front'))

  (*  le_gen : 'a list -> ('a list -> 'b) -> 'b  *)
  let le_gen es build =
    let es_gen = permute es in
    Arb.(es_gen >>= fun es ->
	   int (1 + List.length es) >>= fun i -> 
	     let smaller_es,_ = split i es in
	     build smaller_es)
      
  let arb_elem_le e = le_gen (LabelSet.elements e) build_labelset
end

(* Interval domain extended with generators *)
module Interval =
struct
  include Interval
  let name = "interval"
  let arb_int = Arb.int_range ~start:(-100) ~stop:100
  let arb_lowerbound = Arb.(choose [return MInf; lift (fun i -> LBound i) arb_int])
  let arb_upperbound = Arb.(choose [return PInf; lift (fun i -> UBound i) arb_int])
  let arb_elem = Arb.lift2 (fun lb ub -> interval (lb,ub)) arb_lowerbound arb_upperbound
    (* smart constructor will reduce to Bot when lb > ub. Alternatively:
       Arb.(choose [return Bot;
                    lift2 (fun lb ub -> interval (lb,ub)) arb_lowerbound arb_upperbound]) *)
  let arb_lowerbound_ge lb = match lb with
    | MInf      -> arb_lowerbound
    | LBound lb -> Arb.(lift (fun lb' -> LBound lb') (int_range ~start:lb ~stop:100))
  let arb_upperbound_le ub = match ub with
    | PInf      -> arb_upperbound
    | UBound ub -> Arb.(lift (fun ub' -> UBound ub') (int_range ~start:(-100) ~stop:(ub+1)))
  let arb_elem_le e  = match e with
    | Bot              -> Arb.return Bot
    | Interval (lb,ub) -> Arb.lift2 (fun lb' ub' -> interval (lb',ub')) (arb_lowerbound_ge lb)
                                                                        (arb_upperbound_le ub)
  let equiv_pair = Arb.(arb_elem >>= fun r -> match r with
    | Bot              -> return (r,Bot)
    | Interval (lb,ub) -> return (r,interval (lb,ub))) (* Could be refined *)
end

(* Store lattice extended with generators *)
module StoreLat(L: LATTICE) =
struct
  let name = "Storelattice(" ^ L.name ^ ")"
  include Absstore.Make(L)

  let arb_str = Arb.among ["ch1";"ch2";"ch3";"ch4";"ch5"](*Arb.string*)

  let arb_elem =
    Arb.choose
      [ Arb.return Bot;
	Arb.(fix ~max:10 ~base:(return empty) (fun st -> lift3 extend st arb_str L.arb_elem));
	Arb.(fix ~max:10 ~base:(return top) (fun st -> lift3 extend st arb_str L.arb_elem)); ]
	   
  (*  build_map : ('b Map.t) -> ('a -> 'b -> 'b Map.t -> 'b Map.t) -> 'a * 'b list -> 'b Map.t  *)
  let build_map mt add ls =
    let rec build ls = match ls with
      | [] ->        Arb.return mt
      | (k,v)::ls -> Arb.(build ls >>= fun tbl -> return (add k v tbl)) in
    build ls

  (*  permute : 'a list -> 'a list Arb.t *)
  let rec permute es = match es with
    | []  -> Arb.return []
    | [e] -> Arb.return [e]
    | _   ->
      let len = List.length es in
      let front,back = split (len/2) es in
      Arb.(permute front >>= fun front' ->
 	    permute back  >>= fun back' ->
	     Arb.bool >>= fun b ->
	      if b then return (front' @ back') else return (back' @ front'))

  (*  le_gen : 'a list -> ('a list -> 'b) -> 'b  *)
  let le_gen es build =
    let es_gen = permute es in
    Arb.(es_gen >>= fun es ->
	  int (1 + List.length es) >>= fun i -> 
	   let smaller_es,_ = split i es in
	    build smaller_es)

  (*  le_entries :  ('b -> 'b Arb.t) -> ('a * 'b) list -> (('a * 'b) list) Arb.t *)
  let le_entries arb_elem_le es =
    let rec build es = match es with
      | [] -> Arb.return []
      | (k,v)::es -> Arb.(build es >>= fun es' ->
	  	 	   arb_elem_le v >>= fun v' ->
			    return ((k,v')::es')) in
    build es
      
  (*  build_smap :  (string * L.elem) list -> (L.elem SMap.t) Arb.t *)
  let build_smap = build_map SMap.empty SMap.add
  let arb_elem_le st = match st with
    | Bot -> Arb.return Bot
    | Nonbot st ->
      Arb.(small_int >>= fun i ->
	   if i > 10
	   then
	     lift
	       (fun st -> Nonbot st)
	       (le_gen (SMap.bindings st) Arb.(fun es -> le_entries L.arb_elem_le es >>= build_smap))
	   else return Bot)
    | Exttop st ->
      if SMap.is_empty st
      then arb_elem
      else 
	Arb.(choose
	      [lift
		(fun st -> Nonbot st)
		(le_gen (SMap.bindings st) Arb.(fun es -> le_entries L.arb_elem_le es >>= build_smap));
	       lift
		 (fun st -> Exttop st)
		 (fix ~max:10 ~base:(return st)
		    (fun stgen -> arb_str >>= fun s ->
		      if SMap.mem s st
		      then lift3 SMap.add (return s) (L.arb_elem_le (SMap.find s st)) stgen
		                    (* generate entry less than present *)
		      else lift3 SMap.add (return s) L.arb_elem stgen));
	       return Bot;])

 let equiv_pair = Arb.(arb_elem >>= fun st -> match st with
                         | Bot -> return (Bot,Bot)
			 | Nonbot st ->
 			   permute (SMap.bindings st) >>= fun perm_entries ->
			    (build_smap perm_entries) >>= fun perm_st ->
			     return (Nonbot st,Nonbot perm_st)
			   (* pair (return st) (build_smap perm_entries) *)
			 | Exttop st ->
 			   permute (SMap.bindings st) >>= fun perm_entries ->
			    (build_smap perm_entries) >>= fun perm_st ->
			     return (Exttop st,Exttop perm_st) )
end

module ParityStore = StoreLat(Parity)
module SignStore = StoreLat(Sign)
module ConstpropStore = StoreLat(Constprop)
module ModStore = StoreLat(Modulo)
module IntervalStore = StoreLat(Interval)

(* Regular expression domain extended with generators *)
module RegLat(L : EXTLATTICE) =
struct
  let name = "Reglattice(" ^ L.name ^ ")"
  include Regexpdom.Make(L)
  let arb_elem =
    Arb.(fix ~max:10 ~base:(choose [return Regexpdom.Empty;
				    return Regexpdom.Eps;
				    lift (fun e -> letter e) L.arb_elem])
	   (fun gr -> choose [lift (fun r -> kleene r) gr;
			      lift (fun r -> compl r) gr;
			      lift2 (fun r1 r2 -> concat (r1,r2)) gr gr;
			      lift2 (fun r1 r2 -> union (r1,r2)) gr gr;
			      lift2 (fun r1 r2 -> inter (r1,r2)) gr gr;
			     ]))
  let rec arb_elem_le r = match r with
    | Regexpdom.Empty          -> Arb.lift2 (fun l l' -> if L.leq (L.meet l l') L.bot
 					                 then inter (letter l, letter l')
					                 else r) L.arb_elem L.arb_elem
    | Regexpdom.Eps            -> Arb.among [Regexpdom.Empty;r]
    | Regexpdom.Letter a       -> Arb.(choose [return Regexpdom.Empty;
					       lift (fun a' -> letter a') (L.arb_elem_le a)])
    | Regexpdom.Kleene r'      -> Arb.(choose (* Could be refined *)
					 [return Regexpdom.Empty;
					  return Regexpdom.Eps;
					  return r';
					  lift (fun r'' -> kleene r'') (arb_elem_le r')])
    | Regexpdom.Concat []      -> Arb.return (Regexpdom.Concat [])
    | Regexpdom.Concat [r]     -> arb_elem_le r
    | Regexpdom.Concat (r::rs) -> Arb.lift2 (fun r' rs' -> concat (r',rs'))
                                    (arb_elem_le r) (arb_elem_le (Regexpdom.Concat rs))
    | Regexpdom.Union []       -> Arb.return (Regexpdom.Empty)
    | Regexpdom.Union (r::rs)  -> Arb.lift2 (fun r' rs' -> union (r',rs'))
				      (arb_elem_le r) (arb_elem_le (Regexpdom.Union rs))
    (* this may indirectly discard one or more of the summands, via union(bot,...) *)
    | Regexpdom.Inter []       -> Arb.return (Regexpdom.Empty) (* unreachable *)
    | Regexpdom.Inter [r]      -> arb_elem_le r
    | Regexpdom.Inter (r::rs)  -> Arb.(small_int >>= fun i ->
                                   if i >=25 then lift2 (fun r' rs' -> inter (r',rs'))
				     (arb_elem_le r) (arb_elem_le (Regexpdom.Inter rs))
				   else lift2 (fun r' rs' -> inter (r,inter (r',rs')))
				     arb_elem (arb_elem_le (Regexpdom.Inter rs)))
                                     (* add one or more elements to the intersection *)
    | Regexpdom.Compl r'       -> Arb.(choose (* Could be refined *)
					 [return Regexpdom.Empty;
					  lift (fun r'' -> inter (r'',(compl r'))) arb_elem;
					  lift (fun r'' -> compl (union (r',r''))) arb_elem])

  let equiv_pair =
    let rec rotate r = match r with
      | Regexpdom.Empty          -> r
      | Regexpdom.Eps            -> r
      | Regexpdom.Letter _       -> r
      | Regexpdom.Kleene r'      -> Regexpdom.Kleene (rotate r') (* forces commutative rot.*)
      | Regexpdom.Concat []      -> Regexpdom.Concat []
      | Regexpdom.Concat [r]     -> rotate r
      | Regexpdom.Concat (r::rs) -> concat (rotate r,rotate (Regexpdom.Concat rs))
      | Regexpdom.Union []       -> Regexpdom.Union []
      | Regexpdom.Union [r]      -> rotate r
      | Regexpdom.Union (r::rs)  -> union (rotate (Regexpdom.Union rs),rotate r)
      | Regexpdom.Inter []       -> Regexpdom.Inter []
      | Regexpdom.Inter [r]      -> rotate r
      | Regexpdom.Inter (r::rs)  -> inter (rotate (Regexpdom.Inter rs),rotate r)
      | Regexpdom.Compl r'       -> Regexpdom.Compl (rotate r') (* forces commutative rot.*)
    in
    Arb.(arb_elem >>= fun r -> return (r,rotate r)) (* Could be refined *)
end

module Pairdom(C1 : EXTLATTICE)(C2 : EXTLATTICE) =
struct
  let name = "Pairlattice(" ^ C1.name ^ "," ^ C2.name ^ ")"
  include Pairdom.MakeExt(C1)(C2)

  let arb_elem = Arb.pair C1.arb_elem C2.arb_elem
  let arb_elem_le (c1,c2) =
    Arb.pair (C1.arb_elem_le c1) (C2.arb_elem_le c2)
  let equiv_pair = Arb.lift2 (fun (c1,d1) (c2,d2) -> (c1,c2),(d1,d2))
                     (C1.equiv_pair) (C2.equiv_pair)
end

module Redpairdom(C1 : EXTLATTICE)(C2 : EXTLATTICE)(Str : sig val prefix : string end) =
struct
  let name = "RedPairlattice(" ^ C1.name ^ "," ^ C2.name ^ ")"
  include Redpairdom.MakeExt(C1)(C2)(Str)

  let arb_elem = Arb.lift2 (fun c1 c2 -> pair(c1,c2)) C1.arb_elem C2.arb_elem
  let arb_elem_le (c1,c2) =
    Arb.lift2 (fun c1 c2 -> pair(c1,c2)) (C1.arb_elem_le c1) (C2.arb_elem_le c2)
  let equiv_pair = Arb.lift2 (fun (c1,d1) (c2,d2) -> (pair(c1,c2),pair(d1,d2)))
                     (C1.equiv_pair) (C2.equiv_pair)
end

module Proddom(C1 : LATTICE)(C2 : LATTICE)(C3 : LATTICE) =
struct
  let name = "Prodlattice(" ^ C1.name ^ "," ^ C2.name ^ "," ^ C3.name ^ ")"
  include Proddom.Make(C1)(C2)(C3)

  let arb_elem = Arb.triple C1.arb_elem C2.arb_elem C3.arb_elem
  let arb_elem_le (c1,c2,c3) =
    Arb.triple (C1.arb_elem_le c1) (C2.arb_elem_le c2) (C3.arb_elem_le c3)
  let equiv_pair = Arb.lift3 (fun (c1,d1) (c2,d2) (c3,d3) -> (c1,c2,c3),(d1,d2,d3))
                     (C1.equiv_pair) (C2.equiv_pair) (C3.equiv_pair)
end

(* A generic functor for generating operation tests over a given lattice L.  *)
(* Includes test suite for:
     L, List(L), Reg(L) and d,concat,kleene,union,inter,rev,first operations *)
module GenericRegexpTests(L : EXTLATTICE) =
struct
  module Tests    = GenericTests(L)
  module TopTests = GenericTopTests(L)
  module RegL     = RegLat(L)
  module RegLTests    = GenericTests(RegL)
  module RegLTopTests = GenericTopTests(RegL)

  let test_d =
    let reg_d = (RegL.name^".d",RegL.d) in
     [(*testsig (module L) ---> (module RegL) -<-> (module RegL) =: reg_d;*) (* we cannot test wrt. Atom(L) *)
      testsig (module L) ---> (module RegL) -$-> (module RegL) =: reg_d;
      testsig (module L) ---> (module RegL) -~-> (module RegL) =: reg_d;]

  let test_rev_d =
    let reg_rev_d = (RegL.name^".rev_d",RegL.rev_d) in
     [testsig (module L) ---> (module RegL) -<-> (module RegL) =: reg_rev_d;
      testsig (module L) ---> (module RegL) -$-> (module RegL) =: reg_rev_d;
      testsig (module L) ---> (module RegL) -~-> (module RegL) =: reg_rev_d;]

  let test_concat =
    let reg_concat = (RegL.name^".concat", fun r1 r2 -> RegL.concat (r1,r2)) in
    [testsig (module RegL) -<-> (module RegL) ---> (module RegL) =: reg_concat;
     testsig (module RegL) -$-> (module RegL) ---> (module RegL) =: reg_concat;
     testsig (module RegL) -~-> (module RegL) ---> (module RegL) =: reg_concat;
     testsig (module RegL) ---> (module RegL) -<-> (module RegL) =: reg_concat;
     testsig (module RegL) ---> (module RegL) -$-> (module RegL) =: reg_concat;
     testsig (module RegL) ---> (module RegL) -~-> (module RegL) =: reg_concat;]

  let test_kleene = (* kleene is not strict (bottom preserving) *)
    let reg_kleene = (RegL.name^".kleene", RegL.kleene) in
    [testsig (module RegL) -<-> (module RegL)  =: reg_kleene;
     testsig (module RegL) -~-> (module RegL)  =: reg_kleene;]

  let test_union = (* union is not strict (bottom preserving) *)
    let reg_union = (RegL.name^".union", fun r1 r2 -> RegL.union (r1,r2)) in
    [testsig (module RegL) -<-> (module RegL) ---> (module RegL) =: reg_union;
     testsig (module RegL) -~-> (module RegL) ---> (module RegL) =: reg_union;
     testsig (module RegL) ---> (module RegL) -<-> (module RegL) =: reg_union;
     testsig (module RegL) ---> (module RegL) -~-> (module RegL) =: reg_union;]

  let test_inter =
    let reg_inter = (RegL.name^".inter", fun r1 r2 -> RegL.inter (r1,r2)) in
    [testsig (module RegL) -<-> (module RegL) ---> (module RegL) =: reg_inter;
     testsig (module RegL) -$-> (module RegL) ---> (module RegL) =: reg_inter;
     testsig (module RegL) -~-> (module RegL) ---> (module RegL) =: reg_inter;
     testsig (module RegL) ---> (module RegL) -<-> (module RegL) =: reg_inter;
     testsig (module RegL) ---> (module RegL) -$-> (module RegL) =: reg_inter;
     testsig (module RegL) ---> (module RegL) -~-> (module RegL) =: reg_inter;]

  let test_widening =
    let reg_widening = (RegL.name^".widening", RegL.widening) in
    [testsig (module RegL) -!-> (module RegL) ---> (module RegL) =: reg_widening;
     testsig (module RegL) -~-> (module RegL) ---> (module RegL) =: reg_widening;
     testsig (module RegL) ---> (module RegL) -!-> (module RegL) =: reg_widening;
     testsig (module RegL) ---> (module RegL) -~-> (module RegL) =: reg_widening;]

  let test_widening0 =
    let reg_widening0 = (RegL.name^".widening0", RegL.widening0) in
    [testsig (module RegL) -!-> (module RegL) ---> (module RegL) =: reg_widening0;
     testsig (module RegL) -~-> (module RegL) ---> (module RegL) =: reg_widening0;
     testsig (module RegL) ---> (module RegL) -!-> (module RegL) =: reg_widening0;
     testsig (module RegL) ---> (module RegL) -~-> (module RegL) =: reg_widening0;]

  let test_widening1 =
    let reg_widening1 = (RegL.name^".widening1", RegL.widening1) in
    [testsig (module RegL) -!-> (module RegL) ---> (module RegL) =: reg_widening1;
     testsig (module RegL) -~-> (module RegL) ---> (module RegL) =: reg_widening1;
     testsig (module RegL) ---> (module RegL) -!-> (module RegL) =: reg_widening1;
     testsig (module RegL) ---> (module RegL) -~-> (module RegL) =: reg_widening1;]

  let test_rev =
    let reg_rev = (RegL.name^".rev", RegL.rev) in
    [testsig (module RegL) -<-> (module RegL) =: reg_rev;
     testsig (module RegL) -$-> (module RegL) =: reg_rev;
     testsig (module RegL) -~-> (module RegL) =: reg_rev;]

  let test_rev_rev_id =  (* forall r. rev (rev r) = r  *)
    mk_test ~n:1000 ~pp:RegL.to_string ~limit:1 ~size:(fun r -> String.length (RegL.to_string r))
            ~name:("rev o rev is identity in " ^ L.name)
      RegL.arb_elem
      (fun r -> RegL.eq (RegL.rev (RegL.rev r)) r)

  let suite = flatten [Tests.suite;
		       TopTests.suite;
		       RegLTests.suite;
		       RegLTopTests.suite;
		       test_d;
		       test_concat;
		       test_kleene;
		       test_union;
		       test_inter;
		       test_widening;
		       test_widening0;
		       test_widening1;
		       test_rev;
		       [test_rev_rev_id]; ]
end

module RegParityTests = GenericRegexpTests(Parity)
module RegSignTests = GenericRegexpTests(Sign)
module RegModuloTests = GenericRegexpTests(Modulo)
module RegConstpropTests = GenericRegexpTests(Constprop)
module RegIntervalTests  = GenericRegexpTests(Interval)
module RegIntsetTests  = GenericRegexpTests(Intset)

module type ARITHLATTICE =
sig
  include LATTICE
  val add : elem -> elem -> elem
  val sub : elem -> elem -> elem
  val mult : elem -> elem -> elem
end
  (* Sum lattice extended with generators *)
module GenericArithmeticTests(L: ARITHLATTICE) =
struct
  let test_l_add =
    let l_add = (L.name^".add", L.add) in
    [testsig (module L) -<-> (module L) ---> (module L) =: l_add;
     testsig (module L) -$-> (module L) ---> (module L) =: l_add;
     testsig (module L) -~-> (module L) ---> (module L) =: l_add;
     testsig (module L) ---> (module L) -<-> (module L) =: l_add;
     testsig (module L) ---> (module L) -$-> (module L) =: l_add;
     testsig (module L) ---> (module L) -~-> (module L) =: l_add;]

  let test_l_sub =
    let l_sub = (L.name^".sub", L.sub) in
    [testsig (module L) -<-> (module L) ---> (module L) =: l_sub;
     testsig (module L) -$-> (module L) ---> (module L) =: l_sub;
     testsig (module L) -~-> (module L) ---> (module L) =: l_sub;
     testsig (module L) ---> (module L) -<-> (module L) =: l_sub;
     testsig (module L) ---> (module L) -$-> (module L) =: l_sub;
     testsig (module L) ---> (module L) -~-> (module L) =: l_sub;]
      
  let test_l_mult =
    let l_mult = (L.name^".mult", L.mult) in
    [testsig (module L) -<-> (module L) ---> (module L) =: l_mult;
     testsig (module L) -$-> (module L) ---> (module L) =: l_mult;
     testsig (module L) -~-> (module L) ---> (module L) =: l_mult;
     testsig (module L) ---> (module L) -<-> (module L) =: l_mult;
     testsig (module L) ---> (module L) -$-> (module L) =: l_mult;
     testsig (module L) ---> (module L) -~-> (module L) =: l_mult;]

  let suite = flatten [test_l_add; test_l_sub; test_l_mult;]
end

module ArithParityTests = GenericArithmeticTests(Parity)
module ArithSignTests = GenericArithmeticTests(Sign)
module ArithConstpropTests = GenericArithmeticTests(Constprop)
module ArithIntervalTests  = GenericArithmeticTests(Interval)
module ArithModuloTests = GenericArithmeticTests(Modulo)

module StringTag =
struct
  type elem = string
  let to_string s = s
  let arb_elem = Arb.among ["ch1";"ch2";"ch3";"ch4";"ch5"] (* Arb.string *)
  let bg_repr = "a"
  let succ s = s ^ "a"
  let compare = String.compare
end

module Prod = Proddom(IntervalStore)(Interval)(Interval)
module ProddomTests = GenericTests(Prod)

module ParityPair = Pairdom(Parity)(Parity)
module IntPair = Pairdom(Interval)(Interval)
module RedParityPair = Redpairdom(Parity)(Parity)(struct let prefix = "" end)
module RedSignPair = Redpairdom(Sign)(Sign)(struct let prefix = "" end)
module RedIntsetPair = Redpairdom(Intset)(Intset)(struct let prefix = "" end)
module RedIntPair = Redpairdom(Interval)(Interval)(struct let prefix = "" end)
module RedParityIntPair = Redpairdom(Parity)(Interval)(struct let prefix = "" end)

module IntPairTests = GenericTests(IntPair)
module IntPairTopTests = GenericTopTests(IntPair)

module RegParityPairTests  = GenericRegexpTests(ParityPair)
module RegIntPairTests  = GenericRegexpTests(IntPair)
module RegRedParityPairTests  = GenericRegexpTests(RedParityPair)
module RegRedSignPairTests  = GenericRegexpTests(RedSignPair)
module RegRedIntsetPairTests  = GenericRegexpTests(RedIntsetPair)
module RegRedIntPairTests  = GenericRegexpTests(RedIntPair)
module RegRedParityIntPairTests  = GenericRegexpTests(RedParityIntPair)

module ParityStoreTests = GenericTests(ParityStore)
module SignStoreTests = GenericTests(SignStore)
module ConstpropStoreTests = GenericTests(ConstpropStore)
module ModStoreTests = GenericTests(ModStore)
module IntervalStoreTests = GenericTests(IntervalStore)

(* Operation tests *)
module IntSto = IntervalStore
let test_lookup =
  let as_lookup = (IntSto.name^".lookup", IntSto.lookup) in
  [pw_right (module StringTag) op_monotone  (module IntSto) (module Interval) =:: as_lookup;
   pw_right (module StringTag) op_strict    (module IntSto) (module Interval) =:: as_lookup;
   pw_right (module StringTag) op_invariant (module IntSto) (module Interval) =:: as_lookup;]

let test_extend = (* Current extend implementation is not strict in third argument *)
  let as_extend = (IntSto.name^".extend", IntSto.extend) in
  [pw_right (module StringTag) (pw_right (module Interval) op_monotone)  (module IntSto) (module IntSto) =:: as_extend;
   pw_right (module StringTag) (pw_right (module Interval) op_strict)  (module IntSto) (module IntSto) =:: as_extend;
   pw_right (module StringTag) (pw_right (module Interval) op_invariant) (module IntSto) (module IntSto) =:: as_extend;
   pw_left (module IntSto) (pw_left (module StringTag) op_monotone)  (module Interval) (module IntSto) =:: as_extend;
   pw_left (module IntSto) (pw_left (module StringTag) op_strict)    (module Interval) (module IntSto) =:: as_extend;
   pw_left (module IntSto) (pw_left (module StringTag) op_invariant) (module Interval) (module IntSto) =:: as_extend;]

(* Widening tests *)
let test_as_widening =
  let as_widening = (IntSto.name^".widening", IntSto.widening) in
  [testsig (module IntSto) -!-> (module IntSto) ---> (module IntSto) =: as_widening;
   testsig (module IntSto) -~-> (module IntSto) ---> (module IntSto) =: as_widening;
   testsig (module IntSto) ---> (module IntSto) -!-> (module IntSto) =: as_widening;
   testsig (module IntSto) ---> (module IntSto) -~-> (module IntSto) =: as_widening;]

let test_proddom_widening =
  let proddom_widening = (Prod.name^".widening", Prod.widening) in
  [testsig (module Prod) -!-> (module Prod) ---> (module Prod) =: proddom_widening;
   testsig (module Prod) -~-> (module Prod) ---> (module Prod) =: proddom_widening;
   testsig (module Prod) ---> (module Prod) -!-> (module Prod) =: proddom_widening;
   testsig (module Prod) ---> (module Prod) -~-> (module Prod) =: proddom_widening;]

let _ =
  if not (!Sys.interactive)
  then
    run_tests
      (flatten [
        (* domain tests *)
	RegParityTests.suite;
        RegSignTests.suite;
	RegModuloTests.suite;
	RegConstpropTests.suite;      (* infinite number of atoms *)
        RegIntervalTests.suite;       (* infinite number of atoms *)
	RegIntsetTests.suite;

	IntPairTests.suite;
	IntPairTopTests.suite;

	RegParityPairTests.suite;
	RegIntPairTests.suite;
	RegRedParityPairTests.suite;
	RegRedSignPairTests.suite; 
	RegRedIntsetPairTests.suite;
	RegRedIntPairTests.suite;
	RegRedParityIntPairTests.suite;

	ProddomTests.suite;

	(* store tests *)
	ParityStoreTests.suite;
	SignStoreTests.suite;
	ConstpropStoreTests.suite;
	ModStoreTests.suite;
        IntervalStoreTests.suite;   (* infinite number of atoms *)
	(* arithmetic tests *)
	ArithParityTests.suite;
	ArithSignTests.suite;
	ArithModuloTests.suite;
	ArithConstpropTests.suite;
	ArithIntervalTests.suite;
	(* operation tests *)
	test_lookup;
        test_extend;
        test_as_widening;
        test_proddom_widening;
      ])
  else false
