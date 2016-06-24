open QCheck

(*  split : int -> 'a list -> 'a list * 'a list  *)
let rec split i ls = match i,ls with
  | 0,   ls -> [],ls
  | n,   [] -> failwith "splitting beyond list length"
  | n,l::ls -> let ls,rs = split (n-1) ls in l::ls,rs


(** Generic lattice tests *)

module type LATTICE_TOPLESS =
sig
  val name  : string
  type elem
  val leq       : elem -> elem -> bool
  val join      : elem -> elem -> elem
  val meet      : elem -> elem -> elem
  val bot       : elem
(*  val top       : elem *)
  val widening  : elem -> elem -> elem
  val eq          : elem -> elem -> bool
  val to_string   : elem -> string
  val fpprint     : Format.formatter -> elem -> unit
  val pprint      : elem -> unit
  val arb_elem    : elem Arbitrary.t
  val equiv_pair  : (elem * elem) Arbitrary.t
  val arb_elem_le : elem -> elem Arbitrary.t
end

module type LATTICE =
sig
  include LATTICE_TOPLESS
  val top : elem
end

module GenericTests (L : LATTICE_TOPLESS) =
struct
  (* Helpers for generating pairs and triples *)
  let arb_pair   = Arbitrary.pair L.arb_elem L.arb_elem
  let arb_triple = Arbitrary.triple L.arb_elem L.arb_elem L.arb_elem

  let ord_pair   = Arbitrary.(L.arb_elem >>= fun e -> pair (L.arb_elem_le e) (return e))
  let ord_triple = Arbitrary.(L.arb_elem >>= fun e -> 
 			       L.arb_elem_le e >>= fun e' ->
 			        L.arb_elem_le e' >>= fun e'' -> return (e'',e',e))

  (* Helpers for pretty printing pairs and triples *)
  let pp_pair    = PP.pair L.to_string L.to_string
  let pp_triple  = PP.triple L.to_string L.to_string L.to_string

  (* Generic lattice property tests *)
  let leq_refl =  (* forall a. a <= a *)
    mk_test ~n:1000 ~pp:L.to_string ~name:("leq reflexive in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (L.to_string a))
      L.arb_elem
      (fun a -> L.leq a a)

  let leq_trans = (* forall a,b,c. a <= b /\ b <= c  =>  a <= c *)
    mk_test ~n:1000 ~pp:pp_triple ~name:("leq transitive in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_triple a))
      ord_triple (* arb_triple *)
      (fun (a,b,c) -> Prop.assume (L.leq a b); 
                      Prop.assume (L.leq b c); 
		      L.leq a c)

  let leq_antisym = (* forall a,b. a <= b /\ b <= a  =>  a = b *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("leq anti symmetric in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      L.equiv_pair (* Alternatively: Arbitrary.(choose [L.equiv_pair; ord_pair; ord_pair >>= fun (a,b) -> return (b,a)]) *)
      (fun (a,b) -> Prop.assume (L.leq a b); 
                    Prop.assume (L.leq b a); 
		    L.eq a b)

(*let top_is_upperbound = (* forall a. a <= top *)
    mk_test ~n:1000 ~pp:L.to_string ~name:("top is upper bound in " ^ L.name)
      L.arb_elem
      (fun a -> L.(leq a top))    *)

  let bot_is_lowerbound = (* forall a. bot <= a *)
    mk_test ~n:1000 ~pp:L.to_string ~name:("bot is lower bound in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (L.to_string a))
      L.arb_elem
      (fun a -> L.(leq bot a))

  let join_comm = (* forall a,b. a \/ b = b \/ a *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("join commutative in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      arb_pair
      (fun (a,b) -> L.(eq (join a b) (join b a)))

  let join_assoc = (* forall a,b,c. (a \/ b) \/ c = a \/ (b \/ c) *)
    mk_test ~n:1000 ~pp:pp_triple ~name:("join associative in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_triple a))
      arb_triple
      (fun (a,b,c) -> L.(eq (join (join a b) c) (join a (join b c)) ))

  let join_idempotent = (* forall a. a \/ a = a *)
    mk_test ~n:1000 ~pp:L.to_string ~name:("join idempotent in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (L.to_string a))
      L.arb_elem
      (fun a -> L.(eq (join a a) a))

  let meet_comm = (* forall a,b. a /\ b = b /\ a *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("meet commutative in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      arb_pair
      (fun (a,b) -> L.(eq (meet a b) (meet b a)))

  let meet_assoc = (* forall a,b,c. (a /\ b) /\ c = a /\ (b /\ c) *)
    mk_test ~n:1000 ~pp:pp_triple ~name:("meet associative in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_triple a))
      arb_triple
      (fun (a,b,c) -> L.(eq (meet (meet a b) c) (meet a (meet b c)) ))

  let meet_idempotent = (* forall a. a /\ a = a *)
    mk_test ~n:1000 ~pp:L.to_string ~name:("meet idempotent in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (L.to_string a))
      L.arb_elem
      (fun a -> L.(eq (meet a a) a))

  let join_meet_absorption = (* forall a,b. a \/ (a /\ b) = a *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("join meet absorbtion in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      arb_pair
      (fun (a,b) -> L.(eq (join a (meet a b)) a))

  let meet_join_absorption =  (* forall a,b. a /\ (a \/ b) = a *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("meet join absorbtion in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      arb_pair
      (fun (a,b) -> L.(eq (meet a (join a b)) a))

  let leq_compat_join =  (* forall a,b. a < b  ==>  a \/ b = b  *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("leq compatible join in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      ord_pair (*arb_pair*)
      (fun (a,b) -> Prop.assume (L.leq a b);
                    L.(eq (join a b) b))

  let join_compat_leq =  (* forall a,b. a \/ b = b  ==> a < b  *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("join compatible leq in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      ord_pair (*arb_pair*)
      (fun (a,b) -> Prop.assume L.(eq (join a b) b);
                    (L.leq a b))

  let join_compat_meet =  (* forall a,b. a \/ b = b  ==>  a /\ b  = a  *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("join compatible meet in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      ord_pair (*arb_pair*)
      (fun (a,b) -> Prop.assume L.(eq (join a b) b);
                    L.(eq (meet a b) a))

  let meet_compat_join =  (* forall a,b. a /\ b  = a  ==>  a \/ b = b    *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("meet compatible join in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      ord_pair (*arb_pair*)
      (fun (a,b) -> Prop.assume L.(eq (meet a b) a);
                    L.(eq (join a b) b))

  let meet_compat_leq =  (* forall a,b. a /\ b  = a  ==>  a <= b  *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("meet compatible leq in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      ord_pair (*arb_pair*)
      (fun (a,b) -> Prop.assume (L.(eq (meet a b) a));
                    L.leq a b)

  let leq_compat_meet =  (* forall a,b. a <= b  ==>  a /\ b  = a  *)
    mk_test ~n:1000 ~pp:pp_pair ~name:("leq compatible meet in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      ord_pair (*arb_pair*)
      (fun (a,b) -> Prop.assume (L.leq a b);
                    L.(eq (meet a b) a))

  (* Consistency check: generated ordered pairs are in fact ordered *)
  let check_ordering =
    mk_test ~n:1000 ~pp:pp_pair ~name:("generated ordered pairs consistent in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (pp_pair a))
      ord_pair (fun (a,b) -> L.leq a b)

  let pp_pair    = PP.pair L.to_string L.to_string
  let ord_pair   = Arbitrary.(L.arb_elem >>= fun v -> pair (L.arb_elem_le v) (return v))

  let suite =
    [ leq_refl; leq_trans; leq_antisym;
      (*top_is_upperbound;*)
      bot_is_lowerbound;
      join_comm; join_assoc; join_idempotent;
      meet_comm; meet_assoc; meet_idempotent;
      join_meet_absorption; meet_join_absorption;
      (* compatibility *)
      leq_compat_join; join_compat_leq;
      join_compat_meet; meet_compat_join;
      meet_compat_leq; leq_compat_meet;
      check_ordering; ]
end

module GenericTopTests (L : LATTICE) =
struct
  let top_is_upperbound = (* forall a. a <= top *)
    mk_test ~n:1000 ~pp:L.to_string ~name:("top is upper bound in " ^ L.name)
            ~limit:1 ~size:(fun a -> String.length (L.to_string a))
      L.arb_elem
      (fun a -> L.(leq a top))

  let suite = [ top_is_upperbound ]
end


(** EDSL for lattice operation tests *)

let ord_pair (type a) (module L : LATTICE_TOPLESS with type elem = a) =
  Arbitrary.(L.arb_elem >>= fun e -> pair (L.arb_elem_le e) (return e))

module type ARB_ARG =
sig
(*  val name  : string *)
  type elem
  val arb_elem    : elem Arbitrary.t
  val to_string   : elem -> string
end

module MkArbListArg (A : ARB_ARG) =
struct
  type elem = A.elem list
  let arb_elem = Arbitrary.(list ~len:(int 20) A.arb_elem)
  let to_string = PP.list A.to_string
end

let op_monotone (type a) (type b) (module PL : LATTICE_TOPLESS with type elem = a)
                                  (module RL : LATTICE_TOPLESS with type elem = b) k =
  let ord_pair = Arbitrary.(PL.arb_elem >>= fun e -> pair (PL.arb_elem_le e) (return e)) in
  k (PP.pair PL.to_string PL.to_string, 
     ord_pair,
     (fun op (v,v') -> Prop.assume (PL.leq v v'); RL.leq (op v) (op v')),
     "monotone",
     1)

let pw_left (type a) (module PL : ARB_ARG with type elem = a) op_prop m1 m2 k =
  op_prop m1 m2 (fun (subpp,subgen,prop,pname,leftargs) -> k (PP.pair PL.to_string subpp,
							      Arbitrary.pair PL.arb_elem subgen,
							      (fun op (a,b) -> prop (op a) b),
						              pname,
							      leftargs+1))
let pw_right (type a) (module PL : ARB_ARG with type elem = a) op_prop m1 m2 k =
  op_prop m1 m2 (fun (subpp,subgen,prop,pname,leftargs) -> k (PP.pair subpp PL.to_string,
							      Arbitrary.pair subgen PL.arb_elem,
							      (fun op (p,st) -> prop (fun v -> op v st) p),
							      pname,
							      leftargs))

let op_invariant (type a) (type b) (module PL : LATTICE_TOPLESS with type elem = a)
                                   (module RL : LATTICE_TOPLESS with type elem = b) k =
  k (PP.pair PL.to_string PL.to_string, 
     PL.equiv_pair,
     (fun op (v,v') -> Prop.assume (PL.eq v v'); RL.eq (op v) (op v')),
     "invariant",
     1)

let op_strict (type a) (type b) (module PL : LATTICE_TOPLESS with type elem = a)
                                (module RL : LATTICE_TOPLESS with type elem = b) k =
  k (PL.to_string, 
     Arbitrary.return PL.bot,
     (fun op bot -> Prop.assume (PL.eq bot PL.bot); RL.eq (op bot) RL.bot),
     "strict",
     1)

let op_increasing (type a) (module PL : LATTICE_TOPLESS with type elem = a)
                           (module RL : LATTICE_TOPLESS with type elem = a) k =
  k (PL.to_string, 
     PL.arb_elem,
     (fun op e -> PL.leq e (op e)),
     "increasing",
     1)

let op_distributive (type a) (type b) (module PL : LATTICE_TOPLESS with type elem = a)
                                      (module RL : LATTICE_TOPLESS with type elem = b) k =
  let arb_pair = Arbitrary.pair PL.arb_elem PL.arb_elem in
  k (PP.pair PL.to_string PL.to_string, 
     arb_pair,
     (fun op (v,v') -> RL.eq (op (PL.join v v')) (RL.join (op v) (op v'))),
     "distributive",
     1)

let ( ---> ) (type e) (type e') = fun a -> fun (b : (module LATTICE_TOPLESS with type elem = e)) ->
                        fun k -> a (fun (l,optranl,r,optranr,prop) ->
			  let module R = (val r : LATTICE_TOPLESS with type elem = e') in (* manual "upcast" *)
			  let r = (module R : ARB_ARG with type elem = e') in             (* the module type *)
			  k (l,(fun prop -> optranl (pw_left r prop)),
			     b,(fun prop -> optranr (pw_right r prop)),
			     prop))
let ( -<-> ) (type e) = fun a -> fun (b : (module LATTICE_TOPLESS with type elem = e)) ->
                        fun k -> a (fun (l,optranl,r,_,_) -> k (r,(fun prop -> prop),b,optranl,op_monotone))
let ( -$-> ) (type e) = fun a -> fun (b : (module LATTICE_TOPLESS with type elem = e)) ->
                        fun k -> a (fun (l,optranl,r,_,_) -> k (r,(fun prop -> prop),b,optranl,op_strict))
let ( -~-> ) (type e) = fun a -> fun (b : (module LATTICE_TOPLESS with type elem = e)) ->
                        fun k -> a (fun (l,optranl,r,_,_) -> k (r,(fun prop -> prop),b,optranl,op_invariant))
let ( -!-> ) (type e) = fun a -> fun (b : (module LATTICE_TOPLESS with type elem = e)) ->
                        fun k -> a (fun (l,optranl,r,_,_) -> k (r,(fun prop -> prop),b,optranl,op_increasing))
let ( -%-> ) (type e) = fun a -> fun (b : (module LATTICE_TOPLESS with type elem = e)) ->
                        fun k -> a (fun (l,optranl,r,_,_) -> k (r,(fun prop -> prop),b,optranl,op_distributive))
    
let testsig (type e) (i : (module LATTICE_TOPLESS with type elem = e)) k =
  k (i,(fun prop -> prop),i,(fun prop -> prop),(fun _ -> assert false))

let finalize opsig (opname,op) =
  opsig (fun (pp,gen,prop,pname,leftargs) ->
           mk_test ~n:1000 ~pp:pp ~limit:1 ~size:(fun a -> String.length (pp a))
                   ~name:(Printf.sprintf "'%s %s in argument %i'" opname pname leftargs)
                   gen (prop op))

let ( =:: ) a (b,c) = finalize a (b,c)

let for_op = (fun (l,_,r,optrans,prop) (opname,op) ->
                finalize (optrans prop l r) (opname,op))
let ( =: ) a (b,c) = a for_op (b,c)


(** A number of reusable lattices *)

(* Note: the following module represents the Boolean lattice:   *)
(*       {true,false} under reverse implication ordering,       *)
(*        bot = true <== true <== false <== false = top         *)
module Bool =
struct
  let name = "Boolean lattice"
  type elem = bool
  let leq a b = if a then true else (not b)
  let join = (&&)
  let meet = (||)
  let bot = true
  let top = false
  let widening = join
  let eq = (=)
  let to_string = string_of_bool
  let pprint = Format.printf "%b"
  let fpprint fmt = Format.fprintf fmt "%b"
  (* The below ones are generic *)
  let arb_elem = Arbitrary.among [bot; top]
  let equiv_pair = Arbitrary.(lift (fun a -> (a,a)) arb_elem)
  let arb_elem_le e = if e = top then arb_elem else Arbitrary.return bot
end

(* Note: the following module represents the dual Boolean lattice:   *)
(*       {true,false} under implication ordering,                    *)
(*        bot = false <== false <== true <== true = top              *)
module DBool =
struct
  let name = "Dual Boolean lattice"
  type elem = bool
  let leq a b = if a then b else true
  let join = (||)
  let meet = (&&)
  let bot = false
  let top = true
  let widening = join
  let eq = (=)
  let to_string = string_of_bool
  let pprint = Format.printf "%b"
  let fpprint fmt = Format.fprintf fmt "%b"
  (* The below ones are generic *)
  let arb_elem = Arbitrary.among [bot; top]
  let equiv_pair = Arbitrary.(lift (fun a -> (a,a)) arb_elem)
  let arb_elem_le e = if e = top then arb_elem else Arbitrary.return bot
end

module GenBoolTests     = GenericTests(Bool)
module GenBoolTopTests  = GenericTopTests(Bool)
module GenDBoolTests    = GenericTests(DBool)
module GenDBoolTopTests = GenericTopTests(DBool)

module MkPairLattice (A : LATTICE_TOPLESS) (B : LATTICE_TOPLESS)
= struct
  let name = "(" ^ A.name ^ " * " ^ B.name ^ ") pair lattice"
  type elem = A.elem * B.elem
  let leq p p'  = A.leq (fst p) (fst p') && B.leq (snd p) (snd p')
  let join p p' = (A.join (fst p) (fst p'), B.join (snd p) (snd p'))
  let meet p p' = (A.meet (fst p) (fst p'), B.meet (snd p) (snd p'))
  let bot       = (A.bot, B.bot)
  let widening p p' = (A.widening (fst p) (fst p'), B.widening (snd p) (snd p'))
  let eq p p'   = A.eq (fst p) (fst p') && B.eq (snd p) (snd p')
  let to_string = PP.pair A.to_string B.to_string
  let fpprint fmt p = Format.fprintf fmt "%s" (to_string p)
  let pprint p  = Format.printf "%s" (to_string p)
  let arb_elem  = Arbitrary.pair A.arb_elem B.arb_elem
  let equiv_pair = Arbitrary.(A.equiv_pair >>= fun (a,a') ->
			      B.equiv_pair >>= fun (b,b') -> return ((a,b),(a',b')))
  let arb_elem_le p = Arbitrary.pair (A.arb_elem_le (fst p)) (B.arb_elem_le (snd p))
end

module MkListLattice (A : LATTICE_TOPLESS) =
struct
  let name = "(" ^ A.name ^ ") list lattice"
  type elem = A.elem list
  let rec leq vs us = match vs,us with
    | [],_ -> true
    | _,[] -> false
    | v::vs,u::us -> A.leq v u && leq vs us
  let rec join vs us = match vs,us with
    | [],_ -> us
    | _,[] -> vs
    | v::vs,u::us -> (A.join v u) :: (join vs us)
  let rec meet vs us = match vs,us with
    | [],_ -> []
    | _,[] -> []
    | v::vs,u::us -> (A.meet v u) :: (meet vs us)
  let bot = []
  let rec widening vs us = match vs,us with
    | [],_ -> us
    | _,[] -> vs
    | v::vs,u::us -> (A.widening v u) :: (widening vs us)
  let rec eq vs us = match vs,us with
    | [],[]-> true
    | v::vs,u::us -> A.eq v u && eq vs us
    | _,_  -> false
  let to_string = PP.list A.to_string
  let pprint vs = Format.printf "%s" (to_string vs)
  let arb_elem = Arbitrary.list A.arb_elem
  let equiv_pair = Arbitrary.(lift (fun v -> (v,v)) arb_elem)
  let arb_elem_le vs = Arbitrary.(int (1 + List.length vs) >>= fun i -> 
		 		  let smaller_vs,_ = split i vs in
				  List.fold_right
				    (fun v acc_gen -> lift2 (fun v a -> v::a) (A.arb_elem_le v) acc_gen)
				    smaller_vs (Arbitrary.return []))
end
