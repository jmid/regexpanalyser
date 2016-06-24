module type EXTLATTICE =
sig
  type elem
  val leq       : elem -> elem -> bool
  val join      : elem -> elem -> elem
  val meet      : elem -> elem -> elem
  val bot       : elem
  val top       : elem
  val widening  : elem -> elem -> elem
  val eq          : elem -> elem -> bool
  val to_string   : elem -> string
  val pprint      : elem -> unit
  val fpprint      : Format.formatter -> elem -> unit
  type equiv_class
  type partition
  val compare            : equiv_class -> equiv_class -> int
  val repr               : equiv_class -> elem
  val project            : equiv_class -> elem
  val partition          : elem -> partition
  val fold_partition     : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a
  val overlay_partitions : partition -> partition -> partition
end

module Make(C1 : Absstore.LATTICE)(C2 : Absstore.LATTICE)(Str : sig val prefix : string end) =
struct
  type elem = C1.elem * C2.elem

  let bot = (C1.bot,C2.bot)

  (* a smart constructor for handling reduction *)
  let pair (c1,c2) = if C1.eq c1 C1.bot || C2.eq c2 C2.bot then bot else (c1,c2)

  let top = pair (C1.top,C2.top)

  (*  leq : elem -> elem -> bool  *)
  let leq (c1,c2) (d1,d2) = C1.leq c1 d1 && C2.leq c2 d2

  (*  eq : elem -> elem -> bool  *)
  let eq (c1,c2) (d1,d2) = C1.eq c1 d1 && C2.eq c2 d2
    
  (*  join : elem -> elem -> elem  *)
  let join (c1,c2) (d1,d2) = pair (C1.join c1 d1, C2.join c2 d2)

  (*  meet : elem -> elem -> elem  *)
  let meet (c1,c2) (d1,d2) = pair (C1.meet c1 d1, C2.meet c2 d2)

  (*  widening : elem -> elem -> elem  *)
  let widening (c1,c2) (d1,d2) = pair (C1.widening c1 d1, C2.widening c2 d2)


  (** {3 Pretty printing routines } *)

  (*  fpprint : Format.formatter -> elem -> unit  *)
  let fpprint fmt (c1,c2) =
    let s1 = C1.to_string c1 in
    let s2 = C2.to_string c2 in
    Format.fprintf fmt "%s(%s, %s)" Str.prefix s1 s2  

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

module MakeExt(C1 : EXTLATTICE)(C2 : EXTLATTICE)(Str : sig val prefix : string end) =
struct
  include Make(C1)(C2)(Str)
    
  module EqMap = Map.Make(struct type t = C1.equiv_class
				 let compare = C1.compare end)
  type equiv_class = C1.equiv_class * C2.equiv_class
  type partition = C1.partition * (C2.partition EqMap.t)

  (*  compare : equiv_class -> equiv_class -> int  *)
  let compare (eq1,eq2) (eq1',eq2') =
    let cmp1 = C1.compare eq1 eq1' in
    if cmp1 = 0 then C2.compare eq2 eq2' else cmp1 

  (*  repr : equiv_class -> elem  *)
  let repr (eqcl1,eqcl2) = pair (C1.repr eqcl1, C2.repr eqcl2)
    (* the atoms of the reduced product are (a1,a2) *)
    
  (*  project : equiv_class -> elem  *)
  let project (eqcl1,eqcl2) = pair (C1.project eqcl1, C2.project eqcl2)

  (*  partition : elem -> partition  *)
  let partition (c,d) = let c1part = C1.partition c in
			let c2part = C2.partition d in
			let c2bg   = C2.partition C2.top in
			(c1part,
			 C1.fold_partition
			   (fun acc eq1 ->
			      if C1.leq (C1.repr eq1) c
			      then EqMap.add eq1 c2part acc
			      else EqMap.add eq1 c2bg acc) EqMap.empty c1part)

  (*  fold_partition : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a  *)
  let fold_partition f acc (_kpart,part) =
    EqMap.fold (fun eq1 part2 acc' ->
                  C2.fold_partition (fun acc'' eq2 -> f acc'' (eq1,eq2)) acc' part2) part acc

  (*  overlay_partitions : partition -> partition -> partition  *)
  let overlay_partitions (kp,p) (kp',p') =
    let keypart = C1.overlay_partitions kp kp' in
    let keylist = List.rev (C1.fold_partition (fun acc k -> k::acc) [] keypart) in
    let map1 = Hashtbl.create 42 in
    let map2 = Hashtbl.create 42 in
    let _ = EqMap.fold
              (fun eq1 part2 rest ->
		let eq1s',rest' = List.partition
 		                    (fun eq1' -> C1.leq (C1.repr eq1') (C1.project eq1)) rest in
		let () = List.iter (fun eq1' -> Hashtbl.add map1 eq1' part2) eq1s' in
		rest') p keylist in
    let _ = EqMap.fold
              (fun eq1 part2 rest ->
		let eq1s',rest' = List.partition
 		                    (fun eq1' -> C1.leq (C1.repr eq1') (C1.project eq1)) rest in
		let () = List.iter (fun eq1' -> Hashtbl.add map2 eq1' part2) eq1s' in
		rest') p' keylist in
    let map = List.fold_left
      (fun acc eq -> let ol = C2.overlay_partitions
		                (Hashtbl.find map1 eq) (Hashtbl.find map2 eq) in
		     EqMap.add eq ol acc) EqMap.empty keylist in
    (keypart,map)

(* The simpler partition *)
(*
  type equiv_class = C1.equiv_class * C2.equiv_class
  type partition = C1.partition * C2.partition

  (*  repr : equiv_class -> elem  *)
  let repr (eqcl1,eqcl2) = pair (C1.repr eqcl1, C2.repr eqcl2)
    (* the atoms of the reduced product are (a1,a2) *)
    
  (*  project : equiv_class -> elem  *)
  let project (eqcl1,eqcl2) = pair (C1.project eqcl1, C2.project eqcl2)
      
  (*  partition : elem -> partition  *)
  let partition (c,d) = (C1.partition c, C2.partition d)
    
  (*  fold_partition : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a  *)
  let fold_partition f acc (part1,part2) =
    C1.fold_partition (fun acc' eq1 ->
      C2.fold_partition (fun acc'' eq2 -> f acc'' (eq1,eq2)) acc' part2) acc part1

  (*  overlay_partitions : partition -> partition -> partition  *)
  let overlay_partitions (p1,p2) (p1',p2') =
    (C1.overlay_partitions p1 p1', C2.overlay_partitions p2 p2')
*)
end
