(** Abstract set lattice and operations *)

module Make(N : sig val n : int end) =
struct
  module LabelSet = Set.Make(struct type t = int
				    let compare i i' = i - i' end)

  type elem = LabelSet.t (* 0,...,N.n-1 *)

  let bot = LabelSet.empty
  let top =
    let rec make n = if n = N.n then LabelSet.empty else LabelSet.add n (make (n+1)) in
    (make 0)

  (*  const : int -> elem  *)
  let const i =
    if 0 <= i && i < N.n
    then LabelSet.singleton i
    else failwith "intset.ml: argument to const out of bounds {0...N.n-1}"

  (*  eq : elem -> elem -> bool  *)
  let eq = LabelSet.equal

  (*  leq : elem -> elem -> bool  *)
  let leq = LabelSet.subset

  (*  join : elem -> elem -> elem  *)
  let join = LabelSet.union

  (*  meet : elem -> elem -> elem  *)
  let meet = LabelSet.inter

  (*  widening : elem -> elem -> elem  *)
  let widening = LabelSet.union

  module Partition = Set.Make(struct type t = LabelSet.t
				     let compare = LabelSet.compare end)
  type equiv_class = elem
  type partition = Partition.t

  (*  compare : equiv_class -> equiv_class -> equiv_class  *)
  let compare = LabelSet.compare

  (*  partition : elem -> partition *)
  let partition (c:elem) = (* [] *)
    let rec make n = if n = N.n then [] else n::(make (n+1)) in
    let rest = List.fold_left (fun rest m ->
                                 if LabelSet.mem m c
                                 then rest
				 else LabelSet.add m rest) LabelSet.empty (make 0) in
    let part = Partition.add c Partition.empty in
    if LabelSet.is_empty rest then part else Partition.add rest part

  (*  repr : equiv_class -> elem  *)
  let repr m = LabelSet.singleton (LabelSet.min_elt m) (*m*)
    
  (*  project : equiv_class -> elem  *)
  let project m = m
    
  (*  fold_partition : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a *)
  let fold_partition f acc ms = Partition.fold (fun eq acc' -> f acc' eq) ms acc
  
  (*  overlay_partitions : partition -> partition -> partition  *)
  let overlay_partitions cs cs' = (*[]*)
    let reptbl = Hashtbl.create N.n in
    let () = Partition.iter (fun eq ->
                               let rep = LabelSet.min_elt eq in
			       LabelSet.iter (fun e -> Hashtbl.add reptbl e rep) eq) cs'  in
    Partition.fold
      (fun eq acc ->
	let rest,acc'' =           (* fold over elems, *)
	  LabelSet.fold               (*  refine each eqclass according to each rep of each elem *)
	    (fun elem (rest,acc') ->    (* add each refined eqclass to acc *)
	      let same,rest' =
		LabelSet.partition
		  (fun elem' -> Hashtbl.find reptbl elem = Hashtbl.find reptbl elem') rest in
	      if LabelSet.is_empty same
	      then (rest',acc')
	      else (rest', Partition.add same acc')) eq (eq,acc)
	in acc'') cs Partition.empty

  (** {3 Pretty printing routines } *)

  (*  to_string : elem -> string  *)
  let to_string ts =
    let elems =
      LabelSet.fold (fun t acc -> 
                       if acc = ""
		       then string_of_int t
		       else acc ^ "," ^ (string_of_int t)) ts "" in
    "{" ^ elems ^ "}"

  (*  fpprint : formatter -> elem -> unit  *)
  let fpprint fmt ts =
    Format.fprintf fmt "%s" (to_string ts)

  (*  pprint : elem -> unit  *)
  let pprint ts =
    Format.printf "%s" (to_string ts)
end
