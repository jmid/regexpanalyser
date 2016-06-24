(** Generic lattice signature *)

module type EXTLATTICE =
sig
  type elem
  val leq       : elem -> elem -> bool
  val join      : elem -> elem -> elem
  val meet      : elem -> elem -> elem
  val bot       : elem
  val top       : elem 
  val widening  : elem -> elem -> elem
  val eq        : elem -> elem -> bool
  val to_string : elem -> string
  val pprint    : elem -> unit
  val fpprint   : Format.formatter -> elem -> unit
  type equiv_class
  type partition
  val compare            : equiv_class -> equiv_class -> int
  val partition          : elem -> partition
  val repr               : equiv_class -> elem
  val project            : equiv_class -> elem
  val fold_partition     : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a
  val overlay_partitions : partition -> partition -> partition
end

type 'a rexp =
  | Empty
  | Eps
  | Letter of 'a
  | Concat of ('a rexp) list (* with minimum two elements *)
  | Kleene of 'a rexp
  | Union of ('a rexp) list  (* sorted, with minimum two elements *)
  | Inter of ('a rexp) list  (* sorted, with minimum two elements *)
  | Compl of 'a rexp

module Make(L : EXTLATTICE) =
  struct
    type elem = L.elem rexp

    (** a total ordering of the datatype, useful for sorting *)
    (*  compare : elem -> elem -> int  *)
    let rec compare r1 r2 =
      match (r1,r2) with
	| Empty, Empty ->  0
	| Empty, _     -> -1
	| _    , Empty ->  1
	| Eps,   Eps   ->  0 
	| Eps,   _     -> -1
	| _  ,   Eps   ->  1
	| Letter a, Letter b -> Pervasives.compare a b (* Or better: factor comparison operator into L *)
	| Letter _, _        -> -1
	| _       , Letter _ ->  1
	| Concat [],      Concat []      ->  0
	| Concat _,       Concat []      ->  1
	| Concat [],      Concat _       -> -1
	| Concat (x::xs), Concat (y::ys) ->
	  let res = compare x y in
	  if res = 0 then compare (Concat xs) (Concat ys) else res
	| Concat _,       _              -> -1
	| _       ,       Concat _       ->  1
	| Kleene r, Kleene r' -> compare r r'
	| Kleene _, _         -> -1
	| _       , Kleene _  ->  1
	| Union [], Union []  ->  0
	| Union _,  Union []  ->  1
	| Union [], Union _   -> -1
	| Union (x::xs), Union (y::ys) ->
	  let res = compare x y in
	  if res = 0 then compare (Union xs) (Union ys) else res
	| Union _,  _         -> -1
	| _,        Union _   ->  1
	| Inter [], Inter []  ->  0
	| Inter _,  Inter []  ->  1
	| Inter [], Inter _   -> -1
	| Inter (x::xs), Inter (y::ys) ->
	  let res = compare x y in
	  if res = 0 then compare (Inter xs) (Inter ys) else res
	| Inter _,  _         -> -1
	| _,        Inter _   ->  1
	| Compl r,  Compl r'  -> compare r' r

    (** Smart constructors, as in Owens-Reppy-Turon:JFP09,p.180-181 *)

    (*  letter : L.elem -> elem  *)
    let letter l = if L.leq l L.bot then Empty else Letter l

    (*  inter : elem * elem -> elem  *)
    let rec inter (r,t) =
      if r == t || r = t
      then r                                                          (*  r & r  ~  r  *)
      else match r,t with
	| Inter rs, Inter ts -> Inter (List.sort_uniq compare (rs@ts))
	| Empty,    _        -> Empty                                 (*  Ø & r  ~  Ø  *)
	| _,        Empty    -> Empty                                 (*  r & Ø  ~  Ø  *)
	| Inter rs, _        -> Inter (List.sort_uniq compare (t::rs))
	| _,        Inter ts -> Inter (List.sort_uniq compare (r::ts))
	| _,        _        -> (match List.sort_uniq compare [r;t] with
  	                          | [r] -> r
				  | rs  -> Inter rs)

    (*  union : elem * elem -> elem  *)
    let rec union (r,t) =
      if r == t || r = t
      then r                                                          (*  r + r  ~  r  *)
      else match r,t with
	| Union rs, Union ts -> Union (List.sort_uniq compare (rs@ts))
	| Empty,    _        -> t                                     (*  Ø + r  ~  r  *)
	| _,       Empty     -> r                                     (*  r + Ø  ~  r  *)
	| Union rs, _        -> Union (List.sort_uniq compare (t::rs))
	| _,        Union ts -> Union (List.sort_uniq compare (r::ts))
	| _,        _        -> (match List.sort_uniq compare [r;t] with
          	                  | [r] -> r
				  | rs  -> Union rs)

    (*  concat : elem * elem -> elem  *)
    let rec concat (r,t) = match r,t with
      | Concat rs, Concat ts -> Concat (rs@ts)
      | Empty,     _         -> Empty                          (*   Ø . r  ~  Ø      *)
      | _,         Empty     -> Empty                          (*   r . Ø  ~  Ø      *)
      | Eps,       _         -> t                              (*   e . r  ~  r      *)
      | _,         Eps       -> r                              (*   r . e  ~  r      *)
      | Concat rs, _         -> Concat (rs@[t])
      | _,         Concat ts -> Concat (r::ts)
      | _,         _         -> Concat [r;t]

    (*  kleene : elem -> elem  *)
    let rec kleene r = match r with
      | Kleene r' -> Kleene r'               (*   [r*]*  ~  r*     *)
      | Eps       -> Eps                     (*      e*  ~  e      *)
      | Empty     -> Eps                     (*      Ø*  ~  e      *)
      | _         -> Kleene r

    (*  compl : elem -> elem  *)
    let rec compl r = match r with
      | Compl r'  -> r'                      (* C(C(r))  ~  r      *)
      | Empty     -> kleene (Letter L.top)   (*     C Ø  ~  top    *)
      | _         ->
	if r = Kleene (Letter L.top)
	   || r == Kleene (Letter L.top)     (*  C top*  ~  Ø      *)
	then Empty
	else Compl r


    (**  Lattice operations  **)

    let bot = Empty
    let top = kleene (Letter L.top)
    let join r1 r2 = union (r1,r2)
    let meet r1 r2 = inter (r1,r2)

    (*  nullable : L.elem rexp -> bool  *)
    let rec nullable r = match r with
      | Empty     -> false
      | Eps       -> true
      | Letter _  -> false
      | Kleene r  -> true
      | Concat rs -> List.for_all nullable rs
      | Union rs  -> List.exists nullable rs
      | Inter rs  -> List.for_all nullable rs
      | Compl r   -> not (nullable r)
	
    (*  rev : L.elem rexp -> L.elem rexp  *)
    let rec rev r = match r with
      | Empty          -> r
      | Eps            -> r
      | Letter _       -> r
      | Concat []      -> failwith "internal, empty concatenation in rev"
      | Concat [r]     -> failwith "internal, singleton concatenation in rev"
      | Concat [r;s]   -> concat (rev s,rev r)
      | Concat (r::rs) -> List.fold_left (fun acc r -> concat (rev r,acc)) (rev r) rs
      | Kleene r       -> kleene (rev r)
      | Union []       -> failwith "internal, empty union in rev"
      | Union [r]      -> failwith "internal, singleton union in rev"
      | Union [r;s]    -> union (rev r,rev s)
      | Union (r::rs)  -> List.fold_left (fun acc r -> union (rev r,acc)) (rev r) rs
      | Inter []       -> failwith "internal, empty intersection in rev"
      | Inter [r]      -> failwith "internal, singleton intersection in rev"
      | Inter [r;s]    -> inter (rev r,rev s)
      | Inter (r::rs)  -> List.fold_left (fun acc r -> inter (rev r,acc)) (rev r) rs
      | Compl r        -> compl (rev r)

    (*  d : L.elem -> L.elem rexp -> L.elem rexp  *)
    let rec d a r = match r with
      | Eps            -> Empty
      | Letter b       -> if L.leq a b then Eps else Empty
      | Empty          -> Empty
      | Concat []      -> failwith "internal, empty concatenation in d"
      | Concat [r]     -> d a r
      | Concat [r;s]   -> if nullable r then union (concat (d a r, s), d a s)
                          else concat (d a r, s)
      | Concat (r::rs) -> if nullable r then union (concat (d a r, Concat rs), d a (Concat rs))
                          else concat (d a r, Concat rs)
      | Kleene r'      -> concat (d a r', r)
      | Union []       -> failwith "internal, empty union in d"
      | Union (r::rs)  -> List.fold_right (fun r acc -> union (d a r, acc)) rs (d a r)
      | Inter []       -> failwith "internal, empty intersection in d"
      | Inter (r::rs)  -> List.fold_right (fun r acc -> inter (d a r, acc)) rs (d a r)
      | Compl r'       -> compl (d a r')

    (*  rev_d : L.elem -> L.elem rexp -> L.elem rexp  *)
    let rec rev_d a r = rev (d a (rev r))

    (*  range : L.elem rexp -> L.atom_equivs  *)
    let rec range r = match r with
      | Empty          -> L.partition L.top
      | Eps            -> L.partition L.top
      | Letter a       -> L.partition a
      | Concat []      -> L.partition L.top
      | Concat (r::rs) -> if nullable r
                          then L.overlay_partitions (range r) (range (Concat rs))
                          else range r
      | Kleene r'      -> range r'
      | Union []       -> failwith "internal, empty union in range"
      | Union (r::rs)  -> List.fold_left
	                    (fun acc r -> L.overlay_partitions (range r) acc) (range r) rs
      | Inter []       -> failwith "internal, empty intersection in range"
      | Inter (r::rs)  -> List.fold_left
	                    (fun acc r -> L.overlay_partitions (range r) acc) (range r) rs
      | Compl r'       -> range r'


    (** Note: modulo the ACI axioms
         (r + s) + t  ~  r + (s + t)  (Associativity of +)
               r + s  ~  s + r        (Commutativity of +)
               r + r  ~  r            (Idempotency of +)
	 which the smart constructors include, there are only finitely many derivatives  *)

    exception False
    (*  leq : L.elem rexp -> L.elem rexp -> bool *)
    let leq r s =
      let cache = Hashtbl.create 50 in
      let rec memoleq r s =
	try Hashtbl.find cache (r,s)
	with Not_found ->
          if r == s || r = s (* address or structural equality *)
          then (* a little optimization of reflexive queries *) 
            Hashtbl.add cache (r,s) () (* add elem to model simulation / gfp *)
          else
            match nullable r, nullable s with
              | true, false -> raise False
              | true, true
              | false, _ ->
		let partition = L.overlay_partitions (range r) (range s) in
                begin
                  Hashtbl.add cache (r,s) (); (* add elem to model simulation / gfp *)
                  L.fold_partition
		    (fun () eqclass ->
 		       let a = L.repr eqclass in
		       let r' = d a r in (* a is a repr. of equiv.class *)
                       let s' = d a s in
                       memoleq r' s')
		    () partition
                end
      in try (memoleq r s; true) with False -> false

    (*  eq : L.elem rexp -> L.elem rexp -> bool *)
    let eq r r' = leq r r' && leq r' r

(* The initial widening operator, from Logozzo:AMAST04 *)
    (*  widening : L.elem rexp -> L.elem rexp -> L.elem rexp  *)
    let rec widening r r' = match r,r' with
      (* first column, Logozzo, AMAST04, Fig.3, p.8 *)
      | Kleene (Letter a), _ when (L.leq L.top a) -> top
      | _, Kleene (Letter a) when (L.leq L.top a) -> top
      | Letter a, Letter b       -> letter (L.widening a b)
      | Union [],      Letter _  -> failwith "internal, empty union in widening"
      | Union (r::rs), Letter _  -> List.fold_right (fun r a -> union (widening r r',a)) rs (widening r r')
      | Concat [], Concat _             -> widening Eps r' (* Eps is identity for concatenation *)
      | Concat _,  Concat []            -> widening r Eps  (* Eps is identity for concatenation *)
      | Concat [r],Concat [r']          -> widening r r'
      | Concat (r::rs),Concat (r'::rs') -> concat (widening r r', widening (Concat rs) (Concat rs'))
      | Union [], Union _               -> widening Empty r' (* Empty is identity for union *)
      | Union _,  Union []              -> widening r Empty  (* Empty is identity for union *)
      | Union [r],Union [r']            -> widening r r'
      | Union (r::rs),Union (r'::rs')   -> union (widening r r', widening (Union rs) (Union rs'))
      (* widening for intersection *)
      | Inter [],      Letter _  -> failwith "internal, empty intersection in widening"
      | Inter [r],     Letter _  -> widening r r'
      | Inter (r::rs), Letter _  -> inter (widening r r', widening (Inter rs) r')
      | Inter [], Inter _               -> widening top r' (* top is identity for intersection *)
      | Inter _,  Inter []              -> widening r top  (* top is identity for intersection *)
      | Inter [r],Inter [r']            -> widening r r'
      | Inter (r::rs),Inter (r'::rs')   -> inter (widening r r', widening (Inter rs) (Inter rs'))
      (* Added the following two since Logozzo excludes Empty and instead represents it as L.bot *)
      | _, Empty -> r
      | Empty, _ -> r'
      (* New rules for Eps, since under Logozzo's concretization Eps means emptyset, hence increasing *)
      | _, Eps -> kleene r  (* instead we generalize to Kleene star *)
      | Eps, _ -> kleene r'
      (* Merge iteration (on right) into Kleene star -- useful for generalizing history *)
      | Kleene r1, Concat (Kleene r2::r2s) when leq r2 r1  
	  -> let rest = (match r2s with
 	            | []    -> r2 (* failwith "internal, singleton concat in widening, case 1"*)
		    | [r2'] -> r2'
		    | r2s'  -> Concat r2s') in
	      kleene (widening r1 rest)
      (*  r1^*  \/  r2 + r2'  =  r1^*  *)
      | Kleene r1, Union rs when (List.for_all (fun r2 -> leq r2 r) rs) -> r
      | Kleene r1, Union (r2::rs)
        when (List.for_all (function Concat (r2'::rest) -> eq r2' r | _ -> false) (r2::rs)) ->
	  let concatmapper r = (match r with
	    | Concat []          -> failwith "internal, empty concat in widening"
	    | Concat [r2']       -> failwith "internal, singleton concat in widening"
	    | Concat [r2';r2'']  -> r2''
	    | Concat (r2'::rest) -> (Concat rest)
	    | _                  -> failwith "non-Concat-node encountered in all Concat list") in
	  let restunion =
	    List.fold_right (fun r acc -> union (concatmapper r,acc)) rs (concatmapper r2) in
	  kleene (widening r1 restunion)

   (* second column, Logozzo, AMAST04, Fig.3, p.8 *)
   (* | _, Eps -> r
      | Eps, _ -> r' *)
   (* | Concat (r::rs), Letter _ -> concat (widening r r', Concat rs) *)
                                      (* This is not increasing in second parameter *)
      | Kleene r, Letter _       -> kleene (widening r r')
      | Kleene r1, Kleene r2     -> kleene (widening r1 r2)
      | _, _ -> top


    type color = Color1 | Color2 | Color3
    type unknown = Unknown of int

    (*  color : L.elem rexp -> L.elem rexp -> color  *)
    let color r' r =
      if r = r' then Color1  (* This tests ACI equivalence, not semantic equality *)
      else if nullable r then Color2
      else Color3

    (*  col_discrim : L.elem rexp -> (L.elem rexp) list ^3 -> (L.elem rexp) list ^3  *)
    let rec col_discrim root rss = (match rss with
	| [] -> [],[],[]
	| rs::rss ->
	  let rec color_walk rs = (match rs with
	    | [] -> col_discrim root rss
	    | hd::rs ->
	      let c1,c2,c3 = color_walk rs in
	      let (_,r) = hd in
	      (match color root r with (* This tests ACI equivalence, not sem.equiv. *)
		| Color1 -> (hd::c1,c2,c3)  
		| Color2 -> (c1,hd::c2,c3)
		| Color3 -> (c1,c2,hd::c3))) in
	  color_walk rs)

    (*  map : L.elem rexp Hashtbl -> eqs -> eqs *)
    let rec map seen eqs = match eqs with
      | [] -> []
      | (num,eq,opt)::eqs' ->
	let eqs = map seen eqs' in
	(num,List.map (fun (a,d) -> let num = Hashtbl.find seen d in
				    (letter a,Unknown num)) eq,opt)::eqs

    (* a worklist algorithm for building derivative equations *)
    let rec build wlist seen count eqs = match wlist with
      | [] -> List.rev eqs
      | r::rlist' ->
	if Hashtbl.mem seen r
	then build rlist' seen count eqs
	else
	  (let num = !count in
	   let () = Hashtbl.add seen r num in
	   let () = incr count in
	   let eq = L.fold_partition
	     (fun acc eqclass ->
	       let a = L.repr eqclass in
	       let e = L.project eqclass in
	       let d_a_r = d a r in (e,d_a_r)::acc) [] (range r)
	   in
	   let rlist'' = (List.map snd eq) @ rlist' in
	   let eq = if nullable r then (num,eq,Some Eps) else (num,eq,None) in
	   build rlist'' seen count (eq::eqs))

    (* Resulting representation as array:
       R0 = [| [| r00; r01; r02  ; rb0 |]    ~  R0 = r00 R0 + r01 R1 + r02 R2 + rb0
       R1 =    [| r10; r11; r12  ; rb1 |]    ~  R1 = r10 R0 + r11 R1 + r12 R2 + rb1
       R2 =    [| r20; r21; r22  ; rb2 |] |] ~  R2 = r20 R0 + r21 R1 + r22 R2 + rb2 *)
	    
    (* Input representation as lists:
       [ (0, [(r00,Unknown 0); (r01,Unknown 1); (r02,Unknown 2)], Some rb0);
         (1, [(r10,Unknown 0); (r11,Unknown 1); (r12,Unknown 2)], Some rb1);
         (2, [(r20,Unknown 0); (r21,Unknown 1); (r22,Unknown 2)], Some rb2) ]

       + an equivalence equation representation:   [ [0]; [1;2]; ... ] *)

    (*  elim_error_states : int -> "eq list" -> "eq list" *)
    let elim_error_states dim eqs =
      let visited = Array.make dim false in
      let eq_arr = Array.make dim ([],None) in
      let rev_graph = Array.make dim [] in
      let () = List.iter (fun (eqnum,rhs,opt) ->
	                    begin
	                      eq_arr.(eqnum) <- (rhs,opt);
			      List.iter (fun (a,Unknown j) -> rev_graph.(j) <- eqnum::rev_graph.(j)) rhs;
                            end) eqs in
      let rec dfs i =
	if visited.(i)
	then ()
	else
	  let outgoing = rev_graph.(i) in
	  begin
	    visited.(i) <- true;
	    List.iter (fun j -> (dfs j)) outgoing;
	  end in
      begin
	Array.iteri (fun i (rhs,opt) -> (* start reachability dfs from acceptance roots *)
	               if opt<>None && (not visited.(i)) then dfs i else ()) eq_arr;
	ignore (dfs 0); (* mark states as non-empty in a dfs traversal *)
	Array.iteri (fun i (rhs,opt) -> (* run over array linearly, eliminating error states *)
	               if visited.(i)
		       then
			 let rhs' = List.fold_right
			              (fun (a,Unknown j) acc ->
					 if visited.(j)
					 then (a,Unknown j)::acc
					 else acc) rhs [] in
			 eq_arr.(i) <- (rhs',opt)
		       else eq_arr.(i) <- ([],None)) eq_arr;
        (* return as list representation again *)
	let _,eqs =
	  Array.fold_right
	    (fun (rhs,opt) (eqnum,eqs) -> (eqnum-1,(eqnum,rhs,opt)::eqs)) eq_arr (dim-1,[]) in
	eqs
      end

    (*  elim_equivs : int -> "eq list" -> int list list -> int * L.elem rexp array array *)
    let elim_equivs dim eqs equivs =
      let repr   = Array.init dim (fun i -> i) in (* [| 0; 1; ... ; dim |] *)
      let rename = Array.init dim (fun i -> i) in (* [| 0; 1; ... ; dim |] *)
      let rec fill equivs = match equivs with
	| [] -> ()
	| eclass::equivs ->
	  (match eclass with
	    | [] -> fill equivs
	    | i::is -> let root = List.fold_left min i is in
		       begin
			 repr.(i) <- root;
			 List.iter (fun j -> repr.(j) <- root) is;
			 fill equivs
		       end) in
      let () = fill equivs in (* Step 0: calculate repr name/index for each class *)
      let res =    (* Step 1: res renames eqs according to equivalences [R1=R3; R4=R5; ...] *)
	List.map
	  (fun (eqnum,rhs,opt) ->
             (repr.(eqnum), List.map (fun (r,Unknown n) -> (r,Unknown (repr.(n)))) rhs, opt)) eqs in
      let newdim = (* Step 2: rename calculates new defragmented indices for R1,...,Rdim-1 *)
	List.fold_left
	  (fun next (eqnum,_,_) -> let rep = repr.(eqnum) in
				   if rep = eqnum (* repr *)
	                           then (rename.(eqnum) <- next; next+1)
	                           else (rename.(eqnum) <- rename.(rep); next)) 0 eqs in
      let res' = (* rename res according to new index *)
	List.map (fun (eqnum,rhs,opt) ->
	            (rename.(eqnum),
		     List.map (fun (r,Unknown n) -> (r,Unknown (rename.(n)))) rhs,
		     match opt with None -> Empty | Some eps -> eps)) res in
      let a  = Array.make_matrix newdim (newdim+1) Empty in
      let () =
	List.iter (* run over equation lists and fill in array representation *)
	  (fun (eqnum,rhs,opt) ->
	    begin
	      List.iter (fun (r,Unknown n) -> a.(eqnum).(n) <- union (a.(eqnum).(n), r)) rhs;
	      a.(eqnum).(newdim) <- union (a.(eqnum).(newdim), opt)
	    end) res'
      in newdim,a (* repr,res,rename,newdim,res',a *)

    (* solve 3 eqs: 
       R2 = r20 R0 + r21 R1 + r22 R2 + rb2
          = r22 R2 + (r20 R0 + r21 R1 + rb2)
       R2 = r22^* (r20 R0 + r21 R1 + rb2)
          = r22^* r20 R0 + r22^* r21 R1 + r22^* rb2
          =        s0 R0 +        s1 R1 + ØR2 + sb2

       hence by substitution:
       R0 = r00 R0 + r01 R1 + r02 R2 + rb0
          = r00 R0 + r01 R1 + r02 (r22^* r20 R0 + r22^* r21 R1 + r22^* rb2) + rb0
          = r00 R0 + r01 R1 + r02 r22^* r20 R0 + r02 r22^* r21 R1 + r02 r22^* rb2 + rb0
          = (r00 + r02 r22^* r20) R0 + (r01 + r02 r22^* r21) R1 + (rb0 + r02 r22^* rb2)
                       ^^^^^^^^^                  ^^^^^^^^^                  ^^^^^^^^^
       R1 = r10 R0 + r11 R1 + r12 R2 + rb1
          = r10 R0 + r11 R1 + r12 (r22^* r20 R0 + r22^* r21 R1 + r22^* rb2) + rb1
          = r10 R0 + r11 R1 + r12 r22^* r20 R0 + r12 r22^* r21 R1 + r12 r22^* rb2 + rb1
          = (r10 + r12 r22^* r20) R0 + (r11 + r12 r22^* r21) R1 + (rb1 + r12 r22^* rb2)
                       ^^^^^^^^^                  ^^^^^^^^^                  ^^^^^^^^^    *)
    (* i is the target equation for elimination
       tgt is the target being eliminated
       j is an entry/index into i's sum .(i).(j) *) 
    (*  solve_eqs : int -> L.elem rexp array array -> rexp *)
    let solve_eqs dim eqs =
      let sollast = ref Empty in (* no solution *)
      for tgt = dim-1 downto 0 do
	let sol = if eqs.(tgt).(tgt) = Empty
	          then eqs.(tgt)
	          else
	            let a = Array.map (fun r -> concat (kleene (eqs.(tgt).(tgt)),r)) eqs.(tgt) in
		    let () = eqs.(tgt).(tgt) <- Empty in
		    a in
	begin
	  for i = 0 to tgt-1 do
	    for j = 0 to tgt-1 do
	      eqs.(i).(j) <- union (eqs.(i).(j), concat (eqs.(i).(tgt), sol.(j)))
	    done;
	    eqs.(i).(dim) <- union (eqs.(i).(dim), concat (eqs.(i).(tgt), sol.(dim)))
	  done;
	  sollast := sol.(dim)
	end
      done;
      !sollast
(*
module R = Regexpdom.Make(Sign);;
let a = [| [| Regexpdom.Empty; R.letter (Sign.const 1); Regexpdom.Empty |];
           [| R.letter (Sign.const (-1)); Regexpdom.Empty; Regexpdom.Eps |]; |];;
R.solve_eqs 2 a;;
let b = [| [| Regexpdom.Empty; R.letter (Sign.const (-1)); Regexpdom.Empty; Regexpdom.Eps |];
           [| Regexpdom.Empty; Regexpdom.Empty; R.letter (Sign.const 0); Regexpdom.Empty  |];
           [| R.letter (Sign.const 1); Regexpdom.Empty; Regexpdom.Empty; Regexpdom.Empty; |]; |];;
R.solve_eqs 3 b;;
a;;
*)	
    (*  determinize : L.elem rexp -> L.elem rexp  *)
    let determinize r =
      let seen = Hashtbl.create 43 in
      let count = ref 0 in  
      let eqs = build [r] seen count [] in
      let elems = Hashtbl.fold (fun r num elems -> (num,r)::elems) seen [] in
      let eqs = map seen eqs in
      let eqs = elim_error_states !count eqs in (* cleanup *)
      let equivs = List.map (fun (num,_) -> [num]) elems in (* each elem in its own equi.class *)
      let newdim,a = elim_equivs !count eqs equivs in
      solve_eqs newdim a
	
    (*  widening0 : L.elem rexp -> L.elem rexp -> L.elem rexp  *)
    let widening0 r r' =
      let seen = Hashtbl.create 43 in
      let count = ref 0 in  
      let sum = union (r,r') in
      let eqs = build [sum] seen count [] in
      let elems = Hashtbl.fold (fun r num elems -> (num,r)::elems) seen [] in
      let (c1,c2,c3) = col_discrim sum [elems] in
      let eqs = map seen eqs in
      let eqs = elim_error_states !count eqs in (* cleanup *)
      let equivs = [List.map fst c1; List.map fst c2; List.map fst c3] in
  (*    let () = Printf.printf "Count is %i\n" (!count) in *)
      let newdim,a = elim_equivs !count eqs equivs in
      solve_eqs newdim a

    (*  discrim1 : atom list -> (L.elem rexp) list list -> (L.elem rexp) list list  *)
    let rec discrim1 atoms root rss =
      let rec discrim a rss = (match rss with
	  | []    -> []
	  | rs::rss ->
	    let rec walk rs = (match rs with
	      | [] -> [],[],[]
	      | hd::rs -> let c1,c2,c3 = walk rs in
			  let (_,r) = hd in
			  (match color root (d a r) with
			   | Color1 -> (hd::c1,c2,c3)  
			   | Color2 -> (c1,hd::c2,c3)
			   | Color3 -> (c1,c2,hd::c3))) in
	    let rss' = discrim a rss in
	    let c1,c2,c3 = walk rs in
	    let rss' = if c3 = [] then rss' else c3::rss' in
	    let rss' = if c2 = [] then rss' else c2::rss' in
	    let rss' = if c1 = [] then rss' else c1::rss' in(* slight optimization to avoid empties *)
	    rss')
      in L.fold_partition (fun rss eqclass -> discrim (L.repr eqclass) rss) rss atoms

    (*  widening1 : L.elem rexp -> L.elem rexp -> L.elem rexp  *)
    let widening1 r r' =
      let seen = Hashtbl.create 43 in
      let count = ref 0 in  
      let sum = union (r,r') in
      let eqs = build [sum] seen count [] in
      let elems = Hashtbl.fold (fun r num elems -> (num,r)::elems) seen [] in
      let (c1,c2,c3) = col_discrim sum [elems] in
      let equivs = discrim1 (L.partition L.top) sum [c1;c2;c3] in
      let equivs = List.map (List.map fst) equivs in
      let eqs = map seen eqs in
      let eqs = elim_error_states !count eqs in (* cleanup *)
 (*     let () = Printf.printf "Count is %i\n" (!count) in *)
      let newdim,a = elim_equivs !count eqs equivs in
      solve_eqs newdim a

    let widening = widening1 (* widening1 *)

 (*
module R = Regexpdom.Make(Sign);;
R.pprint (R.widening0 Regexpdom.Eps (R.letter (Sign.const (-1))));;
R.pprint (R.widening0 (R.letter (Sign.const 0)) (R.kleene (R.letter (Sign.const 0))));;
R.pprint (R.widening0 Regexpdom.Eps (R.concat (R.letter (Sign.const (-1)),R.letter (Sign.const 0))));;
 *)
    (**  Pretty printing **)

    let latex = false
    let empty   = if latex then "\\emptyset" else "\195\152"
    let epsilon = if latex then "\\epsilon" else "\xce\xb5" (* was "e" *)
    let dot     = if latex then "\\cdot" else "\xc2\xb7"    (* was "." *)
    let neg     = if latex then "\\neg" else "\xc2\xac"

    (*  fpprint : Format.formatter -> L.elem rexp -> unit  *)
    let rec fpprint fmt r =
      
      match r with
      | Empty     -> Format.fprintf fmt "%s" empty
      | Eps       -> Format.fprintf fmt "%s" epsilon
      | Letter a  -> L.fpprint fmt a
      | Concat rs ->
	begin
	  Format.fprintf fmt "(";
	  ignore(List.fold_left (fun acc r ->
	           begin
		     Format.fprintf fmt "%s" acc;
		     fpprint fmt r;
		     " " ^ dot ^ " "
		   end) "" rs);
	  Format.fprintf fmt ")";
	end
      | Kleene r ->
	begin
	  fpprint fmt r;(* invariant: the rec. calls print something fully parenthesized *)
	  Format.fprintf fmt "*";
	end
      | Union rs ->
	begin
	  Format.fprintf fmt "(";
	  ignore(List.fold_left (fun acc r ->
	           begin
		     Format.fprintf fmt "%s" acc;
		     fpprint fmt r;
		     " + "
		   end) "" rs);
	  Format.fprintf fmt ")";
	end
      | Inter rs ->
	begin
	  Format.fprintf fmt "(";
	  ignore(List.fold_left (fun acc r ->
 	           begin
		     Format.fprintf fmt "%s" acc;
		     fpprint fmt r;
		     " & "
		   end) "" rs);
	  Format.fprintf fmt ")";
	end
      | Compl r ->
	begin
	  Format.fprintf fmt "%s" neg;
	  Format.print_flush ();
	  fpprint fmt r;(* invariant: the rec. calls print something fully parenthesized *)
	end

    (*  pprint : L.elem rexp -> unit  *)
    let pprint e =
      begin
	fpprint Format.std_formatter e;
	Format.print_flush ();
      end

    (*  to_string : L.elem rexp -> string  *)
    let rec to_string r = match r with
      | Empty     -> empty
      | Eps       -> epsilon
      | Letter a  -> L.to_string a
      | Concat rs ->
	let _sep,elms =
	  List.fold_left (fun (sep,acc) r -> (" " ^ dot ^ " ", acc ^ sep ^ (to_string r))) ("","") rs in
	"(" ^ elms ^ ")";
      | Kleene r ->
	  (to_string r) (* invariant: the rec. calls print something fully parenthesized *)
	  ^ "*";
      | Union rs ->
	let _sep,elms =
	  List.fold_left (fun (sep,acc) r -> (" + ", acc ^ sep ^ (to_string r))) ("","") rs in
	"(" ^ elms ^ ")";
      | Inter rs ->
	let _sep,elms =
	  List.fold_left (fun (sep,acc) r -> (" & ", acc ^ sep ^ (to_string r))) ("","") rs in
	"(" ^ elms ^ ")";
      | Compl r ->
	  neg ^ (to_string r) (* invariant: the rec. calls print something fully parenthesized *)

    (*  visualize : L.elem rexp -> (int * string) list *)
    let visualize r =
      let cache = Hashtbl.create 50 in
      let edges = ref [] in
      let count = ref 1 in
      (*  memovisualize : L.elem rexp -> (int * string) *)
      let rec memovisualize r =
	try Hashtbl.find cache r
	with Not_found ->
          let rnum  = !count in
	  let rstr  = to_string r in
	  let final = nullable r in
	  let rtriple = (rnum,final,rstr) in
          begin
	    Hashtbl.add cache r rtriple; (* add elem to model simulation / gfp *)
	    incr count;
	    let part = range r in
            L.fold_partition (fun () eqclass -> let a = L.repr eqclass in
						let e = L.project eqclass in
						let r' = d a r in
 			  			let ttriple = (memovisualize r') in
						let lab = L.to_string e in
						edges := (rtriple,lab,ttriple)::!edges) () part;
	    rtriple
	  end
      in
      let _ = memovisualize r in
      (* let fname,ch = Filename.open_temp_file ~temp_dir:"/tmp" "fa" ".dot" in *)
      let fname = "/tmp/fa.dot" in
      let ch = open_out fname in
      begin
	Printf.fprintf ch "digraph fa { rankdir=LR;\n";
	Printf.fprintf ch "  node [style=\"state\"];\n";
	Printf.fprintf ch "  edge [lblstyle=\"auto\"];\n";
	Hashtbl.iter
	  (fun r (n,final,str) ->
	    let style = if n=1 then "state,initial" else "state" in
	    let style = if final then style ^ ",accepting" else style in
	    Printf.fprintf ch "  node [style=\"%s\",color=black,label=\"%s\"] n%i;\n" style str n) cache;
	List.iter
	  (fun ((rn,_,_),lab,(tn,_,_)) -> Printf.fprintf ch "  n%i -> n%i [label=\"%s\"];\n" rn tn lab) !edges;
	Printf.fprintf ch "}\n";
	Printf.printf "Printed result to %s\n" fname;
	close_out ch;
	Sys.command ("dot -Tpng " ^ fname ^ " -o /tmp/fa.png");
      end
  end
