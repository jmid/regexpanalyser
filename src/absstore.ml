module type LATTICE =
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
end

module Make (L : LATTICE) =
struct
    module SMap = Map.Make(String)

    type 'a t =
      | Bot
      | Nonbot of 'a SMap.t
      | Exttop of 'a SMap.t (* top store, "downgraded" at selected entries *)
	  
    let empty = Nonbot SMap.empty

    let lookup e x = match e with
      | Bot -> L.bot
      | Nonbot e -> (try SMap.find x e
                     with Not_found -> L.bot)
      | Exttop e -> (try SMap.find x e
                     with Not_found -> L.top)
		      
    let extend e x v = match e with
      | Bot -> Bot
      | Nonbot m ->
	if L.leq v L.bot then Bot else Nonbot (SMap.add x v m)
      | Exttop m ->
	if L.leq v L.bot then Bot else (* makes extend strict *)
	  if L.leq L.top v
	  then
	    if SMap.mem x m
	    then Exttop (SMap.remove x m)
	    else e
	  else Exttop (SMap.add x v m)

    type elem = L.elem t (*L.elem SMap.t*)

    let bot = Bot
    let top = Exttop SMap.empty

    (*  leq : elem -> elem -> bool  *)
    let leq m m' = match m,m' with
      | Bot,_ -> true
      | _,Bot -> false
      | Nonbot m, _ -> SMap.for_all (fun v e -> L.leq e (lookup m' v)) m
      | Exttop sm, Exttop sm' -> (SMap.for_all (fun v e -> L.leq e (lookup m' v)) sm)
	                      && (SMap.for_all (fun v e -> L.leq (lookup m v) e) sm')
      | Exttop m, _  -> false
	
    (*  join : elem -> elem -> elem  *)
    let join m m' = match m,m' with
      | Bot,_ -> m'
      | _,Bot -> m
      | Nonbot m,Nonbot m' ->
	Nonbot (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> e
			      |   None, Some _  -> e'
			      | Some l, Some l' -> Some (L.join l l')) m m')
      | Nonbot m,Exttop m' ->
	Exttop (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> None
			      |   None, Some _  -> e'
			      | Some l, Some l' -> Some (L.join l l')) m m')
      | Exttop m,Nonbot m' ->
	Exttop (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> e
			      |   None, Some _  -> None
			      | Some l, Some l' -> Some (L.join l l')) m m')
      | Exttop m,Exttop m' ->
	Exttop (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> None
			      |   None, Some _  -> None
			      | Some l, Some l' -> Some (L.join l l')) m m')
	
    (*  meet : elem -> elem -> elem  *)
    let meet m m' = match m,m' with
      | Bot,_ -> m
      | _,Bot -> m'
      | Nonbot m,Nonbot m' ->
	Nonbot (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> None
			      |   None, Some _  -> None
			      | Some l, Some l' -> Some (L.meet l l')) m m')
      | Nonbot m,Exttop m' ->
	Nonbot (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> e
			      |   None, Some _  -> None
			      | Some l, Some l' -> Some (L.meet l l')) m m')
      | Exttop m,Nonbot m' ->
	Nonbot (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> None
			      |   None, Some _  -> e'
			      | Some l, Some l' -> Some (L.meet l l')) m m')
      | Exttop m,Exttop m' ->
	Exttop (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> e
			      |   None, Some _  -> e'
			      | Some l, Some l' -> Some (L.meet l l')) m m')

    (*  widening : elem -> elem -> elem  *)
    let widening m m' = match m,m' with
      | Bot,_ -> m'
      | _,Bot -> m
      | Nonbot m,Nonbot m' ->
	Nonbot (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> e
			      |   None, Some _  -> e'
			      | Some l, Some l' -> Some (L.widening l l')) m m')
      | Nonbot m,Exttop m' ->
	Exttop (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> None
			      |   None, Some _  -> e'
			      | Some l, Some l' -> Some (L.widening l l')) m m')
      | Exttop m,Nonbot m' ->
	Exttop (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> e
			      |   None, Some _  -> None
			      | Some l, Some l' -> Some (L.widening l l')) m m')
      | Exttop m,Exttop m' ->
	Exttop (SMap.merge (fun v e e' -> match (e,e') with
	                      |   None, None    -> None
			      | Some _, None    -> None
			      |   None, Some _  -> None
			      | Some l, Some l' -> Some (L.widening l l')) m m')
	  
    (*  eq : elem -> elem -> bool  *)
    let eq m m' = leq m m' && leq m' m

    (*  fpprint :  Format.formatter -> elem -> unit  *)
    let fpprint fmt m = match m with
      | Bot ->
	begin
	  Format.fprintf fmt "Bot";
	end
      | Nonbot m ->
	begin
	  Format.fprintf fmt "[";
	  ignore(SMap.fold
		   (fun v e sep ->
		     begin
		       Format.fprintf fmt "%s%s -> " sep v;
		       L.fpprint fmt e;
		       "; "
 	 	     end) m "");
	  Format.fprintf fmt "]";
	end
      | Exttop m ->
	begin
	  Format.fprintf fmt "Top[";
	  ignore(SMap.fold
		   (fun v e sep ->
		     begin
		       Format.fprintf fmt "%s%s -> " sep v;
		       L.fpprint fmt e;
		       "; "
 	 	     end) m "");
	  Format.fprintf fmt "]";
	end

    (*  to_string : elem -> string  *)
    let to_string m =
      begin
	fpprint Format.str_formatter m;
	Format.flush_str_formatter ();
      end

    (*  pprint : elem -> unit  *)
    let pprint = fpprint Format.std_formatter
end
