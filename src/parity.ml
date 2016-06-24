(** Abstract parity datatype and operations *)

type elem =
  | Top
  | Even
  | Odd
  | Bot

(*  eq : elem -> elem -> bool  *)
let eq (p:elem) p' = p = p'

(*  leq : elem -> elem -> bool  *)
let leq a b = match a,b with
  | _, Top -> true
  | Bot, _ -> true
  | _, _   -> a = b
  
(*  join : elem -> elem -> elem  *)
let join a b = match a,b with
  | _, Bot -> a
  | Bot, _ -> b
  | _, Top -> Top
  | Top, _ -> Top
  | _, _   -> if a = b then a else Top

(*  meet : elem -> elem -> elem  *)
let meet a b = match a,b with
  | _, Bot -> Bot
  | Bot, _ -> Bot
  | _, Top -> a
  | Top, _ -> b
  | _, _   -> if a = b then a else Bot
	
(*  const : int -> elem  *)
let const c = if c mod 2 = 0 then Even else Odd

(*  bot : elem  *)
let bot = Bot

(*  is_bot : elem -> bool  *)
let is_bot e = (e = Bot)

(*  top : elem  *)
let top = Top

(*  widening : elem -> elem -> elem  *)
let widening = join

(*  add : elem -> elem -> elem *)
let add v1 v2 = match v1,v2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Top, _ -> Top
    | _, Top -> Top
    | _, _   -> if v1=v2 then Even else Odd

(*  sub : elem -> elem -> elem *)
let sub = add

(*  mult : elem -> elem -> elem *)
let mult c c' = match c,c' with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | Top, _ -> Top
  | _, Top -> Top
  | Odd, Odd -> Odd
  | Even, _  -> Even
  | _, Even  -> Even


type equiv_class = elem
type partition = equiv_class list

(*  compare : equiv_class -> equiv_class -> int *)
let compare e e' = match e,e' with
  | Even,Even -> 0
  | Odd,Odd -> 0
  | Even,Odd -> -1
  | Odd,Even -> 1
  | _,_ -> failwith "Parity.compare applied to non-atom equivalence classes"
    
(*  partition : elem -> partition  *)
let partition c = []

(*  repr : equiv_class -> elem  *)
let repr p = p
  
(*  project : equiv_class -> elem  *)
let project p = p

(*  fold_partition : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a  *)
let fold_partition f acc equivs =
  let tmp = f acc Even in (* fold order agrees with compare's total order *)
  f tmp Odd

(*  overlay_partitions : partition -> partition -> partition  *)
let overlay_partitions cs cs' = []


(** {3 Pretty printing routines } *)

(*  to_string : elem -> unit  *)
let to_string c = match c with
  | Bot  -> "\\bot"
  | Even -> "\\even"
  | Odd  -> "\\odd"
  | Top  -> "\\top"

(*  fpprint : formatter -> elem -> unit  *)
let fpprint fmt c = Format.fprintf fmt "%s" (to_string c)

(*  pprint : elem -> unit  *)
let pprint c = Format.printf "%s" (to_string c)
