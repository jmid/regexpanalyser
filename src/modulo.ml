(** Abstract modulo datatype and operations *)

module Make(N : sig val n : int end) =
struct

  type elem =
    | Bot
    | Rem of int (* a  where  a < n *)
    | Top

  (** A smart constructor to normalize remainder representatives *)
  (*  rem : int -> elem  *)
  let rem a = if a<N.n then Rem a else Rem (a mod N.n)

  (*  const : int -> elem  *)
  let const c = rem c

  (*  eq : elem -> elem -> bool  *)
  let eq (c:elem) c' = c = c'

  (*  leq : elem -> elem -> bool  *)
  let leq c c' = match c,c' with
    | _,Top -> true
    | Top,_ -> false
    | Bot,_ -> true
    | _,Bot -> false
    | Rem a, Rem a' -> (abs (a - a')) mod N.n = 0
    
  (*  join : elem -> elem -> elem  *)
  let join c c' = match c,c' with
    | _,Top -> Top
    | Top,_ -> Top
    | Bot,_ -> c'
    | _,Bot -> c
    | Rem a, Rem a' -> if (abs (a - a')) mod N.n = 0 then rem a else Top

  (*  meet : elem -> elem -> elem  *)
  let meet c c' = match c,c' with
    | _,Top -> c
    | Top,_ -> c'
    | Bot,_ -> Bot
    | _,Bot -> Bot
    | Rem a, Rem a' -> if (abs (a - a')) mod N.n = 0 then c else Bot

  (*  bot : elem  *)
  let bot = Bot

  (*  is_bot : elem -> bool *)
  let is_bot e = (e = Bot)

  (*  top : elem  *)
  let top = Top

  (*  widening : elem -> elem -> elem  *)
  let widening = join

  (*  add : elem -> elem -> elem *)
  let add c c' = match c,c' with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Top, _ -> Top
    | _, Top -> Top
    | Rem a, Rem a' -> rem (a + a')

  (*  sub : elem -> elem -> elem *)
  let sub c c' = match c,c' with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Top, _ -> Top
    | _, Top -> Top
    | Rem a, Rem a' -> rem (a - a')

  (*  mult : elem -> elem -> elem *)
  let mult c c' = match c,c' with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Top, _ -> Top
    | _, Top -> Top
    | Rem a, Rem a' -> rem (a * a')

  type equiv_class = elem
  type partition = elem list

  (*  compare : equiv_class -> equiv_class -> int *)
  let compare e e' = match e,e' with
    | Rem i, Rem i' -> i - i'
    | _, _ -> failwith "Modulo.compare applied to non-atom equivalence classes"
      
  (*  partition : elem -> partition *)
  let partition c = []

  (*  repr : equiv_class -> elem  *)
  let repr m = m

  (*  project : equiv_class -> elem  *)
  let project m = m
    
  (*  fold_partition : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a *)
  let fold_partition f acc ms =
    let rec make n = if n = N.n then [] else n::(make (n+1)) in
    List.fold_left (fun a m -> f a (rem m)) acc (make 0)
  
  (*  overlay_partitions : partition -> partition -> partition  *)
  let overlay_partitions cs cs' = []


(** {3 Pretty printing routines } *)

  (*  to_string : elem -> unit  *)
  let to_string c = match c with
    | Bot   -> "Bot"
    | Rem i -> "Mod " ^ (string_of_int i)
    | Top   -> "Top"

  (*  fpprint : formatter -> elem -> unit  *)
  let fpprint fmt c = Format.fprintf fmt "%s" (to_string c)

  (*  pprint : elem -> unit  *)
  let pprint c = Format.printf "%s" (to_string c)

end
