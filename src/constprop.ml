(** Abstract constant propagation datatype and operations *)

type elem =
  | Bot
  | Const of int
  | Top

(*  eq : elem -> elem -> bool  *)
let eq (c:elem) c' = c = c'

(*  leq : elem -> elem -> bool  *)
let leq c c' = match c,c' with
  | Bot,_ -> true
  | _,Bot -> false
  | _,Top -> true
  | Top,_ -> false
  | Const i, Const i' -> i=i'

(*  join : elem -> elem -> elem  *)
let join c c' = match c,c' with
  | Bot,_ -> c'
  | _,Bot -> c
  | Top,_ -> Top
  | _,Top -> Top
  | Const i, Const i' -> if i=i' then c else Top

(*  meet : elem -> elem -> elem  *)
let meet c c' = match c,c' with
  | Bot,_ -> Bot
  | _,Bot -> Bot
  | Top,_ -> c'
  | _,Top -> c
  | Const i, Const i' -> if i=i' then c else Bot

(* const : int -> elem  *)
let const i = Const i

(*  bot : elem  *)
let bot = Bot

(*  is_bot : elem -> bool *)
let is_bot e = (e = Bot)

(*  top : elem  *)
let top = Top

(*  widening : elem -> elem -> elem  *)
let widening = join

(*  iszero : elem -> elem *)
let iszero c = match c with
  | Bot -> Bot
  | Top -> Const 0
  | Const 0 -> c
  | Const _ -> Bot

(*  notzero : elem -> elem *)
let notzero c = match c with
  | Bot -> Bot
  | Top -> Top
  | Const 0 -> Bot
  | Const _ -> c

(*  add : elem -> elem -> elem *)
let add c c' = match c,c' with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | Top, _ -> Top
  | _, Top -> Top
  | Const c, Const c' -> Const (c+c')

(*  sub : elem -> elem -> elem *)
let sub c c' = match c,c' with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | Top, _ -> Top
  | _, Top -> Top
  | Const c, Const c' -> Const (c-c')

(*  mult : elem -> elem -> elem *)
let mult c c' = match c,c' with
  | Bot, _ -> Bot
  | _, Bot -> Bot
  | Const 0, _ -> const 0
  | _, Const 0 -> const 0
  | Top, _ -> Top
  | _, Top -> Top
  | Const c, Const c' -> Const (c*c')

type equiv_class =
  | ConstEqCl of int (* + a rest element *)
  | Bg of int list
type partition = int list

(*  compare : equiv_class -> equiv_class -> int *)
let compare e e' = match e,e' with
  | ConstEqCl i, ConstEqCl i' -> i - i'
  | ConstEqCl _, Bg _ -> -1
  | Bg _, ConstEqCl _ -> 1
  | Bg is, Bg is' ->
    let rec walk is is' = (match is,is' with
      | [], []   -> 0
      | _::_, [] -> 1
      | [], _::_ -> -1
      | i::is,j::js ->
	if i<j then -1 else 
	  if i>j then 1 else walk is js) in walk is is'

(*  partition : elem -> partition *)
let partition c = match c with
  | Bot     -> []
  | Const c -> [c]
  | Top     -> []

(*  repr : equiv_class -> elem  *)
let repr eqcl = match eqcl with
  | ConstEqCl i -> const i
  | Bg []       -> const 0
  | Bg (c::_)   -> const (c-1) (* potential underflow *)

(*  project : equiv_class -> elem  *)
let project eqcl = match eqcl with
  | ConstEqCl i -> Const i
  | Bg _ -> top

(*  fold_partition : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a *)
let fold_partition f acc cs =
  match cs with
    | []         -> f acc (Bg [])
    | c::_ as cs ->
      List.fold_left
	(fun a c -> f a (ConstEqCl c))
	(f acc (Bg cs)) (*first: fold over c's pred. as repr of background*)
	cs

(*  overlay_partitions : partition -> partition -> partition  *)
let overlay_partitions cs0 cs1 =
  let rec merge is js = match is,js with
    | [], _ -> js
    | _, [] -> is
    | i::is',j::js' -> (* linear time merge of sorted int lists *)
      if i < j then i::(merge is' js) else
	if i > j then j::(merge is js') else
	  i::(merge is' js') in
  (merge cs0 cs1)
    

(** {3 Pretty printing routines } *)

(*  to_string : elem -> unit  *)
let to_string c = match c with
  | Bot     -> "Bot"
  | Const i -> "Const " ^ (string_of_int i)
  | Top     -> "Top"

(*  fpprint : formatter -> elem -> unit  *)
let fpprint fmt c = Format.fprintf fmt "%s" (to_string c)

(*  pprint : elem -> unit  *)
let pprint c = Format.printf "%s" (to_string c)
