(** Abstract sign datatype and operations *)

type elem = Sign of int
(*  | Bot     ~ 0x00  0b000 *)
(*  | Neg     ~ 0x01  0b001 *)
(*  | Zero    ~ 0x02  0b010 *)
(*  | NegZero ~ 0x03  0b011 *)
(*  | Pos     ~ 0x04  0b100 *)
(*  | NotZero ~ 0x05  0b101 *)
(*  | PosZero ~ 0x06  0b110 *)
(*  | Top     ~ 0x07  0b111 *)

(** A shorthand to inject constants *)
(*  const : int -> elem  *)
let const c = match c with
  | 0 -> Sign 0x02 (* zero *)
  | _ -> if c > 0 then Sign 0x04 else Sign 0x01

(*  eq : elem -> elem -> bool *)
let eq (Sign i) (Sign i') = (i = i')

(*  leq : elem -> elem -> bool  *)
let leq (Sign i) (Sign i') = if i = (i land i') then true else false

(*  join : elem -> elem -> elem  *)
let join (Sign i) (Sign i') = Sign (i lor i')

(*  meet : elem -> elem -> elem  *)
let meet (Sign i) (Sign i') = Sign (i land i')

(*  top : elem  *)
let top = Sign 0x07

(*  bot : elem  *)
let bot = Sign 0x00

(*  is_bot : elem -> bool  *)
let is_bot e = (e = Sign 0x00)

(*  widening : elem -> elem -> elem  *)
let widening = join

(*  add : elem -> elem -> elem *)
let add (Sign i) (Sign i') = match i,i' with
  | 0x00, _ -> bot         (* bot + _ = bot       *)
  | _, 0x00 -> bot         (* _ + bot = bot       *)
  | 0x07, _ -> top         (* top + _ = top       *)
  | _, 0x07 -> top         (* _ + top = top       *)
  | 0x02, _ -> Sign i'     (* zero + i' = i'      *)
  | _, 0x02 -> Sign i      (* i' + zero = i'      *)
  | 0x01,0x01 -> Sign 0x01 (* neg + neg = neg     *)
  | 0x01,0x03 -> Sign 0x01 (* neg + negzero = neg *)
  | 0x03,0x01 -> Sign 0x01 (* negzero + neg = neg *)
  | 0x04,0x04 -> Sign 0x04 (* pos + pos = pos     *)
  | 0x04,0x06 -> Sign 0x04 (* pos + poszero = pos *)
  | 0x06,0x04 -> Sign 0x04 (* poszero + pos = pos *)
  | _,_       -> top

(*  sub : elem -> elem -> elem *)
let sub (Sign i) (Sign i') = match i,i' with
  | 0x00, _ -> bot          (* bot - _ = bot               *)
  | _, 0x00 -> bot          (* _ - bot = bot               *)
  | 0x07, _ -> top          (* top - _ = top               *)
  | _, 0x07 -> top          (* _ - top = top               *)
  | 0x02, 0x01 -> Sign 0x04 (* zero - neg = pos            *)
  | 0x02, 0x04 -> Sign 0x01 (* zero - pos = neg            *)
  | 0x02, 0x03 -> Sign 0x06 (* zero - negzero = poszero    *)
  | 0x02, 0x06 -> Sign 0x03 (* zero - poszero = negzero    *)
  | 0x02, _    -> Sign i'   (* zero - i = i   i \in {zero,notzero} *)
  | _, 0x02    -> Sign i    (* i' - zero = i'              *)
  | 0x01,0x04  -> Sign 0x01 (* neg - pos = neg             *)
  | 0x01,0x06  -> Sign 0x01 (* neg - poszero = neg         *)
  | 0x03,0x04  -> Sign 0x01 (* negzero - pos = neg         *)
  | 0x03,0x06  -> Sign 0x03 (* negzero - poszero = negzero *)
  | 0x04,0x01  -> Sign 0x04 (* pos - neg = pos             *)
  | 0x04,0x03  -> Sign 0x04 (* pos - negzero = pos         *)
  | 0x06,0x01  -> Sign 0x04 (* poszero - neg = pos         *)
  | 0x06,0x03  -> Sign 0x06 (* poszero - negzero = poszero *)
  | _,_        -> top

(*  mult : elem -> elem -> elem *)
let mult (Sign i) (Sign i') = match i,i' with
  | 0x00, _ -> bot         (* bot * _ = bot           *)
  | _, 0x00 -> bot         (* _ * bot = bot           *)
  | 0x02, _ -> Sign 0x02   (* zero * i' = zero        *)
  | _, 0x02 -> Sign 0x02   (* i' * zero = zero        *)
  | 0x07, _ -> top         (* top * _ = top           *)
  | _, 0x07 -> top         (* _ * top = top           *)
  | 0x01,0x01 -> Sign 0x04 (* neg * neg = pos         *)
  | 0x01,0x03 -> Sign 0x06 (* neg * negzero = poszero *)  (*fixed, was: negzero*)
  | 0x03,0x01 -> Sign 0x06 (* negzero * neg = poszero *)  (*fixed, was: negzero*)
  | 0x04,0x04 -> Sign 0x04 (* pos * pos = pos         *)
  | 0x04,0x06 -> Sign 0x06 (* pos * poszero = poszero *)
  | 0x06,0x04 -> Sign 0x06 (* poszero + pos = poszero *)
  | _,_       -> top

type equiv_class = int
type partition = int list   (* could be refined to 3 bits of an int *)

(*  compare : equiv_class -> equiv_class -> int *)
let compare e e' = e - e'

(*  repr : equiv_class -> elem  *)
let repr e = Sign e

(*  project : equiv_class -> elem  *)
let project e = Sign e

(*  fold_partition : ('a -> equiv_class -> 'a) -> 'a -> partition -> 'a  *)
let fold_partition = List.fold_left (* agrees with total order *)

(*  partition : elem -> partition  *)
let partition (Sign i) = [0x01;0x02;0x04]

(*  overlay_partitions : partition -> partition -> partition  *)
let overlay_partitions ss1 ss2 = [0x01;0x02;0x04]


(** {3 Pretty printing routines } *)

(*  to_string : elem -> unit  *)
let to_string (Sign i) = match i with
  | 0x00 -> "Bot"
  | 0x01 -> "Neg"
  | 0x02 -> "Zero"
  | 0x03 -> "NegZero"
  | 0x04 -> "Pos"
  | 0x05 -> "NotZero"
  | 0x06 -> "PosZero"
  | 0x07 -> "Top"
  | _ ->
    failwith ("sign.ml: unexpected Sign " ^ (string_of_int i) ^ " in to_string")

(*  fpprint : formatter -> elem -> unit  *)
let fpprint fmt c = Format.fprintf fmt "%s" (to_string c)

(*  pprint : elem -> unit  *)
let pprint c = Format.printf "%s" (to_string c)
