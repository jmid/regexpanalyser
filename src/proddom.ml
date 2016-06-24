module Make(C1 : Absstore.LATTICE)(C2 : Absstore.LATTICE)(C3 : Absstore.LATTICE) =
struct
  type elem = C1.elem * C2.elem * C3.elem

  let bot = (C1.bot,C2.bot,C3.bot)

  let top = (C1.top,C2.top,C3.top)
    
  (*  leq : elem -> elem -> bool  *)
  let leq (c1,c2,c3) (d1,d2,d3) = C1.leq c1 d1 && C2.leq c2 d2 && C3.leq c3 d3

  (*  eq : elem -> elem -> bool  *)
  let eq (c1,c2,c3) (d1,d2,d3) = C1.eq c1 d1 && C2.eq c2 d2 && C3.eq c3 d3
    
  (*  join : elem -> elem -> elem  *)
  let join (c1,c2,c3) (d1,d2,d3) = (C1.join c1 d1, C2.join c2 d2, C3.join c3 d3)

  (*  meet : elem -> elem -> elem  *)
  let meet (c1,c2,c3) (d1,d2,d3) = (C1.meet c1 d1, C2.meet c2 d2, C3.meet c3 d3)

  (*  widening : elem -> elem -> elem  *)
  let widening (c1,c2,c3) (d1,d2,d3) = (C1.widening c1 d1, C2.widening c2 d2, C3.widening c3 d3)


  (** {3 Pretty printing routines } *)

  (*  fpprint : Format.formatter -> elem -> unit  *)
  let fpprint fmt (c1,c2,c3) =
    begin
      Format.fprintf fmt "(";
      C1.fpprint fmt c1;
      Format.print_flush ();
      Format.fprintf fmt ", ";
      C2.fpprint fmt c2;
      Format.print_flush ();
      Format.fprintf fmt ", ";
      C3.fpprint fmt c3;
      Format.print_flush ();
      Format.fprintf fmt ")";
    end

  (*  pprint : elem -> unit  *)
  let pprint (c1,c2,c3) =
    let s1 = C1.to_string c1 in
    let s2 = C2.to_string c2 in
    let s3 = C3.to_string c3 in
    Format.printf "(%s, %s, %s)" s1 s2 s3

  (*  to_string : L.elem -> string  *)
  let to_string e =
    begin
      fpprint Format.str_formatter e;
      Format.flush_str_formatter ();
    end
end
