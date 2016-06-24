module A = Ast

type stmt = { label : int;
	      stmt  : stmt_desc; }
and stmt_desc =
  | Skip
  | Assign of A.var * A.aexp
  | Seq of stmt * stmt
  | While of A.bexp * stmt
  | If of A.bexp * stmt * stmt
  | Chread of A.chan * A.var
  | Chwrite of A.chan * A.aexp
  | Choice of stmt * stmt
  | Stop

let reset,make_label =
  let count     = ref 1 in
  (fun () -> count := 1),
  (fun () -> let label = !count in
	     begin 
	       incr count;
	       label
	     end)

let make_stmt sd = { label = make_label ();
		     stmt  = sd }

(** Smart constructors for creating labelled statements *)
let skip ()        = make_stmt Skip
let assign (x,e)   = make_stmt (Assign (x,e))
let seq (s1,s2)    = make_stmt (Seq (s1,s2))
let whiles (e,s)   = make_stmt (While (e,s))
let ifs (e,s1,s2)  = make_stmt (If (e,s1,s2))
let chread (ch,x)  = make_stmt (Chread (ch,x))
let chwrite (ch,e) = make_stmt (Chwrite (ch,e))
let choice (s1,s2) = make_stmt (Choice (s1,s2))
let stop ()        = make_stmt Stop
  
let rec label s = match s with
  | A.Skip           -> skip ()
  | A.Assign (x,e)   -> assign (x,e)
  | A.Seq (s1,s2)    ->
    let s1' = label s1 in
    let s2' = label s2 in
    seq (s1',s2')
  | A.While (e,s)    ->
    let s' = label s in
    whiles (e,s')
  | A.If (e,s1,s2)   ->
    let s1' = label s1 in
    let s2' = label s2 in
    ifs (e,s1',s2')
  | A.Chread (ch,x)  -> chread (ch,x)
  | A.Chwrite (ch,e) -> chwrite (ch,e)
  | A.Choice (s1,s2) ->
    let s1' = label s1 in
    let s2' = label s2 in
    choice (s1',s2')
  | A.Stop           -> stop ()
