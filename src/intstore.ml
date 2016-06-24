module A = Ast
  
module I = Interval
module Val = I
    
include Absstore.Make(Interval)
  
(*  eval_aexp : Ast.aexp -> absstore -> interval  *)
let rec eval_aexp e sigma = match e with
  | A.Num n  -> I.const n
  | A.Var x  -> lookup sigma x
  | A.Any    -> I.top
  | A.Binop (e1,op,e2) ->
    (match eval_aexp e1 sigma, op, eval_aexp e2 sigma with
      | v1, A.Plus,  v2 -> I.add v1 v2
      | v1, A.Minus, v2 -> I.sub v1 v2
      | v1, A.Mult,  v2 -> I.mult v1 v2)
  
(*  eval_bexp_true : Ast.bexp -> absstore -> absstore  *)
let rec eval_bexp_true b sigma = match b with
  | A.True  -> sigma
  | A.False -> bot
  | A.Not b -> eval_bexp_false b sigma
  | A.Relop (e1,op,e2) ->
    (match eval_aexp e1 sigma, op, eval_aexp e2 sigma with
      | v1, A.Eq, v2 ->
	let meet_v1v2 = I.meet v1 v2 in
	if I.is_bot meet_v1v2
        then bot
	else
	  (match e1, e2 with
	    | A.Var x1, A.Var x2 -> extend (extend sigma x1 meet_v1v2) x2 meet_v1v2
	    | A.Var x1, _  -> extend sigma x1 meet_v1v2
	    | _, A.Var x2  -> extend sigma x2 meet_v1v2
	    | _, _ -> sigma)
      | v1, A.Lt, v2 ->
	(match v1,v2 with
	  | I.Bot, _ -> bot
	  | _, I.Bot -> bot
	  | I.Interval (l1,u1),I.Interval (l2,u2) ->
	    let u1' = I.ub_min u1 (I.ub_sub u2 (I.LBound 1)) in
	    let l2' = I.lb_max (I.lb_add l1 (I.LBound 1)) l2 in
	    (match e1, e2 with
	      | A.Var x1, A.Var x2 ->
		extend (extend sigma x1 (I.interval (l1,u1')))
		                     x2 (I.interval (l2',u2))
	      | A.Var x1,_ -> extend sigma x1 (I.interval (l1,u1'))
	      | _,A.Var x2 -> extend sigma x2 (I.interval (l2',u2))
	      | _, _ -> sigma))
      | v1, A.Leq, v2 ->
	(match v1,v2 with
	  | I.Bot, _ -> bot
	  | _, I.Bot -> bot
	  | I.Interval (l1,u1),I.Interval (l2,u2) ->
	    let u1' = I.ub_min u1 u2 in
	    let l2' = I.lb_max l1 l2 in
	    (match e1, e2 with
	      | A.Var x1, A.Var x2 ->
		extend (extend sigma x1 (I.interval (l1,u1')))
		                     x2 (I.interval (l2',u2))
	      | A.Var x1,_  -> extend sigma x1 (I.interval (l1,u1'))
	      | _,A.Var x2  -> extend sigma x2 (I.interval (l2',u2))
	      | _, _ -> sigma)))
  | A.Conj (b1,b2) -> eval_bexp_true b2 (eval_bexp_true b1 sigma) (* models left-to-right eval *)

(*  eval_bexp_false : Ast.bexp -> absstore -> absstore  *)
and eval_bexp_false b sigma = match b with
  | A.True  -> bot
  | A.False -> sigma
  | A.Not b -> eval_bexp_true b sigma
  | A.Relop (e1,op,e2) ->
    (match eval_aexp e1 sigma, op, eval_aexp e2 sigma with
      | v1, A.Eq, v2 ->
	if I.is_bot v1 || I.is_bot v2
        then bot
	else sigma
      | v1, A.Lt, v2 ->
	(match v1,v2 with
	  | I.Bot, _ -> bot
	  | _, I.Bot -> bot
	  | I.Interval (l1,u1),I.Interval (l2,u2) ->
	    let l1' = I.lb_max l1 l2 in
	    let u2' = I.ub_min u1 u2 in
	    (match e1, e2 with
	      | A.Var x1, A.Var x2 ->
		extend (extend sigma x1 (I.interval (l1',u1)))
		                     x2 (I.interval (l2,u2'))
	      | A.Var x1, _ -> extend sigma x1 (I.interval (l1',u1))
	      | _, A.Var x2 -> extend sigma x2 (I.interval (l2,u2'))
	      | _,_ ->	sigma))
      | v1, A.Leq, v2 ->
	(match v1,v2 with
	  | I.Bot, _ -> bot
	  | _, I.Bot -> bot
	  | I.Interval (l1,u1),I.Interval (l2,u2) ->
	    let l1' = I.lb_max l1 (I.lb_add l2 (I.LBound 1)) in
	    let u2' = I.ub_min u2 (I.ub_sub u1 (I.LBound 1)) in
	    (match e1, e2 with
	      | A.Var x1, A.Var x2 ->
		extend (extend sigma x1 (I.interval (l1',u1)))
		                     x2 (I.interval (l2,u2'))
	      | A.Var x1,_ -> extend sigma x1 (I.interval (l1',u1))
	      | _,A.Var x2 -> extend sigma x2 (I.interval (l2,u2'))
	      | _, _ -> sigma)))
  | A.Conj (b1,b2) -> join (eval_bexp_false b1 sigma) (* models shortcut Bool eval *)
                           (eval_bexp_false b2 (eval_bexp_true b1 sigma))

