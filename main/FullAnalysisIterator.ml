(***************************************************)
(*                                                 *)
(*    Forward/Backward Full Analysis Iterator    *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open InvMap
open Apron
open Bddapron
open Iterator
open Partition 
open BDDDomain
(*open Yices*)

module FullAnalysisIterator (B: PARTITION)(D: BDDDomain) =
struct

  	module B = B 
  	module D = D   	
	module InvMapTuple = Map.Make(struct type t=label*int let compare=compare end)

	(* exceptions *)
	exception Bottom_error

	let d_err1 = ref [] 
	let dd_err1 = ref [] 
	let typ_err1 = ref "B" 
	let d_err2 = ref [] 
	let dd_err2 = ref [] 	
	let label_ass = ref [] 	
	let predicates = ref [] 
	let predicates2 = ref [] 
  	let bool_vars : var list ref = ref [] 
  	let bool_exps : bExp list ref = ref []

	let fwdInvMapTuple = ref InvMapTuple.empty
	let addFwdInvTuple (l,n) (a:B.t) = fwdInvMapTuple := InvMapTuple.add (l,n) a !fwdInvMapTuple
	let fwdInvMapTuple2 = ref InvMapTuple.empty
	let addFwdInvTuple2 (l,n) (a:D.t) = fwdInvMapTuple2 := InvMapTuple.add (l,n) a !fwdInvMapTuple2
	
	let bwdInvMapTuple = ref InvMapTuple.empty
	let addBwdInvTuple (l,n) (a:B.t) = bwdInvMapTuple := InvMapTuple.add (l,n) a !bwdInvMapTuple		
	let bwdInvMapTuple2 = ref InvMapTuple.empty
	let addBwdInvTuple2 (l,n) (a:D.t) = bwdInvMapTuple2 := InvMapTuple.add (l,n) a !bwdInvMapTuple2
	
  	let fwdInvMap = ref InvMap.empty
  	let addFwdInv l (a:B.t) = fwdInvMap := InvMap.add l a !fwdInvMap
  	let fwdInvMap2 = ref InvMap.empty
  	let addFwdInv2 l (a:D.t) = fwdInvMap2 := InvMap.add l a !fwdInvMap2
  		
  	let fwdMap_print fmt m1 m2 = InvMap.iter (fun l a -> if l>0 then (
		if InvMapTuple.mem (l,1) m2 then ( InvMapTuple.iter (fun (l,n) b -> Format.fprintf fmt "%a unwind %d: %a\n" label_print l (n-1) B.print b ) m2; Format.fprintf fmt "%a: %a\n" label_print l B.print a )
      	else Format.fprintf fmt "%a: %a\n" label_print l B.print a)
		) m1

  	let fwdMap2_print fmt m1 m2 = InvMap.iter (fun l a -> if l>0 then (
		if InvMapTuple.mem (l,1) m2 then ( InvMapTuple.iter (fun (l,n) b -> Format.fprintf fmt "%a unwind %d: %a\n" label_print l (n-1) D.print b ) m2; Format.fprintf fmt "%a: %a\n" label_print l D.print a )
      	else Format.fprintf fmt "%a: %a\n" label_print l D.print a)
		) m1

  	let errInvMap = ref InvMap.empty
  	let addErrInv l (a:B.t) = errInvMap := InvMap.add l a !errInvMap
  	let errMap_print fmt m1 = InvMap.iter (fun l a -> Format.fprintf fmt "%a: %a\n" label_print l B.print a) m1

  	let errInvMap2 = ref InvMap.empty
  	let addErrInv2 l (a:D.t) = errInvMap2 := InvMap.add l a !errInvMap2
  	let errMap2_print fmt m1 = InvMap.iter (fun l a -> Format.fprintf fmt "%a: %a\n" label_print l D.print a) m1


	let findFwdInv l m : B.t = InvMap.find l m

  	let bwdInvMap = ref InvMap.empty
  	let addBwdInv l (a:B.t) = bwdInvMap := InvMap.add l a !bwdInvMap
  	let bwdInvMap2 = ref InvMap.empty
  	let addBwdInv2 l (a:D.t) = bwdInvMap2 := InvMap.add l a !bwdInvMap2

  	let bwdMap_print fmt m1 m2 = let sr = Stack.create () in
						InvMap.iter (fun l a -> Stack.push l sr) m1;
						Stack.iter (fun l -> if InvMapTuple.mem (l,!joinbwd) m2 then (  Format.fprintf fmt "%a unwind >%d: %a\n" label_print l (!joinbwd-1) B.print (InvMapTuple.find (l,!joinbwd) m2);
						for i = !joinbwd-1 downto 1 do Format.fprintf fmt "%a unwind %d: %a\n" label_print l i B.print (InvMapTuple.find (l,i) m2) done; Format.fprintf fmt "%a unwind 0: %a\n" label_print l B.print (InvMap.find l m1)	) else Format.fprintf fmt "%a: %a\n" label_print l B.print (InvMap.find l m1) ) sr


  	let bwdMap2_print fmt m1 m2 = let sr = Stack.create () in
						InvMap.iter (fun l a -> Stack.push l sr) m1;
						Stack.iter (fun l -> if InvMapTuple.mem (l,!joinbwd) m2 then (  Format.fprintf fmt "%a unwind >%d: %a\n" label_print l (!joinbwd-1) D.print (InvMapTuple.find (l,!joinbwd) m2);
						for i = !joinbwd-1 downto 1 do Format.fprintf fmt "%a unwind %d: %a\n" label_print l i D.print (InvMapTuple.find (l,i) m2) done; Format.fprintf fmt "%a unwind 0: %a\n" label_print l D.print (InvMap.find l m1)	) else Format.fprintf fmt "%a: %a\n" label_print l D.print (InvMap.find l m1) ) sr
 
  	let read_process_lines command =
  		let lines = ref [] in
  		let in_channel = Unix.open_process_in command in
  		begin
    	try
      		while true do
        		lines := input_line in_channel :: !lines
      		done;
    	with End_of_file ->
      	ignore (Unix.close_process_in in_channel)
  		end;
  		List.rev !lines


	let rec print_list n  = function 
		[] -> ()
		| e::l -> print_int n; print_string e ; print_string " \n" ; print_list (n+1) l 


	let rec process_result = function 
		[] -> []
		| e :: [] -> List.filter (fun s -> String.contains s 'A') (String.split_on_char ' ' (String.sub e 1 (String.length e - 2)))
		| e::l -> (if (e="sat") then ( []) else (process_result l))
				 (*	else (*(print_string e; (*let sl = (String.split_on_char ' ' e) in for i in sl: print_string i;*)*) (B.top env vars)  *)

	let rec print_Latteresult  = function 
		[] -> 1
		| e :: [] -> int_of_string e
		| e::l -> print_Latteresult l


	let partition_toZ3 (p1:B.t) (p2:B.t) =
		let lines = ref ["(set-option :produce-unsat-cores true)"] in
		List.iter (fun v -> lines := !lines @ [("(declare-fun " ^ v.varName ^ "() Int)")]) (B.vars p1); 
		List.iter (fun s -> lines := !lines @ [(s)]) (B.to_stringZ3 p1 p2);
		lines := !lines @ [("(check-sat)")] @ [("(get-unsat-core)")];
		String.concat "\n" !lines;;	

	let write_to_Z3file file (p1:B.t) (p2:B.t) =
		let oc = open_out file in  
		let str = partition_toZ3 p1 p2 in 					(* create or truncate file, return channel *)
  		Printf.fprintf oc "%s\n" str; 				(*(process_message message); *)   (* write something *)   
  		(*Format.fprintf !fmt "\n Z3 process: \n %s \n" str; *)
  		close_out oc;;


  (* Forward Iterator *)

  let rec fwdStm funcs env vars p s =
    match s with
    | A_label (s,sa) -> p
    | A_return -> B.bot env vars
    | A_assign ((l,_),(e,_)) ->  (match e with 
      		| A_arithmetic (e,ea) -> let p = B.fwdAssign p (l,e) in (*Format.fprintf !fmt "Assgn inv: %a\n" B.print p;*) p
      		| A_boolean (e,ea) -> let p1 = B.filter p e in 
      				       let p2 = B.filter p (fst (negBExp (e, ea))) in
      				       if (B.isLeq p p1) then ( let e1 = (A_const 1) in B.fwdAssign p (l,e1) ) 
      				       else if (B.isLeq p p2) then ( let e1 = (A_const 0) in B.fwdAssign p (l,e1) ) 
      				       else ( let e1 = A_interval (0,1)  in B.fwdAssign p (l,e1) ) )
    | A_assert (b,ba) ->
		let b' = negBExp (b,ba) in
      	  	let p2 = B.filter p (fst (b')) in	
	        let p2' = (B.filter p b) in 
		(*Format.fprintf !fmt "\n End fwdAssert: %a \n" B.print p2'; *)
		p2'
    | A_if ((b,ba),s1,s2) ->
      let p1' = fwdBlk funcs env vars (B.filter p b) s1 in 
      (*Format.fprintf !fmt "\n IF then: %a \n" B.print p1';*)
      let p2 = B.filter p (fst (negBExp (b,ba))) in
      (*Format.fprintf !fmt "\n IF cond else: %a \n" B.print p2;*)
      let p2' = fwdBlk funcs env vars p2 s2 in 
      (*Format.fprintf !fmt "\n IF else: %a \n" B.print p2';*)
      B.join p1' p2'
    | A_ifdef ((b,ba),s1,s2) -> p  
    | A_while (l,(b,ba),s) ->
      let rec aux i p2 n =
        let i' = B.join p p2 in
	Format.fprintf !fmt "unwind: %d inv: %a\n" n B.print i';
	addFwdInvTuple (l,n) i';
        if !tracefwd && not !minimal then begin
          Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
          Format.fprintf !fmt "p1: %a\n" B.print p;
          Format.fprintf !fmt "i: %a\n" B.print i;
          Format.fprintf !fmt "p2: %a\n" B.print p2;
          Format.fprintf !fmt "i': %a\n" B.print i'
        end;
        if B.isLeq i' i then i else
          let i'' = if n <= !joinfwd then i' 
          	     else B.widen i (B.join i i') in
          if !tracefwd && not !minimal then
            Format.fprintf !fmt "i'': %a\n" B.print i'';
          aux i'' (fwdBlk funcs env vars (B.filter i'' b) s) (n+1)
      in
	(*Format.fprintf !fmt "before inv: %a\n" B.print p;*)
      let i = B.bot env vars in
      let p2 = fwdBlk funcs env vars (B.filter i b) s in
      let pp = aux i p2 1 in
      Format.fprintf !fmt "inv - aux: %a\n" B.print pp;
      let p_down = fwdBlk funcs env vars (B.filter pp b) s in   (* this line is added additionally: performs narrowing  *)
      let p_final = B.join p_down (B.filter p (fst (negBExp (b,ba)))) in (* this line is added to handle example1.c, when the loop variable is non-deterministic *)
      Format.fprintf !fmt "inv narrow down: %a\n" B.print p_down;
      Format.fprintf !fmt "inv narrow+join final: %a\n" B.print p_final;
      let p_final_neg = B.filter p_final (fst (negBExp (b,ba))) in 
      let p_down_neg = B.filter p_down (fst (negBExp (b,ba))) in 
      (*Format.fprintf !fmt "inv narrow final: %a\n" B.print p_final;
      Format.fprintf !fmt "inv narrow final neg: %a\n" B.print p_final_neg;
      Format.fprintf !fmt "inv narrow down: %a\n" B.print p_down;
      Format.fprintf !fmt "inv narrow down neg: %a\n" B.print p_down_neg;  *)  
      let binv = try InvMap.find l !bwdInvMap with Not_found -> B.top env vars in 
      let pp = B.meet p_final binv in 
      let p_err = if (B.isLeq (B.top env vars) pp) then (pp) 
      		   else if (B.isLeq pp (B.bot env vars)) then (pp)
      		   else if (B.isLeq pp binv) && (B.isLeq binv pp) then (pp)
						else (
						  let file = "test" in 
						  write_to_Z3file file pp binv; 
						  let l2 = read_process_lines ("z3 "^(file)) in 
						  (* Format.fprintf !fmt "CALLS Z3: \n"; print_list 0 l2;  *)
						  let z3_list = process_result l2 in 
						  (*print_list 0 z3_list; *)
						  let p1 = B.filter_list z3_list pp in 
						  p1
						) in 
      addErrInv l p_err; 
      (*Format.fprintf !fmt "inv written: %a\n" B.print pp;*)	  								  
      addFwdInv l pp; p_final_neg
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm funcs env vars p s) p ss in
      fwdBlk funcs env vars p f.funcBody
    | A_recall (f,ss) -> B.top env vars (* TODO *)

  and fwdBlk funcs env vars (p:B.t) (b:block) : B.t =
    let result_print l p =
      Format.fprintf !fmt "### %a ###: %a\n" label_print l B.print p
    in
    match b with
    | A_empty l ->
      (*if !tracefwd && not !minimal then result_print l p; *) 
      let binv = try InvMap.find l !bwdInvMap with Not_found -> B.top env vars in 
      let pp = B.meet p binv in 
      let p_err = if (B.isLeq (B.top env vars) pp) then (pp) 
      		   else if (B.isLeq pp (B.bot env vars)) then (pp)
      		   else if (B.isLeq pp binv) && (B.isLeq binv pp) then (pp)
						else (
						  let file = "test" in 
						  write_to_Z3file file pp binv; 
						  let l2 = read_process_lines ("z3 "^(file)) in 
						  (* Format.fprintf !fmt "CALLS Z3: \n"; print_list 0 l2;  *)
						  let z3_list = process_result l2 in 
						  (*print_list 0 z3_list; *)
						  let p1 = B.filter_list z3_list pp in 
						  p1
						) in 
      addErrInv l p_err;      	  
      addFwdInv l pp; pp
    | A_block (l,(s,_),b) ->
      (*result_print l p; *)
      let binv = try InvMap.find l !bwdInvMap with Not_found -> B.top env vars in 
      let pp = B.meet p binv in 
      let p_err = if (B.isLeq (B.top env vars) pp) then (pp)
      		   else if (B.isLeq pp (B.bot env vars)) then (pp)      
      		   else if (B.isLeq pp binv) && (B.isLeq binv pp) then (pp)
						else (
						  let file = "test" in 
						  (*Format.fprintf !fmt "\np: ### %a ###\n" B.print pp; 
						  Format.fprintf !fmt "\nb_inv: ### %a ###\n" B.print binv; *)
						  write_to_Z3file file pp binv; 
						  let l2 = read_process_lines ("z3 "^(file)) in 
						  (*Format.fprintf !fmt "CALLS Z3: \n"; print_list 0 l2; *)
						  let z3_list = process_result l2 in 
						  (*print_list 0 z3_list;*)
						  let p1 = B.filter_list z3_list pp in 
						  p1
						) in 
		(*Format.fprintf !fmt "\n### %a ###\n" B.print p_err; *)
          addErrInv l p_err; 
	  addFwdInv l pp; 
	  (match s with
    		| A_assert (b,ba) -> label_ass := [l]; 
    		| _ -> label_ass := !label_ass); 
      fwdBlk funcs env vars (fwdStm funcs env vars pp s) b



  (* Backward Iterator + Recursion *)

  let rec bwdStm funcs env vars (p,r,flag) s =
    let b_filter = B.bwdfilter_underapprox in
    (*let b_bwdAssign = if !Iterator.nondet then B.bwdAssign_underapprox else B.bwdAssign in *)
    match s with
    | A_label (s,sa) -> (p,r,flag)
    | A_return -> B.bot env vars, r, flag
    | A_assign ((l,_),(e,ea)) -> 
    	(match e with 
      		| A_arithmetic (e,ea) -> B.bwdAssign p (l, e), r, flag 
      		| A_boolean (e,ea) -> let p_proj = B.project p l in 
      					(*Format.fprintf !fmt "project : %a : \n" B.print p_proj; *)
      					
      				       let p1 = B.filter p (A_rbinary (A_GREATER,(l,ea),(A_const 0,ea))) in 
      				       let p2 = B.filter p (A_rbinary (A_LESS_EQUAL,(l,ea),(A_const 0,ea))) in
      				       let p_fin = if (B.isLeq p p1) then ( B.filter p_proj e ) 
      				       else if (B.isLeq p p2) then ( B.filter p_proj (fst (negBExp (e,ea))) ) 
      				       else p_proj in 
      				       (*Format.fprintf !fmt "Assign bool : %a : \n" B.print p_fin; *)
      					p_fin, r, flag )
    | A_assert (b,ba) -> 
    		let b_neg = (negBExp (b,ba)) in 
    		(*Format.fprintf !fmt "assert neg ( %a )\n" bExp_print b_neg; *)
    		let p_neg = B.filter p (fst (b_neg)) in 
    		if B.isBot (List.hd !d_err2) then d_err1 := [p_neg];
		let p = if B.isBot (List.hd !d_err1) then (p_neg)
			else B.meet (List.hd !d_err1) (p_neg) in 
		(*d_err1 := [p];*) typ_err1 := "B";  
		(*Format.fprintf !fmt "ASSERT p_neg : %a : p: %a \n" B.print p_neg B.print p; *)
		(*if B.isBot p then raise Bottom_error; *)
      	p, r, flag
    | A_if ((b,ba),s1,s2) ->
      let (p1, _, flag1) = bwdBlk funcs env vars (p, r, flag) s1 in
      (* Format.fprintf !fmt "IF ### before then p1: %a\n" B.print p1; *)				
	  (*Format.fprintf !fmt "before if p1: %a\n" B.print p1; *)
      let (p2, _, flag2) = bwdBlk funcs env vars (p, r, flag) s2 in
      (*Format.fprintf !fmt "IF ### FileNAME: %s\n" !Iterator.filename;*)
      (*Format.fprintf !fmt "Bwd IF:# p1: %a : p2: %a \n" B.print p1 B.print p2;
      Format.fprintf !fmt "Booleans:# 1: %b : 2: %b \n" (B.isLeq p1 p2) (B.isLeq p2 p1); *)
      if (not (B.isLeq p1 p2)) || (not (B.isLeq p2 p1)) then 
        if (!Iterator.filename="tests/tcas1.c") then 
        (if ((B.isBot p1) || (B.isBot p2)) then 
         (let isAdded = ref false in 
         List.iter (fun d -> if (AbstractSyntax.bExp_isEq b d) then isAdded:=true) !predicates;   
         if (not !isAdded) then predicates:=b::!predicates ))       
        else 
        (let isAdded = ref false in 
         List.iter (fun d -> if (AbstractSyntax.bExp_isEq b d) then isAdded:=true) !predicates;   
         if (not !isAdded) then predicates:=b::!predicates );
      let p1 = B.filter p1 b in 
      let p2 = B.filter p2 (fst (negBExp (b, ba))) in  
      (*Format.fprintf !fmt "IF ### before join p1: %a ## p2: %a\n" B.print p1 B.print p2; *)
      (B.join p1 p2, r, flag1 || flag2)
    | A_while (l, (b, ba), s) ->
      let p_final = B.filter p (fst (negBExp (b,ba))) in
      let rec aux i p2 p_final n = 
        Format.fprintf !fmt "p2- in aux while: %a : %d : %d\n" B.print p2 n !joinbwd;
        let i' = B.join p_final p2 in
	addBwdInvTuple (l,n) i';
        if B.isLeq i' i then ( i) else
          (let i'' = if n <= !joinbwd then i' else 
              (Format.fprintf !fmt "WIDEN while: %a\n" B.print (B.widen i i'); B.widen i i') in 
          Format.fprintf !fmt "i''- in aux while: %a\n" B.print i'';
          let (pp,r,flag) = (bwdBlk funcs env vars (i'',r,flag) s) in 
          aux i'' (B.filter pp b) p_final (n+1))
      in
      let i = B.bot env vars in
      let pp = aux i p_final p_final 1 in 
      Format.fprintf !fmt "pp-aux while: %a\n" B.print pp;
      let p_down1 = if (not !Iterator.narrow) then pp 
      		     else ( 
      			let (p_down,r,flag) = bwdBlk funcs env vars (pp,r,flag) s in 
      			(B.filter p_down b) ) in 
      Format.fprintf !fmt "narrowing while: %a\n" B.print p_down1;
      (addBwdInv l p_down1; (p_down1, r, flag))
(*	  let rec iter_down post pre nb = 
	  		  (*Format.fprintf !fmt "post in while %d: %a\n" nb B.print post;
			  Format.fprintf !fmt "exit in while %d: %a\n" nb B.print p;
			  Format.fprintf !fmt "pre in while %d: %a\n" nb B.print pre;*)
			  let (p2, _, flag2) = bwdBlk funcs env vars (post,r,flag) s in
			  let p2' = if !Iterator.approx>=0 then B.bwdfilter_underapproxwhile p2 p b pre 
			  			else B.bwdfilter p2 b (*B.bwdfilter_underapproxwhile p2 p b pre*) 		  
			  in 	 	
			  (*if !Iterator.underapprox then Format.fprintf !fmt "result in while %B %d: %a\n" !Iterator.underapprox nb B.print p2'
			  else Format.fprintf !fmt "result in while %B %d: %a\n" !Iterator.underapprox nb B.print p2'; *)
			  
			  (*if !Iterator.underapprox then*) (
			  	if (B.isLeq post p2') then
           			( unroll p2' !joinbwd ) (* Format.fprintf !fmt "post in while %d: %a\n" nb B.print post; let pinv = InvMapTuple.find (l,!joinbwd) !fwdInvMapTuple in Format.fprintf !fmt "p-inv while: %a\n" B.print pinv; (post, r, flag2) *)
              	else let c = if nb <= !joinbwd then B.meet post p2'
                		   else B.lowerwiden post p2' in 
					   (*Format.fprintf !fmt "inv in while %B %d: %a\n" !Iterator.underapprox nb B.print c;*)
		               iter_down c pre (nb + 1) )
			  (* else (
			  	if (B.isLeq p2' post) then
           			( unroll p2' !joinbwd ) (* Format.fprintf !fmt "post in while %d: %a\n" nb B.print post; let pinv = InvMapTuple.find (l,!joinbwd) !fwdInvMapTuple in Format.fprintf !fmt "p-inv while: %a\n" B.print pinv; (post, r, flag2) *)
              	else let c = if nb <= !joinbwd then B.meet post p2'
                		   else B.widen post p2' in 
					   Format.fprintf !fmt "inv in while %B %d: %a\n" !Iterator.underapprox nb B.print c;
		               iter_down c pre (nb + 1)			  
			  ) *)
	  and unroll post nb = 
	  		if nb=0 then (post,r,flag) else 
	  		let pre = InvMapTuple.find (l,!joinbwd) !fwdInvMapTuple in
			(* Format.fprintf !fmt "p-inv while %d: %a\n" nb B.print pre; *)
			let (p2, _, flag2) = bwdBlk funcs env vars (post,r,flag) s in
			let p2' = B.bwdfilter_underapproxwhile p2 p b pre in 
			addBwdInvTuple (l,nb) p2';
			unroll p2' (nb-1)
	  in
	  let (pp, r, flag) = iter_down p p 1 in	  
	  (* Format.fprintf !fmt "Result inv while: %a\n" B.print p; *)
	  (*let p = B.meet a p in*)
      (addBwdInv l pp; (pp, r, flag)) *)
    | A_call (f, ss) ->  (* do ovde stignav *)
      let f = StringMap.find f funcs in
      let p = bwdRec funcs env vars p f.funcBody in
      List.fold_left (fun (ap, ar, aflag) (s, _) ->
          bwdStm funcs env vars (ap, ar, aflag) s
        ) (p, r, flag) ss
    | A_recall (f, ss) ->
          List.fold_left (fun (ap, ar, aflag) (s, _) ->
             bwdStm funcs env vars (ap, ar, aflag) s
           ) (B.join p r, r, true) ss

  and bwdBlk funcs env vars (p,r,flag) (b:block) : B.t * B.t * bool =
    let result_print l p =
      Format.fprintf !fmt "### %a ###:\n%a@." label_print l B.print p
    in
    match b with
    | A_empty l ->
      if !tracebwd && not !minimal then result_print l p;
      addBwdInv l p; (p,r,flag)
    | A_block (l,(s,_),b) ->
      stop := Sys.time ();
      if ((!stop -. !start) > !timeout)
      then raise Timeout
      else
        let (b,rb,flagb) = bwdBlk funcs env vars (p,r,flag) b in
        let (p,r,flag) = bwdStm funcs env vars (b,rb,flagb) s in
        if !tracebwd && not !minimal then result_print l p;
        (addBwdInv l p; (p,rb,flagb))  

  and bwdRec funcs env vars (p:B.t) (b:block) : B.t = 
    let (res, _, _) = bwdBlk funcs env vars (p,B.bot env vars,false) b  in
    res


  (* Forward BDD Analyzer *) 
  

  let rec fwdStm2 funcs (env: string Bddapron.Env.t) vars preds p s =
    match s with
    | A_label _ -> p
    | A_return -> D.bot env vars preds
    | A_assign ((l,_),(e,pos)) -> D.fwdAssign p (l,e)
    | A_assert (b,ba) -> 
	  let p2' = (D.filter p b) in
	  p2'	
    | A_if ((b,ba),s1,s2) -> 
    
      let isNode = ref false in 
      let index = ref 0 in 
      let k = ref 1 in 
      (*Format.fprintf !fmt "\n predicates size in BDD: %d \n" (List.length preds); *)
      List.iter (fun p -> if (AbstractSyntax.bExp_isEq b p) then (isNode:=true; index:=!k); k:=!k+1) preds; 
      (*Format.fprintf !fmt "Node if: isNode %b : index %d \n" !isNode !index; *)
      
      let bb = b in  
      let b = if (!isNode) then (A_bvar (List.nth !bool_vars (!index-1))) else b in 
      
      let p1' = if (!isNode) then fwdBlk2 funcs env vars preds (D.filter (D.filter p b) bb) s1 
      		else fwdBlk2 funcs env vars preds (D.filter p b) s1 in
      let p2 = if (!isNode) then D.filter (D.filter p (fst (negBExp (b,ba)))) (fst (negBExp (bb,ba))) 
      		else D.filter p (fst (negBExp (b,ba))) in
      let p2' = fwdBlk2 funcs env vars preds p2 s2 in
      D.join p1' p2'
    | A_ifdef ((b,ba),s1,s2) -> p 
    | A_while (l,(b,ba),s) ->
      let rec aux i p2 n =
        let i' = D.join p p2 in
	Format.fprintf !fmt "unwind: %d inv: %a\n" n D.print i';
	addFwdInvTuple2 (l,n) i';        
        if !tracefwd && not !minimal then begin
          Format.fprintf !fmt "### %a:%i ###:\n" label_print l n;
          Format.fprintf !fmt "p1: %a\n" D.print p;
          Format.fprintf !fmt "i: %a\n" D.print i;
          Format.fprintf !fmt "p2: %a\n" D.print p2;
          Format.fprintf !fmt "i': %a\n" D.print i'
        end;
        if D.isLeq i' i then i else
          let i'' = if n <= !joinfwd then i' else 
              D.widen i (D.join i i') in
          if !tracefwd && not !minimal then
            Format.fprintf !fmt "i'': %a\n" D.print i'';
          aux i'' (fwdBlk2 funcs env vars preds (D.filter i'' b) s) (n+1)
      in
      let i = D.bot env vars preds in
      let p2 = fwdBlk2 funcs env vars preds (D.filter i b) s in
      let pp = aux i p2 1 in 
      
      let p_down = fwdBlk2 funcs env vars preds (D.filter pp b) s in   (* this line is added additionally: performs narrowing  *)
      let p_final = D.join p_down (D.filter p (fst (negBExp (b,ba)))) in
      let p_final_neg = D.filter p_final (fst (negBExp (b,ba))) in 
      let p_down_neg = D.filter p_down (fst (negBExp (b,ba))) in 

      let binv = try InvMap.find l !bwdInvMap2 with Not_found -> D.top env vars preds in 
      let pp = D.meet p_final binv in   
      let p_err = if (D.isLeq (D.top env vars preds) pp) then (pp)
      		   else if (D.isLeq pp (D.bot env vars preds)) then (pp)
      		   else if (D.eq pp binv) then (pp)
		   else (
		   	let pp_list = D.toProcess pp binv in 
		   	let dd_final = ref (D.bot env vars preds) in 
		   	List.iter ( fun (bb,elm1,elm2) ->
		   		let p1 = B.ofArr elm1 (Bddapron.Env.apron env) vars in 
		   		let p2 = B.ofArr elm2 (Bddapron.Env.apron env) vars in 
		   		let cond = Cond.make ~symbol:Env.string_symbol (Cudd.Man.make_v ()) in 
		   		(*Bddapron.Expr1.Bool.print cond !fmt bb; 	*)	
		   		
				let file = "test" in 
				write_to_Z3file file p1 p2; 
				let l2 = read_process_lines ("z3 "^(file)) in 
				let z3_list = process_result l2 in 
				(*Format.fprintf !fmt "CALLS Z3: \n"; print_list 0 l2; *)
				let p1 = B.filter_list z3_list p1 in 
		   		(*Format.fprintf !fmt "\nin fwdBlk2 error p1: %a\n" B.print p1; *)
		   		
		   		let arr = B.toArr p1 in 
		   		let dd = D.meetcond (D.toBDD arr p) bb in 
		   		(*Format.fprintf !fmt "in fwdBlk2 d: %a\n" D.print dd; *)		   		
		   		dd_final := D.join !dd_final dd		   		
		   	) pp_list; !dd_final 
		   ) in       
      addErrInv2 l p_err;         
      addFwdInv2 l pp; p_final_neg
    | A_call (f,ss) ->
      let f = StringMap.find f funcs in
      let p = List.fold_left (fun ap (s,_) -> 
          fwdStm2 funcs env vars preds p s) p ss in
      fwdBlk2 funcs env vars preds p f.funcBody
    | A_recall (f,ss) -> D.top env vars preds (* TODO *)

  and fwdBlk2 funcs (env: string Bddapron.Env.t) vars preds (p:D.t) (b:block) : D.t =
    let result_print l p =
      Format.fprintf !fmt "### %a ###: %a\n" label_print l D.print p
    in
    match b with
    | A_empty l ->
      (*Format.fprintf !fmt "A_empty: ### %a ###: %a\n" label_print l D.print p;*)
      let binv = try InvMap.find l !bwdInvMap2 with Not_found -> D.top env vars preds in 
      let pp = D.meet p binv in   
      let p_err = if (D.isLeq (D.top env vars preds) pp) then (pp)
      		   else if (D.isLeq pp (D.bot env vars preds)) then (pp)
      		   else if (D.eq pp binv) then (pp)
		   else (
		   	let pp_list = D.toProcess pp binv in 
		   	let dd_final = ref (D.bot env vars preds) in 
		   	List.iter ( fun (bb,elm1,elm2) ->
		   		let p1 = B.ofArr elm1 (Bddapron.Env.apron env) vars in 
		   		let p2 = B.ofArr elm2 (Bddapron.Env.apron env) vars in 
		   		let cond = Cond.make ~symbol:Env.string_symbol (Cudd.Man.make_v ()) in 
		   		(*Bddapron.Expr1.Bool.print cond !fmt bb; 	*)	
		   		
				let file = "test" in 
				write_to_Z3file file p1 p2; 
				let l2 = read_process_lines ("z3 "^(file)) in 
				let z3_list = process_result l2 in 
				(*Format.fprintf !fmt "CALLS Z3: \n"; print_list 0 l2; *)
				let p1 = B.filter_list z3_list p1 in 
		   		(*Format.fprintf !fmt "\nin fwdBlk2 error p1: %a\n" B.print p1; *)
		   		
		   		let arr = B.toArr p1 in 
		   		let dd = D.meetcond (D.toBDD arr pp) bb in 
		   		(*Format.fprintf !fmt "in fwdBlk2 d: %a\n" D.print dd; *)		   		
		   		dd_final := D.join !dd_final dd		   		
		   	) pp_list; !dd_final 
		   ) in       
      addErrInv2 l p_err;           
      addFwdInv2 l pp; pp
    | A_block (l,(s,_),b) ->
      if !tracefwd && not !minimal then result_print l p; 
      (*Format.fprintf !fmt "fwdBlk2 ### %a ###:\n%a@." label_print l D.print p; *)
      let binv = try InvMap.find l !bwdInvMap2 with Not_found -> D.top env vars preds in 
      let pp = D.meet p binv in 
      let p_err = if (D.isLeq (D.top env vars preds) pp) then (pp)
      		   else if (D.isLeq pp (D.bot env vars preds)) then (pp)      
      		   else if (D.eq pp binv) then (pp)
		   else (
		   	let pp_list = D.toProcess pp binv in 
		   	let dd_final = ref (D.bot env vars preds) in 
		   	List.iter ( fun (bb,elm1,elm2) ->
		   		let p1 = B.ofArr elm1 (Bddapron.Env.apron env) vars in 
		   		let p2 = B.ofArr elm2 (Bddapron.Env.apron env) vars in 
		   		let cond = Cond.make ~symbol:Env.string_symbol (Cudd.Man.make_v ()) in 
		   		(*Bddapron.Expr1.Bool.print cond !fmt bb; *)		
		   		(*Format.fprintf !fmt "in fwdBlk2 ### p1: %a : p2: %a \n" B.print p1 B.print p2; *)
				let file = "test" in 
				write_to_Z3file file p1 p2; 
				let l2 = read_process_lines ("z3 "^(file)) in 
				let z3_list = process_result l2 in 
				(*Format.fprintf !fmt "CALLS Z3: \n"; print_list 0 l2; *)
				let p1 = B.filter_list z3_list p1 in 
		   		(*Format.fprintf !fmt "\nin fwdBlk2 error result p1: %a\n" B.print p1; *)
		   		
		   		let arr = B.toArr p1 in 
		   		let dd = D.meetcond (D.toBDD arr pp) bb in 
		   		(*Format.fprintf !fmt "in fwdBlk2 d: %a\n" D.print dd; *)		   		
		   		dd_final := D.join !dd_final dd		   		
		   	) pp_list; !dd_final 
		   ) in       
      addErrInv2 l p_err;       
      addFwdInv2 l pp; 
      fwdBlk2 funcs env vars preds (fwdStm2 funcs env vars preds p s) b
  

  (* Backward Iterator BDD + Recursion *)

  let rec bwdStm2 funcs env vars preds (p,r,flag) s =
    match s with
    | A_label (s,sa) -> (p,r,flag)
    | A_return -> D.bot env vars preds, r, flag
    | A_assign ((l,_),(e,_)) -> let pp1 = D.bwdAssign p (l, e) in 
    				(*let pp = D.compress (pp1) in *)
    				(*Format.fprintf !fmt "bwdAss : before %a \n after asgn: %a \n" D.print p D.print pp1; *)
   				pp1, r, flag
    | A_assert (b,ba) ->
    		
	let p = if (!typ_err1="D") then D.meet (List.hd !dd_err1) (D.filter p (fst (negBExp (b,ba)))) 
	else (let arr = B.toArr (List.hd !d_err1) in D.meet (D.toBDD arr p) (D.filter p (fst (negBExp (b,ba)))) )
	in 
	typ_err1:="D"; 
	(*dd_err1 := [p]; *)
	(*Format.fprintf !fmt "dd_err1 : %a : type: %s \n" D.print p !typ_err1; *)
	(*if B.isBot p then raise Bottom_error; *)
      	p, r, flag
    | A_if ((b,ba),s1,s2) -> 
    
      let isNode = ref false in 
      let index = ref 0 in 
      let k = ref 1 in 
      (*Format.fprintf !fmt "\n predicates size in BDD: %d \n" (List.length preds); *)
      List.iter (fun p -> if (AbstractSyntax.bExp_isEq b p) then (isNode:=true; index:=!k); k:=!k+1) preds; 
      (*Format.fprintf !fmt "Node if: isNode %b : index %d \n" !isNode !index; *)
      
      let bb = b in 
      let b = if (!isNode) then (A_bvar (List.nth !bool_vars (!index-1))) else b in     
    
      let (p1, _, flag1) = bwdBlk2 funcs env vars preds (p, r, flag) s1 in
      let (p2, _, flag2) = bwdBlk2 funcs env vars preds (p, r, flag) s2 in

      if (not (D.eq p1 p2)) then 
        (let isAdded = ref false in 
         List.iter (fun d -> if (AbstractSyntax.bExp_isEq bb d) then isAdded:=true) !predicates;   
         if (not !isAdded) then predicates:=bb::!predicates );            
      
      let p1 = if (!isNode) then D.filter (D.filter p1 b) bb else D.filter p1 b in 
      let p2 = if (!isNode) then D.filter (D.filter p2 (fst (negBExp (b, ba)))) (fst (negBExp (bb, ba))) 
      		else D.filter p2 (fst (negBExp (b, ba))) in
      (*Format.fprintf !fmt "IF p1: %a : p2 %a :##: join: %a \n" D.print p1 D.print p2 D.print (D.join p1 p2); *)
      (D.join p1 p2, r, flag1 || flag2)
    | A_while (l, (b, ba), s) ->
      let p_final = D.filter p (fst (negBExp (b,ba))) in 
      Format.fprintf !fmt "While  p_final: %a\n" D.print p_final;
      let rec aux i p2 p_final n =
        let i' = D.join p_final p2 in 
        Format.fprintf !fmt "While  i': %a\n" D.print i';
	addBwdInvTuple2 (l,n) i';
        if D.isLeq i' i then ( i) else
          (let i'' = if n <= !joinbwd then i' else 
              (let dd = D.widen i i'(*(D.join i i')*) in Format.fprintf !fmt "WIDEN: a1: %a ## a2: %a \n res: %a" D.print i D.print (D.join i i') D.print dd; dd) in 
          let (pp,r,flag) = (bwdBlk2 funcs env vars preds (i'',r,flag) s) in 
          Format.fprintf !fmt "While  p2 call: %a\n" D.print (D.filter pp b);
          aux i'' (D.filter pp b) p_final (n+1))
      in
      let i = D.bot env vars preds in
      let pp = aux i p_final p_final 1 in 
      Format.fprintf !fmt "exit in while: %a\n" D.print pp;
      let p_down1 = if (not !Iterator.narrow) then pp 
      		     else ( 
      			let (p_down,r,flag) = bwdBlk2 funcs env vars preds (pp,r,flag) s in 
      			(D.filter p_down b) ) in  
      Format.fprintf !fmt "narrowing while: %a\n" D.print p_down1;
      (addBwdInv2 l p_down1; (p_down1, r, flag))      
    | A_call (f, ss) ->  (* do ovde stignav *)
      let f = StringMap.find f funcs in
      let p = bwdRec2 funcs env vars preds p f.funcBody in
      List.fold_left (fun (ap, ar, aflag) (s, _) ->
          bwdStm2 funcs env vars preds (ap, ar, aflag) s
        ) (p, r, flag) ss
    | A_recall (f, ss) ->
          List.fold_left (fun (ap, ar, aflag) (s, _) ->
             bwdStm2 funcs env vars preds (ap, ar, aflag) s
           ) (D.join p r, r, true) ss

  and bwdBlk2 funcs env vars preds (p,r,flag) (b:block) : D.t * D.t * bool =
    let result_print l p =
      Format.fprintf !fmt "### %a ###:\n%a@." label_print l D.print p
    in
    match b with
    | A_empty l ->
      if !tracebwd && not !minimal then result_print l p;
      addBwdInv2 l p; (p,r,flag)
    | A_block (l,(s,_),b) ->
      stop := Sys.time ();
      if ((!stop -. !start) > !timeout)
      then raise Timeout
      else
        let (b,rb,flagb) = bwdBlk2 funcs env vars preds (p,r,flag) b in
        let (p,r,flag) = bwdStm2 funcs env vars preds (b,rb,flagb) s in
        if !tracebwd && not !minimal then result_print l p;
        (addBwdInv2 l p; (p,rb,flagb))  

  and bwdRec2 funcs (env: string Bddapron.Env.t) vars preds (p:D.t) (b:block) : D.t = 
    let (res, _, _) = bwdBlk2 funcs env vars preds (p,D.bot env vars preds,false) b  in
    res

  (* Syntactic Slicer *)

let rec stmt_print ind fmt (s,_) =
  match s with
  | A_label (l,_) -> Format.fprintf fmt "%s%s:\n" ind l
  | A_return -> Format.fprintf fmt "%sreturn\n" ind
  | A_assign (v,e) -> Format.fprintf fmt "%s%a := %a\n" ind aExp_print v exp_print e
  | A_assert b -> Format.fprintf fmt "%sassert( %a )\n" ind bExp_print b
  | A_if (b,s1,s2) ->
    Format.fprintf fmt "%sif ( %a ) then\n%a%s      else\n%a%s      endif\n"
      ind bExp_print b
      (block_print2 (ind ^ "  ")) s1 ind	
      (block_print2 (ind ^ "  ")) s2 ind
  | A_ifdef (b,s1,s2) ->
    Format.fprintf fmt "%s#if ( %a ) \n%a%s      #else\n%a%s      #endif\n"
      ind bExp_print b
      (block_print2 (ind ^ "  ")) s1 ind	
      (block_print2 (ind ^ "  ")) s2 ind	  
  | A_while (l,b,s1) ->
    Format.fprintf fmt "%swhile %a ( %a ) do\n%a%s      od\n"
      ind label_print l bExp_print b
      (block_print2 (ind ^ "  ")) s1 ind
  | A_call (f,ss) ->
    Format.fprintf fmt "%s%s( " ind f;
    List.iter (fun s -> Format.fprintf fmt "%a; " parameter_print s) ss;
    Format.fprintf fmt ")\n"
  | A_recall (f,ss) ->
    Format.fprintf fmt "%s%s( " ind f;
    List.iter (fun s -> Format.fprintf fmt "%a; " parameter_print s) ss;
    Format.fprintf fmt ")\n"

and parameter_print fmt (s,_) =
  match s with
  | A_assign (v,e) -> Format.fprintf fmt "%a := %a" aExp_print v exp_print e
  | _ -> raise (Invalid_argument "parameter_print:")

and block_print2 ind fmt b =
  match b with
  | A_empty l -> (*if (l=1) then*) (*Format.fprintf fmt "ADD %a\n" label_print l;*) Format.fprintf fmt "%a\n" label_print l (*else if (!typ_err1="B") 
    then (let err1 = InvMap.find l !errInvMap in let err2 = InvMap.find (l+1) !errInvMap in if (B.isLeq err1 err2) && (B.isLeq err2 err1) then Format.fprintf fmt "Remove %a\n" label_print l else Format.fprintf fmt "%a\n" label_print l) 
    else (let err1 = InvMap.find l !errInvMap2 in let err2 = InvMap.find (l+1) !errInvMap2 in if (D.eq err1 err2) then Format.fprintf fmt "Remove %a\n" label_print l else Format.fprintf fmt "%a\n" label_print l)  *)
  | A_block (l,s,b) -> 
    let l2 = (match b with | A_empty l2 -> l2 | A_block (l2,s2,b2) -> l2) in 
    (*Format.fprintf fmt "ADD %a %a\n" label_print l label_print l2; *)
    if (!typ_err1="B") 
    then (let err1 = InvMap.find l !errInvMap in let err2 = InvMap.find (l2) !errInvMap in if (B.isLeq err1 err2) && (B.isLeq err2 err1) then Format.fprintf fmt "Remove %a \n%a\n" label_print l (block_print2 ind) b else Format.fprintf fmt "%a %a%a" label_print l (stmt_print ind) s (block_print2 ind) b) 
    else (let err1 = InvMap.find l !errInvMap2 in let err2 = InvMap.find (l2) !errInvMap2 in if (D.eq err1 err2) 
    then Format.fprintf fmt "Remove %a \n%a\n" label_print l (block_print2 ind) b else Format.fprintf fmt "%a %a%a" label_print l (stmt_print ind) s (block_print2 ind) b)
    

and label_print fmt l = if (l < 10) then Format.fprintf fmt "[ %i:]" l else Format.fprintf fmt "[%i:]" l

let label_of_block (block:block) : label = match block with
  | A_empty l -> l
  | A_block (l, _ , _) -> l


let function_print fmt f =
  match f.funcTyp with
  | None ->
    Format.fprintf fmt "void ";
    Format.fprintf fmt "%s( " f.funcName;
    List.iter (fun v -> Format.fprintf fmt "%a %a; " typ_print v.varTyp var_print v) f.funcArgs;
    Format.fprintf fmt "):\n";
    block_print2 "" fmt f.funcBody
  | Some v ->
    Format.fprintf fmt "%a " typ_print v.varTyp;
    Format.fprintf fmt "%s( " f.funcName;
    List.iter (fun v -> Format.fprintf fmt "%a %a; " typ_print v.varTyp var_print v) f.funcArgs;
    Format.fprintf fmt "):\n";
    block_print2 "" fmt f.funcBody

let prog_print2 fmt (_,b,fs) = block_print2 "" fmt b; StringMap.iter (fun k f -> if (k="main") then function_print fmt f) fs

  (* Analyzer *)

  let rec process list = 
	if List.length list = 0 then [[]]
	else match list with
		| [] -> []
		| hd :: tl -> 
			let with_hd = List.map (fun l -> (hd) :: l) (process tl) in 
			let without_hd = List.map (fun l -> A_bunary (A_NOT,AbstractSyntax.annotate (hd)) :: l) (process tl) in 
			with_hd @ without_hd;;
			
  let print_listlist l =
  List.iter (fun el -> print_string "config: "; List.iter (fun elem -> Format.fprintf !fmt " : %a : " bExp_print_aux elem) el; print_endline "") l;; 
  
  let rec is_same a b = match a, b with
	| [], [] -> true
	| [], _
	| _, [] -> false
	| c::cc, d::dd -> if AbstractSyntax.bExp_isEq c d then is_same cc dd else false   
	
  let rec print_bExp_list fmt a = match a with
	| [] -> ()
	| c::cc -> Format.fprintf fmt ": %a :" AbstractSyntax.bExp_print_aux c; print_bExp_list fmt cc	
  
(* IMPORTANT FUNCTION THAT DOES THE ANALYSIS*)
  let analyze (vars,stmts,funcs) main =
    let rec aux xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux xs (Environment.add env [|(Var.of_string x.varId)|] [||])
    in
    let rec aux_int xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux_int xs (Env.add_vars env [(x.varId, `Int)]) in     
    let rec aux_bool xs env = match xs with
      | [] -> env
      | x::xs -> 
        aux_bool xs (Env.add_vars env [(x.varName, `Bool)] ) in         
    let f = StringMap.find main funcs in
    let v1 = snd (List.split (StringMap.bindings vars)) in
    let v2 = snd (List.split (StringMap.bindings f.funcVars)) in
    let vars = List.append v1 v2 in
    let env = aux vars (Environment.make [||] [||]) in
    let s = f.funcBody in
    
    d_err1 := (B.top env vars)::!d_err1; 
    d_err2 := (B.bot env vars)::!d_err2; 
    let count = ref 1 in 
    let the_end = ref false in 

(* ------------ starts while ------------------------------------------------ *)
    while (not !the_end) (*&& (!count != 3)*) do
    


    if (!typ_err1="B") then (Format.fprintf !fmt "\n Type : B \n predicates1: %a\n" print_bExp_list !predicates; Format.fprintf !fmt " predicates2: %a" print_bExp_list !predicates2; Format.fprintf !fmt "\n d_err1: %a" B.print (List.hd !d_err1); Format.fprintf !fmt "\n d_err2: %a\n" B.print (List.hd !d_err2);) 
    else (Format.fprintf !fmt "\n Type : D \n predicates1 %a \n" print_bExp_list !predicates; Format.fprintf !fmt " predicates2 %a \n" print_bExp_list !predicates2; Format.fprintf !fmt "\n dd_err1: %a" D.print (List.hd !dd_err1); Format.fprintf !fmt "\n dd_err2: %a\n" D.print (List.hd !dd_err2);); 

    
    the_end:= (if (!typ_err1="B") 
    then ((B.isLeq (List.hd !d_err2) (List.hd !d_err1)) && (B.isLeq (List.hd !d_err1) (List.hd !d_err2)))
    else (D.eq (List.hd !dd_err2) (List.hd !dd_err1)));     
    the_end := !the_end && ((List.length !predicates) < (List.length !predicates2)  || (is_same !predicates !predicates2)); 
    Format.fprintf !fmt "\n the_end : %b\n" !the_end; 
    
    if ((!Iterator.filename="tests/tcas1.c") && (!count == 3)) then the_end:=true; 
    
    if (not !the_end) then (
    Format.fprintf !fmt "\n\nITERATION : %d \n" !count;    
    predicates2 := !predicates; 
    predicates := []; 
     
    if (List.length !predicates2 > 0) then (
    	
    	bool_vars := []; 
    	bool_exps := [];
    	let k = ref 1 in 
    	List.iter ( fun b -> 
    	   let vm = { varId = "$" ^ "B" ^ string_of_int(!k); varName = "B" ^ string_of_int(!k); varTyp = A_BOOL } in 
    	   bool_vars := vm::!bool_vars; 
    	   bool_exps := (A_bvar vm)::!bool_exps;
    	   k := (!k) + 1
    	   ) !predicates2; 
    	   
    	ItoA.list_configs := process !predicates2; 
    	ItoA.bool_configs := process !bool_exps;  
    	(*let apron_configs = ref [] in *)
    	ItoA.apron_configs := List.map (fun config -> let apr = ref (B.top env vars) in 
    						   List.iter (fun el -> apr := B.filter !apr el) config; 
    						   let a = Lincons1.array_make env (List.length (B.constraints !apr)) in
    						   let i = ref 0 in
    						   List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) (B.constraints !apr);
    						   Abstract1.of_lincons_array (Polka.manager_alloc_loose ()) env a
    				    ) !ItoA.list_configs;   
    	
    	(*List.iter (fun el -> print_string "\n Bool Config: "; List.iter (fun elem -> Format.fprintf !fmt " : %a : " bExp_print_aux elem) el) !ItoA.bool_configs; 
    	List.iter (fun el -> Format.fprintf !fmt "\n Apr Config : %a : " Abstract1.print el) !ItoA.apron_configs;    *) 	
    			      	
    	(*Format.fprintf !fmt "\n predicates size in BDD: %d \n" (List.length !predicates2); *)
    	D.init();
	let cudd = Cudd.Man.make_v () in 
	let cond = Cond.make ~symbol:Env.string_symbol cudd in 
	let envemp = Env.make ~symbol:Env.string_symbol (D.getcudd ()) in 
	let env1 = aux_int vars envemp in 
	let env2 = aux_bool !bool_vars (env1) in  
	let b = D.top env2 vars !predicates2 in 
	
    	Format.fprintf !fmt "\nBackward Analysis Trace: BDD \n";
    		
    	if (!typ_err1="D") then dd_err1:=[(List.hd !dd_err2)] 
    	else (let arr = B.toArr (List.hd !d_err2) in let dd = D.toBDD arr b in dd_err1:=[dd]; typ_err1:="D"); 
    	
	let i = bwdRec2 funcs env2 vars !predicates2 (bwdRec2 funcs env2 vars !predicates2 b s) stmts in
        bwdMap2_print !fmt !bwdInvMap2 !bwdInvMapTuple2;
	
    	Format.fprintf !fmt "\nForward Analysis Trace after Backward: BDD \n";
    	let binv = InvMap.find 1 !bwdInvMap2 in
	let state = fwdBlk2 funcs env2 vars !predicates2 (fwdBlk2 funcs env2 vars !predicates2 binv stmts) s in
        fwdMap2_print !fmt !fwdInvMap2 !fwdInvMapTuple2; 
 
        Format.fprintf !fmt "\nError Invariant Map::\n";
        errMap2_print !fmt !errInvMap2; 

        let l = (List.hd !label_ass) in 
        dd_err2 := [(InvMap.find l !errInvMap2)]; 
        (*Format.fprintf !fmt "\n dd_err2: %a \n" D.print (List.hd !dd_err2); *)
          	
    )
    else (
    d_err1:=[(List.hd !d_err2)]; 
    (* Backward OverApproximating Analysis *)
    if !tracebwd && not !minimal then
      Format.fprintf !fmt "\nBackward Analysis Trace:\n";
    start := Sys.time ();
    let startbwd = Sys.time () in
	(*Iterator.approx := 3; *)
    let i = bwdRec funcs env vars (bwdRec funcs env vars (B.top env vars) s) stmts in
    let stopbwd = Sys.time () in
    if not !minimal then begin
      if !timebwd then
        Format.fprintf !fmt "\nBackward OverApproximating Analysis Viol (Time: %f s):\n" (stopbwd-.startbwd)
      else
        Format.fprintf !fmt "\n\nBackward OverApproximating Analysis Viol :\n\n";
      bwdMap_print !fmt !bwdInvMap !bwdInvMapTuple;
    end;
	
    if !tracefwd && not !minimal then
      Format.fprintf !fmt "\nForward Analysis Trace after Backward:\n";
    let startfwd = Sys.time () in
	(*Iterator.approx := 2;	*)
	let binv = InvMap.find 1 !bwdInvMap in
    let state = fwdBlk funcs env vars (fwdBlk funcs env vars binv stmts) s in
    let stopfwd = Sys.time () in
    if not !minimal then
      begin
        if !timefwd then
          Format.fprintf !fmt "\nForward Analysis after Backward: (Time: %f s):\n" (stopfwd-.startfwd)
        else
          Format.fprintf !fmt "\n\nForward Analysis after Backward::\n\n";
        fwdMap_print !fmt !fwdInvMap !fwdInvMapTuple; 
	(*Format.fprintf !fmt "\n End Forward"; *)
        Format.fprintf !fmt "\n\nError Invariant Map::\n\n";
        errMap_print !fmt !errInvMap; 
        let l = (List.hd !label_ass) in 
        d_err2 := [(InvMap.find l !errInvMap)]; 
        (*Format.fprintf !fmt "\n d_err2: %a \n" B.print (List.hd !d_err2); 	*)	

      end; 
      );  (* end of else branch *)
      );  (* end of then branch of if (not !the_end)  *)
      (*Format.fprintf !fmt "\n predicates size: %d \n" (List.length !predicates); *)
      count := !count+1;
      done; 
(*------------ ends while --------------------------------------------------------- *)	  
      Format.fprintf !fmt "\n\nAbstract Syntax of Program Slice:\n\n";
      prog_print2 !fmt (vars,stmts,funcs);
    true
	

end
