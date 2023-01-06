(***************************************************)
(*                                                 *)
(*    Forward/Backward Single Analysis Iterator    *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open InvMap
open Apron
open Iterator
open Partition 
(*open Yices*)

module SingleAnalysisIterator (B: PARTITION) =
struct

  	module B = B  	
	module InvMapTuple = Map.Make(struct type t=label*int let compare=compare end)

	(* exceptions *)
	exception Bottom_error

	let d_err1 = ref [] 
	let d_err2 = ref [] 	
	let predicates = ref [] 
  	let bool_vars : var list ref = ref [] 
  	let bool_exps : bExp list ref = ref []

	
	let bwdInvMapTuple = ref InvMapTuple.empty
	let addBwdInvTuple (l,n) (a:B.t) = bwdInvMapTuple := InvMapTuple.add (l,n) a !bwdInvMapTuple		

  	let bwdInvMap = ref InvMap.empty
  	let addBwdInv l (a:B.t) = bwdInvMap := InvMap.add l a !bwdInvMap

  	let bwdMap_print fmt m1 m2 = let sr = Stack.create () in
						InvMap.iter (fun l a -> Stack.push l sr) m1;
						Stack.iter (fun l -> if InvMapTuple.mem (l,!joinbwd) m2 then (  Format.fprintf fmt "%a unwind >%d: %a\n" label_print l (!joinbwd-1) B.print (InvMapTuple.find (l,!joinbwd) m2);
						for i = !joinbwd-1 downto 1 do Format.fprintf fmt "%a unwind %d: %a\n" label_print l i B.print (InvMapTuple.find (l,i) m2) done; Format.fprintf fmt "%a unwind 0: %a\n" label_print l B.print (InvMap.find l m1)	) else Format.fprintf fmt "%a: %a\n" label_print l B.print (InvMap.find l m1) ) sr




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
		(*d_err1 := [p];*)
		(* Format.fprintf !fmt "ASSERT p_neg : %a : p: %a \n" B.print p_neg B.print p; *)
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
        if (!Iterator.filename="tests/final/tcas1.c") then 
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
(let err1 = InvMap.find l !bwdInvMap in let err2 = InvMap.find (l2) !bwdInvMap in 
if (B.isLeq err1 err2) && (B.isLeq err2 err1) then 
(match s with | (A_if (bb,s1,s2),_) -> let l3 = (match s1 with | A_empty l3 -> l3 | A_block (l3,s3,b3) -> l3) in 
				   let err3 = InvMap.find (l3) !bwdInvMap in 
				   if (B.isLeq err1 err3) && (B.isLeq err3 err1) 
				   then Format.fprintf fmt "Remove %a \n%a\n" label_print l (block_print2 ind) b
				   else Format.fprintf fmt "%a %a%a" label_print l (stmt_print ind) s (block_print2 ind) b 
	       | _ -> Format.fprintf fmt "Remove %a \n%a\n" label_print l (block_print2 ind) b ) 
 else Format.fprintf fmt "%a %a%a" label_print l (stmt_print ind) s (block_print2 ind) b) 
    

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
       
    let f = StringMap.find main funcs in
    let v1 = snd (List.split (StringMap.bindings vars)) in
    let v2 = snd (List.split (StringMap.bindings f.funcVars)) in
    let vars = List.append v1 v2 in
    let env = aux vars (Environment.make [||] [||]) in
    let s = f.funcBody in
    
    d_err1 := (B.top env vars)::!d_err1; 
    d_err2 := (B.bot env vars)::!d_err2; 

    (* Backward OverApproximating Analysis *)
    if !tracebwd && not !minimal then
      Format.fprintf !fmt "\nBackward Analysis:\n";
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
	
	  
      Format.fprintf !fmt "\n\nAbstract Syntax of Program Slice:\n\n";
      prog_print2 !fmt (vars,stmts,funcs);
    true
	

end
