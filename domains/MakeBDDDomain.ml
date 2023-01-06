(***************************************************)
(*                                                 *)
(*             MakeBDDDomain.ml                    *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open BDDDomain
open Bddapron
open Apron
open AbstractSyntax
open Constraints

module type BDDAPRON_PARAM = sig
  type lib
  val manager: lib Manager.t
end

module BDDAPRON_DOMAIN(Param: BDDAPRON_PARAM) : BDDDomain =
  struct

    let apron = Polka.manager_alloc_loose ()
    let man = Bdddomain1.make_man apron

    type domain = (string, Polka.loose Polka.t) Bddapron.Bdddomain1.t
    type env = string Bddapron.Env.t
	
    type apron_expr = string Bddapron.Expr1.Apron.t
    type bool_expr = string Bddapron.Expr1.Bool.t
    type bint_expr = string Bddapron.Expr1.Bint.t
    type expr = string Bddapron.Expr1.t
    type label = int

	type t = {
    	dom : domain; (* representation as list of Partition elements *)
    	env : env; (* APRON environment *)
    	vars : var list; (* list of variables in the APRON environment *)	
	nodes : AbstractSyntax.bExp list; (* list of boolean variables in the BDD environmet *)	
	}
	
    let init () = 
      Cudd.Man.print_limit := 10000; 
      Cudd.Man.set_gc 10000
        (begin fun () -> Format.printf "@.CUDD BLI GC@." end)
        (begin fun () -> Format.printf "@.CUDD REORDER@." end);;

    let cudd = Cudd.Man.make_v ()
    let cond = Cond.make ~symbol:Env.string_symbol cudd
    (*let env = Env.make ~symbol:Env.string_symbol cudd*)


    let mkenv () =  Env.make ~bddsize:1000 ~symbol:Env.string_symbol ~relational:true cudd
    let empty () = Bdddomain1.top man (Env.make ~symbol:Env.string_symbol cudd)

  	(** The current element of BDDDomain. *)
  	let dom d: domain = d.dom
  	(** The current APRON environment. *)
  	let env d = d.env
  	(** The current list of variables in the APRON and BDD environment. *)
  	let vars d = d.vars
  	let nodes d = d.nodes

    let bool_var env x = Expr1.Bool.var env cond x
    let bool_and x y = Expr1.Bool.dand cond x y
    let bool_or x y = Expr1.Bool.dor cond x y
    let bool_not x  = Expr1.Bool.dnot cond x
    let bool_eq x y = Expr1.Bool.eq cond x y
    let bool_true env = Expr1.Bool.dtrue env cond
    let bool_false env = Expr1.Bool.dfalse env cond
    let bool_print fmt e = Expr1.Bool.print cond fmt e
    let bool_expr e = Expr1.Bool.to_expr e
    
  	let bot e vs exp = {
    	dom = Bdddomain1.bottom man e;
    	env = e;
    	vars = vs;	
	nodes = exp
  	}	

  	let top e vs exp = 
		let rec aux vs cs = match vs with
		| [] -> (*Format.fprintf Format.std_formatter "end_top";*) cs
		| x::xs ->   match x.varTyp with
  			| A_INT | A_BOOL -> aux xs cs
  			| A_UINT ->  (* Format.fprintf Format.std_formatter "%a %s{%s}\n" typ_print x.varTyp x.varId x.varName; *)
						  let cons = Lincons1.make (Linexpr1.make (Bddapron.Env.apron e)) Lincons1.SUPEQ in
  							Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string x.varId)) |] None; 
						 (*Lincons1.print Format.std_formatter cons;*) aux xs (cons::cs) 
   		in (*Format.fprintf Format.std_formatter "begin_top\n";*) let cs = aux vs [] in
		let ar_cs = Lincons1.array_make (Bddapron.Env.apron e) (List.length cs) in
    	let i = ref 0 in
    	List.iter (fun c -> Lincons1.array_set ar_cs !i c; i := !i + 1) cs;
		(*Lincons1.array_print Format.std_formatter ar_cs;*)
	{
    	dom = Bdddomain1.of_apron man e (Abstract1.of_lincons_array apron (Bddapron.Env.apron e) ar_cs); (*Bdddomain1.top man e;*)
    	env = e;
    	vars = vs; 	
	nodes = exp
  	}	

  	let inner e vs exp el = {
    	dom = el;
    	env = e;
    	vars = vs; 
	nodes = exp
  	}
  
    let isBot d = Bdddomain1.is_bottom man d.dom	
    let eq d1 d2 = Bdddomain1.is_eq man d1.dom d2.dom
    let isLeq d1 d2 = Bdddomain1.is_leq man d1.dom d2.dom
	
    let print fmt d =   (* Format.printf "%a@." (fun fmt x -> Bdddomain1.print fmt x) d.dom *)
		let ll = Bdddomain1.to_bddapron man d.dom in 
		if (List.length ll = 0) then (if (Bdddomain1.is_bottom man d.dom) then Format.fprintf fmt "bottom"; 
						if (Bdddomain1.is_top man d.dom) then Format.fprintf fmt "top" );
		let first = ref true in 
		List.iter (fun elem -> let elem1 = fst elem in if !first then ((bool_print fmt elem1); Format.fprintf fmt " Bool| && ";)
			else (Format.fprintf fmt " ||  "; (Expr1.Bool.print cond fmt (fst elem)); Format.fprintf fmt " Bool| && ";);
								let c = Apron.Abstract1.to_lincons_array apron (snd elem) in 
								let cs = ref [] in 
								for i=0 to (Lincons1.array_length c)-1 do
									cs:=(Lincons1.array_get c i)::!cs;
								done; first := false;
								match !cs with
    								| [] -> Format.fprintf fmt "top"
    								| x::_ ->
      									if (Constraint.isBot x) then Format.fprintf fmt "bottom" else
        								let i = ref 1 and l = List.length !cs in
        								List.iter (fun c ->
            								Constraint.print d.vars fmt c;
            								if (!i = l) then () else Format.fprintf fmt " && ";
            								i := !i + 1
          								) !cs
		) ll
		
    let getenv dom = Bdddomain1.get_env dom
    let getcudd () = cudd

    let toProcess d1 d2 = 
 	let env = d1.env in
    	let vars = d1.vars in 
	let nodes = d1.nodes in     
	let ll1 = Bdddomain1.to_bddapron man d1.dom in     
	List.map (fun (elm11,elm12) -> let dd2 = Bdddomain1.meet_condition man cond d2.dom elm11 in 
					 let ll2 = Bdddomain1.to_bddapron man dd2 in 
					 let (elm21,elm22) = (List.hd ll2) in 					  
					 (elm11,Apron.Abstract1.to_lincons_array apron elm12, Apron.Abstract1.to_lincons_array apron elm22)
	   ) ll1 


    let meetcond d c = 
 	let env = d.env in
    	let vars = d.vars in 
	let nodes = d.nodes in     
	let dd2 = Bdddomain1.meet_condition man cond d.dom c in 
	{ dom = dd2; env = env; vars = vars; nodes = nodes }
 

    let toBDD arr d = 
 	let env = d.env in
    	let vars = d.vars in 
	let nodes = d.nodes in 
	
	let apron = Abstract1.of_lincons_array apron (Bddapron.Env.apron env) arr in 
	let man_apron = Abstract1.manager apron in 
	let env_apron = Abstract1.env apron in 
	
	let k = ref 0 in 
	let index = ref 0 in 
	let list_bdd = List.map2 ( fun configBexp configApron -> 
      			let bexp1 = ref (List.hd configBexp) in
      			if (List.length configBexp > 1) then (
    			    for i=1 to (List.length configBexp)-1 do
      				bexp1 := A_bbinary (A_AND,annotate !bexp1,annotate (List.nth configBexp i)); 
      			    done 
      			);   
      			let b = bExp_to_bddapron env cond !bexp1 in 
      			(b,Abstract1.meet man_apron apron configApron)
      		) !ItoA.bool_configs !ItoA.apron_configs in 		
		
		let apron = List.nth !ItoA.apron_configs !index in 
	let res = Bdddomain1.of_bddapron man env list_bdd in 
	
	(*let dom = Bdddomain1.of_apron man env (Abstract1.of_lincons_array apron (Bddapron.Env.apron env) arr) in*)
	{ dom = res; env = env; vars = vars; nodes = nodes }	   

    let join d1 d2 = 
    	let dom = Bdddomain1.join man d1.dom d2.dom in 
	let env = d1.env in
    	let vars = d1.vars in 
	let nodes = d1.nodes in
	{ dom = dom; env = env; vars = vars; nodes = nodes }		
	
	
    let meet d1 d2 =  
    	let dom = Bdddomain1.meet man d1.dom d2.dom in 
	let env = d1.env in
    	let vars = d1.vars in 
	let nodes = d1.nodes in
	{ dom = dom; env = env; vars = vars; nodes = nodes }		
	
	
    let widen d1 d2 =
    	let dom = Bdddomain1.widening man d1.dom d2.dom in 
	let env = d1.env in
    	let vars = d1.vars in 
	let nodes = d1.nodes in
	{ dom = dom; env = env; vars = vars; nodes = nodes }			


    let widen_threshold d1 d2 threshold =
    	let dom = Bdddomain1.widening_threshold man d1.dom d2.dom threshold in 
	let env = d1.env in
    	let vars = d1.vars in 
	let nodes = d1.nodes in
	{ dom = dom; env = env; vars = vars; nodes = nodes }

    let first_int = ref true

    let compress d = 
	let env = d.env in
    	let vars = d.vars in 
	let nodes = d.nodes in
	
	let allSame = ref true in 
	let allMatch = ref true in 	
	(*Format.fprintf Format.std_formatter "Compress "; *)
	let ll = Bdddomain1.to_bddapron man d.dom in 
      	let res = if (List.length ll = 0) then d.dom 
      	      else ( 
      	        let first_apron = snd (List.hd ll) in 
       	let man_apron = Abstract1.manager first_apron in 
	        let env_apron = Abstract1.env first_apron in 
      	 try List.iter (fun elem -> 
      		let elem1 = fst elem in 
		let elem2 = snd elem in 
		
		let k = ref 0 in 
		let index = ref 0 in 
		List.iter ( fun configBexp -> 
      				let bexp1 = ref (List.hd configBexp) in
      				if (List.length configBexp > 1) then (
    				    for i=1 to (List.length configBexp)-1 do
      					bexp1 := A_bbinary (A_AND,annotate !bexp1,annotate (List.nth configBexp i)); 
      				    done 
      				);   
      				let b = bExp_to_bddapron env cond !bexp1 in 
      				if (Expr1.Bool.is_eq cond elem1 b) then index:=!k; 
      				k := !k + 1
      			) !ItoA.bool_configs; 		
		
		let apron = List.nth !ItoA.apron_configs !index in 		
		if (not (Abstract1.is_eq man_apron elem2 apron)) then allMatch:=false; 	        			
      		if (not (Abstract1.is_eq man_apron elem2 first_apron)) then allSame:=false; 
      		(*Format.fprintf Format.std_formatter "Compress ### elem2: %a : apron: %a : allMatch: %b ### \n" Abstract1.print elem2 Abstract1.print apron !allMatch; *)
      			) ll; 
      		(*if (!allMatch) then Bdddomain1.of_bddapron man env [(Expr1.Bool.dtrue env cond,Abstract1.top man_apron env_apron)] 
      		else*) if (!allSame) then Bdddomain1.of_bddapron man env [(Expr1.Bool.dtrue env cond,first_apron)] 
      		else d.dom
      	 with Invalid_argument _ -> d.dom ) in  	
	{ dom = res; env = env; vars = vars; nodes = nodes }	


    let fwdAssign d (x,e) = match x with
    | A_var x ->
      let env = d.env in
      let vars = d.vars in 
      let nodes = d.nodes in	
      let e1 = 
      ( match e with 
      | A_arithmetic (e,ea) -> (aExp_to_bddapron env cond e) 
      | A_boolean (e,ea) -> (bExp_to_bddapron2 env cond e) ) in 
      (*let e1 = (aExp_to_bddapron env cond e) in *)	      
      (*Format.fprintf Format.std_formatter "Bdd fwdAssign ### x: %a ### exp: %a \n" var_print x aExp_print (annotate e); *)
      
      let ll = Bdddomain1.to_bddapron man d.dom in 
      (*Format.fprintf Format.std_formatter "### size of dom ### %d ### \n" (List.length ll);*)
      let res = 
       if (List.length ll = 0) then (  
		if ((snd e1) = 1) then Bdddomain1.forget_list man d.dom [x.varId] else 
	  	(if ((snd e1) = 2) then (let e2 = aInterval_to_bddapron env cond e in let dom_forget = Bdddomain1.forget_list man d.dom [x.varId] in (Bdddomain1.meet_condition man cond (Bdddomain1.meet_condition man cond (dom_forget) ((Expr1.Apron.supeq cond (Expr1.Apron.sub cond (fst e1) (Expr1.Apron.var env cond (x.varId)) )))  ) (Expr1.Apron.supeq cond (Expr1.Apron.sub cond (Expr1.Apron.var env cond (x.varId)) (e2) ))) ) 
		else (if ((snd e1) = 3) then (let dom_forget = Bdddomain1.forget_list man d.dom [x.varId] in (Bdddomain1.meet_condition man cond (dom_forget)  (Expr1.Apron.supeq cond (Expr1.Apron.sub cond (Expr1.Apron.var env cond (x.varId)) (fst e1) )))) 
		else Bdddomain1.assign_lexpr ~relational:true man cond d.dom [x.varId] [Expr1.Apron.to_expr (fst e1)] None ) )      
     )
      else (
      let first_apron = snd (List.hd ll) in 
      let man_apron = Abstract1.manager first_apron in 
      let env_apron = Abstract1.env first_apron in 
      let abs = ref (Abstract1.bottom man_apron env_apron) in 
      let e2 = (match e with 
      		| A_arithmetic (e,ea) -> Texpr1.of_expr env_apron (aExp_to_apron e) 
      		| A_boolean (e,ea) -> Texpr1.of_expr env_apron (bExp_to_apron env_apron man_apron e)
      		) in     
      
      List.iter (fun elem -> let elem1 = fst elem in (* (Expr1.Bool.print cond fmt (fst elem)) *)
			      let c = snd elem in 
			      let b = Abstract1.assign_texpr man_apron c (Var.of_string x.varId) e2 None in 
			      abs := Abstract1.join man_apron !abs b
		) ll; 
      (*Format.fprintf Format.std_formatter "Bdd fwdAssign ### abs: %a ### \n" Abstract1.print !abs; *)			
      
      let list_bdd = List.map2 ( fun configBexp configApron -> 
      					let apron = Abstract1.meet man_apron !abs configApron in  
      					let bexp1 = ref (List.hd configBexp) in
      					if (List.length configBexp > 1) then (
    					    for i=1 to (List.length configBexp)-1 do
      						bexp1 := A_bbinary (A_AND,annotate !bexp1,annotate (List.nth configBexp i)); 
      					    done 
      					);   
      					let b = bExp_to_bddapron env cond !bexp1 in 
     (*Format.fprintf Format.std_formatter "Bdd fwdAssign ### apron: %a ### bexp: %a \n" Abstract1.print apron bExp_print_aux !bexp1; *)
      					(b,apron)
      			) !ItoA.bool_configs !ItoA.apron_configs in    
      Bdddomain1.of_bddapron man env list_bdd        
	)  in
	{ dom = res; env = env; vars = vars; nodes = nodes }		  
    | _ -> raise (Invalid_argument "fwdAssign: unexpected lvalue")
	


    let bwdAssign d (x,e) = match x with
    | A_var x ->
      let env = d.env in
      let vars = d.vars in 
      let nodes = d.nodes in	
      let e1 = 
      ( match e with 
      | A_arithmetic (e,ea) -> (aExp_to_bddapron env cond e) 
      | A_boolean (e,ea) -> (bExp_to_bddapron2 env cond e) ) in 
      
       (*Format.fprintf Format.std_formatter "Bdd bwdAssign ### x: %a ### exp: %a \n" var_print x exp_print (annotate e);	 *)
	  (* Format.printf "expr = %a@." (Expr1.Apron.print cond) (fst e1); 
	  print_string "Assgn: "; (Expr1.Apron.print cond Format.std_formatter (fst e1)) ; print_string (" : " ^ string_of_int (snd e1) ^ " : "); print_endline x.varId; *)
	  
      let ll = Bdddomain1.to_bddapron man d.dom in 
      (*Format.fprintf Format.std_formatter "### size of dom ### %d ### \n" (List.length ll);*)
      let res = 
       if (List.length ll = 0) then ( 
      	 if ((snd e1) = 1) then (let dd=d.dom in Bdddomain1.forget_list man dd [x.varId]) else 
	  	(if ((snd e1) = 2) then (let dd=(let e2 = aInterval_to_bddapron env cond e in let dom_forget = Bdddomain1.forget_list man d.dom [x.varId] in (Bdddomain1.meet_condition man cond (Bdddomain1.meet_condition man cond (dom_forget) ((Expr1.Apron.supeq cond (Expr1.Apron.sub cond (fst e1) (Expr1.Apron.var env cond (x.varId)) )))  ) (Expr1.Apron.supeq cond (Expr1.Apron.sub cond (Expr1.Apron.var env cond (x.varId)) (e2) ))) ) in Bdddomain1.forget_list man dd [x.varId])
		else (if ((snd e1) = 3) then (let dd=(Bdddomain1.meet_condition man cond d.dom  (Expr1.Apron.supeq cond (Expr1.Apron.sub cond (Expr1.Apron.var env cond (x.varId)) (fst e1) ))) in Bdddomain1.forget_list man dd [x.varId])
		else Bdddomain1.substitute_lexpr man cond d.dom [x.varId] [Expr1.Apron.to_expr (fst e1)] None ) ) 
	) 
	else (
      let first_apron = snd (List.hd ll) in 
      let man_apron = Abstract1.manager first_apron in 
      let env_apron = Abstract1.env first_apron in 
      let abs = ref (Abstract1.bottom man_apron env_apron) in 
      let e2 = (match e with 
      		| A_arithmetic (e,ea) -> Texpr1.of_expr env_apron (aExp_to_apron e) 
      		| A_boolean (e,ea) -> Texpr1.of_expr env_apron (bExp_to_apron env_apron man_apron e)
      		) in     
      
      (*let b = Abstract1.substitute_texpr man_apron elem2 (Var.of_string x.varId) e2 None in *)
      
      		let list_bdd = List.map2 ( fun configBexp configApron -> 
      				(* List.iter (fun elem -> Format.fprintf Format.std_formatter " : %a : " bExp_print_aux elem) configBexp;
      				Format.fprintf Format.std_formatter "Bdd filter ### configApron: %a ### \n" Abstract1.print configApron; *)
      					let b = ref (Expr1.Bool.dtrue env cond) in 
			        	let bexp1 = ref (List.hd configBexp) in
    					for i=1 to (List.length configBexp)-1 do
      						bexp1 := A_bbinary (A_AND,annotate !bexp1,annotate (List.nth configBexp i)); 
      					done;
      					b := bExp_to_bddapron env cond !bexp1;        					
      					let apron = ref (Abstract1.bottom man_apron env_apron) in 
      					List.iter (fun elem -> 
      							let elem1 = fst elem in (* (Expr1.Bool.print cond fmt (fst elem)) *)
			        			let elem2 = snd elem in 	        			
      							(*Format.fprintf Format.std_formatter "Bdd ### subs: %a ### \n" Abstract1.print (Abstract1.substitute_texpr man_apron elem2 (Var.of_string x.varId) e2 None); *)
      							let ap = Abstract1. meet man_apron configApron (Abstract1.substitute_texpr man_apron elem2 (Var.of_string x.varId) e2 None) in 
      							(*Format.fprintf Format.std_formatter "Bdd ### %a ### \n" Abstract1.print ap;*)
							apron := Abstract1.join man_apron !apron ap; 
      							) ll; 
      					(*Expr1.Bool.print cond Format.std_formatter !b; 
      					Format.fprintf Format.std_formatter "Bdd RESULT ### %a ### \n" Abstract1.print !apron; *)
      					(!b,!apron)
      				) !ItoA.bool_configs !ItoA.apron_configs in       
      Bdddomain1.of_bddapron man env list_bdd 	
	) in 	
	{ dom = res; env = env; vars = vars; nodes = nodes }		  
    | _ -> raise (Invalid_argument "fwdAssign: unexpected lvalue")




	
    let filter d b = 
      let env = d.env in
      let vars = d.vars in 
      let nodes = d.nodes in		
      let b = bExp_to_bddapron env cond b in	
      let restrict = Bdddomain1.meet_condition man cond d.dom b in 
      let ll = Bdddomain1.to_bddapron man restrict in 
      let res = 
        if (List.length ll = 0) then (  
      		restrict ) 
      	else (
      		let first_apron = snd (List.hd ll) in 
      		let man_apron = Abstract1.manager first_apron in 
      		let env_apron = Abstract1.env first_apron in 
      		(*Format.fprintf Format.std_formatter "Bdd filter ### first apron: %a ### \n" Abstract1.print first_apron;*)
      		let list_bdd = List.map2 ( fun configBexp configApron -> 
      				(* List.iter (fun elem -> Format.fprintf Format.std_formatter " : %a : " bExp_print_aux elem) configBexp;
      				Format.fprintf Format.std_formatter "Bdd filter ### configApron: %a ### \n" Abstract1.print configApron; *)
      					let b = ref (Expr1.Bool.dtrue env cond) in 
      					let apron = ref (Abstract1.bottom man_apron env_apron) in 
      					List.iter (fun elem -> 
      							let elem1 = fst elem in (* (Expr1.Bool.print cond fmt (fst elem)) *)
			        			let elem2 = snd elem in 
			        			let bexp1 = ref (List.hd configBexp) in
    					    		for i=1 to (List.length configBexp)-1 do
      							bexp1 := A_bbinary (A_AND,annotate !bexp1,annotate (List.nth configBexp i)); 
      					    		done;
      					    		b := bExp_to_bddapron env cond !bexp1;  	        			
      							if (Expr1.Bool.is_leq cond !b elem1) then 
      								apron := Abstract1.meet man_apron elem2 configApron;
      							) ll; 
      					(*Expr1.Bool.print cond Format.std_formatter !b; 
      					Format.fprintf Format.std_formatter "Bdd filter ### apron: %a ### \n" Abstract1.print !apron;*)
      					(!b,!apron)
      				) !ItoA.bool_configs !ItoA.apron_configs in    
      				Bdddomain1.of_bddapron man env list_bdd 			
             		
      	) in 
      (*let res2 = Bdddomain1.meet_condition2 man d.dom b in 
      Format.printf "filter res2: %a@." (fun fmt x -> Bdddomain1.print fmt x) res2; *)
      { dom = res; env = env; vars = vars; nodes = nodes }		  

    let bint_cst env vmax v = Expr1.Bint.of_int env cond (`Bint (false, vmax)) v
    let bint_expr e = Expr1.Bint.to_expr e

    let apron_cst env v = Expr1.Apron.cst env cond v
    let apron_int env a b = failwith "intervals not implemented in bddapron..."
    let apron_add x y = Expr1.Apron.add cond x y
    let apron_sub x y = Expr1.Apron.sub cond x y
    let apron_mul x y = Expr1.Apron.mul cond x y
    let apron_div x y = Expr1.Apron.div cond x y
    let apron_gmod x y = Expr1.Apron.gmod cond x y
    let apron_neg x = Expr1.Apron.negate cond x
    let apron_var env x = Expr1.Apron.var env cond x
    let apron_eq x = Expr1.Apron.eq cond x
    let apron_supeq x = Expr1.Apron.supeq cond x
    let apron_sup x = Expr1.Apron.sup cond x
    let apron_print fmt x = Expr1.Apron.print cond fmt x
    let apron_expr e = Expr1.Apron.to_expr e



    let expr_print fmt e = Expr1.print cond fmt e
    let expr_var env v = Expr1.var env cond v
    let env_print fmt e = Env.print fmt e






    let to_lincons_array dom = 
      let domains = List.map (fun (x, y) -> y) (Bdddomain1.to_bddapron man dom) in
      let d = List.fold_left (fun x y -> Apron.Abstract1.join apron x y) (Apron.Abstract1.bottom apron (Env.apron(Bdddomain1.get_env dom))) domains in
      Apron.Abstract1.to_lincons_array apron d

    let get_apron_env dom = 
      let env = getenv dom in
      Env.apron env
    

         

    let del_vars (dom:domain) vars =
      let env = Bdddomain1.get_env dom in
      (*Bddapron.Env.print Format.std_formatter env;*)
      let env = Env.remove_vars env (List.map (fun (x, y) -> x) vars) in
      Bdddomain1.change_environment man dom env

    let ren_vars (dom:domain) begv endv = 
(*      let env = Bdddomain1.get_env domain in
      let env = Env.rename_vars env (List.map2 (fun x y -> (x, y)) begv endv) in
      Mbtdddomain1.change_environment man domain env*)
      Bdddomain1.rename man dom (List.map2 (fun x y -> (fst x, fst y)) begv endv)

  end


module BP = 
  BDDAPRON_DOMAIN
    (struct
      type lib = Polka.loose Polka.t
      let manager = Polka.manager_alloc_loose ()
    end)

module BB = 
  BDDAPRON_DOMAIN
    (struct
      type lib = Box.t
      let manager = Box.manager_alloc ()
    end)

module BO = 
  BDDAPRON_DOMAIN
    (struct
      type lib = Oct.t
      let manager = Oct.manager_alloc ()
end)
