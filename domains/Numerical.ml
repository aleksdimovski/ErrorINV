(***************************************************)
(*                                                 *)
(*            Numerical Domain Partition           *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open Apron
open Partition
open Constraints


module type NUMERICAL = sig 
  type lib
  val manager: lib Manager.t 
  val supports_underapproximation: bool
end

(** Single partition of the domain of a ranking function 
    represented by an APRON numerical abstract domain. *)
module Numerical(N: NUMERICAL)(C: CONSTRAINT): PARTITION = struct

  (** Linear constraints used to represent the partition. *)
  module C = C 

  module BanalApron = Banal_apron_domain.ApronDomain(N)

  (** An element of the numerical abstract domain. *)
  type t = { 
    constraints : C.t list; (* representation as list of constraints *)
    env : Environment.t; (* APRON environment *)
    vars : var list (* list of variables in the APRON environment *)
  }

  type apron_t = N.lib Abstract1.t

  (** The current representation as list of linear constraints. *)
  let constraints b: C.t list = List.fold_right (fun c cs -> 
      (* warning: fold_left impacts speed and result of the analysis *)
      try (* equality constraints are turned into pairs of inequalities *)
        let (c1,c2) = C.expand c in c1::c2::cs
      with Invalid_argument _ -> c::cs
    ) b.constraints [] 

  (** The current APRON environment. *)
  let env b = b.env

  (** The current list of variables in the APRON environment. *)
  let vars b = b.vars

  (** Creates an APRON manager depending on the numerical abstract domain. *)

  let manager = N.manager

  (**)

  let supports_underapproximation = N.supports_underapproximation
  
  
  let bot e vs = {
    constraints = [Lincons1.make_unsat e];
    env = e;
    vars = vs
  }

  let inner e vs cs = {
    constraints = cs;
    env = e;
    vars = vs
  }

  let top e vs = 
  	let rec aux vs cs = match vs with
		| [] -> (*Format.fprintf Format.std_formatter "end_top";*) cs
		| x::xs ->   match x.varTyp with
  			| A_INT | A_BOOL -> aux xs cs
  			| A_UINT -> (* Format.fprintf Format.std_formatter "%a %s{%s}\n" typ_print x.varTyp x.varId x.varName; *)
						  let cons = Lincons1.make (Linexpr1.make e) Lincons1.SUPEQ in
  							Lincons1.set_array cons [| ((Coeff.s_of_int 1), (Var.of_string x.varId)) |] None; 
						(* Lincons1.print Format.std_formatter cons; *) aux xs (cons::cs) 
   in (*Format.fprintf Format.std_formatter "begin_top\n"; let cs = aux vs [] in*)
   {
    constraints = aux vs [];
    env = e;
    vars = vs
  }

  (**)

  let isBot b =
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
    let b = Abstract1.of_lincons_array manager b.env a in
    Abstract1.is_bottom manager b

  let isLeq b1 b2 = 
    let env = b1.env in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a1 !i c; i := !i + 1) b1.constraints;
    let b1 = Abstract1.of_lincons_array manager env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter (fun c -> Lincons1.array_set a2 !j c; j := !j + 1) b2.constraints;
    let b2 = Abstract1.of_lincons_array manager env a2 in
    Abstract1.is_leq manager b1 b2

  (**)


  let to_apron_t (t:t) : apron_t = 
    let env = t.env in
    let a = Lincons1.array_make env (List.length t.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) t.constraints;
    Abstract1.of_lincons_array manager env a 

  let of_apron_t env vars (a:apron_t) : t = 
    let a = Abstract1.to_lincons_array manager a in
    let cs = ref [] in
    for i=0 to (Lincons1.array_length a)-1 do
      cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
    done; { constraints = !cs; env = env; vars = vars }

  let join b1 b2 = 
    let env = b1.env in
    let vars = b1.vars in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a1 !i c; i := !i + 1) b1.constraints;
    let b1 = Abstract1.of_lincons_array manager env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter (fun c -> Lincons1.array_set a2 !j c; j := !j + 1) b2.constraints;
    let b2 = Abstract1.of_lincons_array manager env a2 in
    let b = Abstract1.join manager b1 b2 in
    let a = Abstract1.to_lincons_array manager b in
    let cs = ref [] in
    for i=0 to (Lincons1.array_length a)-1 do
      cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
    done; { constraints = !cs; env = env; vars = vars }

  let widen b1 b2 = 
    let env = b1.env in
    let vars = b1.vars in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a1 !i c; i := !i + 1) b1.constraints;
    let b1 = Abstract1.of_lincons_array manager env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter (fun c -> Lincons1.array_set a2 !j c; j := !j + 1) b2.constraints;
    let b2 = Abstract1.of_lincons_array manager env a2 in
    let b = Abstract1.widening manager b1 b2 in
    let a = Abstract1.to_lincons_array manager b in
    let cs = ref [] in
    for i=0 to (Lincons1.array_length a)-1 do
      cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
    done; { constraints = !cs; env = env; vars = vars }

  let meet b1 b2 = 
    let env = b1.env in
    let vars = b1.vars in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a1 !i c; i := !i + 1) b1.constraints;
    let b1 = Abstract1.of_lincons_array manager env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter (fun c -> Lincons1.array_set a2 !j c; j := !j + 1) b2.constraints;
    let b2 = Abstract1.of_lincons_array manager env a2 in
    let b = Abstract1.meet manager b1 b2 in
    let a = Abstract1.to_lincons_array manager b in
    let cs = ref [] in
    for i=0 to (Lincons1.array_length a)-1 do
      cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
    done; { constraints = !cs; env = env; vars = vars }

  (**)

  let fwdAssign b (x,e) = match x with
    | A_var x ->
      let env = b.env in
      let vars = b.vars in
      
      let e = Texpr1.of_expr env (aExp_to_apron e) in  
      		      
      let a = Lincons1.array_make env (List.length b.constraints) in
      let i = ref 0 in
      List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
      let b = Abstract1.of_lincons_array manager env a in
      let b = Abstract1.assign_texpr manager b (Var.of_string x.varId) e None in
      let a = Abstract1.to_lincons_array manager b in
      let cs = ref [] in
      for i=0 to (Lincons1.array_length a)-1 do
        let lc = (Lincons1.array_get a i) in if (not (Coeff.equal_int (Lincons1.get_cst lc) 65535)) then cs := lc::!cs; (*TODO: normalization *)
      done; { constraints = !cs; env = env; vars = vars }
    | _ -> raise (Invalid_argument "fwdAssign: unexpected lvalue")


  let fwdAssign_bool b (x,e) = match x with
    | A_var x ->
      let env = b.env in
      let vars = b.vars in

    (*  let p1 = filter b e in 
      let p2 = filter b (fst (negBExp (e, (Lexing.dummy_pos, Lexing.dummy_pos)))) in

      let p = 
      if (B.isLeq b p1) then ( let e1 = (A_const 1) in fwdAssign b (x,e1) ) 
      else if (B.isLeq b p2) then ( let e1 = (A_const 0) in fwdAssign b (x,e1) ) 
      else ( let e1 = A_interval (0,1)  in fwdAssign b (x,e1) ) in
      p   *)
      
      let e = Texpr1.of_expr env (bExp_to_apron env manager e) in  
      		      
      let a = Lincons1.array_make env (List.length b.constraints) in
      let i = ref 0 in
      List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
      let b = Abstract1.of_lincons_array manager env a in
      let b = Abstract1.assign_texpr manager b (Var.of_string x.varId) e None in
      let a = Abstract1.to_lincons_array manager b in
      let cs = ref [] in
      for i=0 to (Lincons1.array_length a)-1 do
        let lc = (Lincons1.array_get a i) in if (not (Coeff.equal_int (Lincons1.get_cst lc) 65535)) then cs := lc::!cs; (*TODO: normalization *)
      done; { constraints = !cs; env = env; vars = vars } 
    | _ -> raise (Invalid_argument "fwdAssign: unexpected lvalue")

  let bwdAssign_underapprox (t:t) ((x,e): aExp * exp) : t = match x with
    | A_var x ->
      if not N.supports_underapproximation then
        raise (Invalid_argument "Underapproximation not supported by this abstract domain, use polyhedra instead");
      let env = t.env in
      let vars = t.vars in
      let at = to_apron_t t in
      let top = Abstract1.top manager (Abstract1.env at) in
      let pre = top in (* use top as pre environment *)
      let assignDest = Banal_domain.STRONG (Function_banal_converter.var_to_banal x) in
      
      let assignValue = (match e with 
      		| A_arithmetic (e,ea) -> Function_banal_converter.of_aExp e
      		| A_boolean (e,ea) -> Function_banal_converter.of_bExp e
      		) in
      
      let assigned = BanalApron.bwd_assign at () assignDest assignValue pre in
      of_apron_t env vars assigned
    | _ -> raise (Invalid_argument "bwdAssign_underapprox: unexpected lvalue")

  let bwdAssign b (x,e) = match x with
    | A_var x ->
      let env = b.env in
      let vars = b.vars in
      
      let e = Texpr1.of_expr env (aExp_to_apron e) in  
      (*Format.fprintf Format.std_formatter " bwdAss e : %a : " Texpr1.print e; *)
      let a = Lincons1.array_make env (List.length b.constraints) in
      let i = ref 0 in
      List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
      let b = Abstract1.of_lincons_array manager env a in
      let b = Abstract1.substitute_texpr manager b (Var.of_string x.varId) e None in
      let a = Abstract1.to_lincons_array manager b in
      let cs = ref [] in
      for i=0 to (Lincons1.array_length a)-1 do
        cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
      done; { constraints = !cs; env = env; vars = vars }
    | _ -> raise (Invalid_argument "bwdAssign: unexpected lvalue")


  let bwdAssign_bool b (x,e) = match x with
    | A_var x ->
      let env = b.env in
      let vars = b.vars in
      
      let e = Texpr1.of_expr env (bExp_to_apron env manager e) in  
      (*Format.fprintf Format.std_formatter " bwdAss e : %a : " Texpr1.print e; *)
      let a = Lincons1.array_make env (List.length b.constraints) in
      let i = ref 0 in
      List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
      let b = Abstract1.of_lincons_array manager env a in
      let b = Abstract1.substitute_texpr manager b (Var.of_string x.varId) e None in
      let a = Abstract1.to_lincons_array manager b in
      let cs = ref [] in
      for i=0 to (Lincons1.array_length a)-1 do
        cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
      done; { constraints = !cs; env = env; vars = vars }
    | _ -> raise (Invalid_argument "bwdAssign: unexpected lvalue")


  let project b x = (match x with
	   		| A_var v ->  
      				let env = b.env in
      				let vars = b.vars in
      				let a = Lincons1.array_make env (List.length b.constraints) in
      				let i = ref 0 in
      				List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
				let b = Abstract1.of_lincons_array manager env a in 
				let aa = Abstract1.forget_array manager b [| Var.of_string v.varId |] false in
				let a = Abstract1.to_lincons_array manager aa in
				let cs = ref [] in 
         			for i=0 to (Lincons1.array_length a)-1 do
           				cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         			done; { constraints = !cs; env = env; vars = vars }
			| _ -> raise (Invalid_argument "project: unexpected lvalue") )



  let bwdfilter_underapprox (t:t) (e:bExp) : t = 
    if not N.supports_underapproximation then
      raise (Invalid_argument "Underapproximation not supported by this abstract domain, use octagons or polyhedra instead");
    let env = t.env in
    let vars = t.vars in
    let expr = Function_banal_converter.of_bExp e in
    let at = to_apron_t t in
    let top = Abstract1.top manager (Abstract1.env at) in
    let bot = Abstract1.bottom manager (Abstract1.env at) in
    let pre = top in (* use top as pre environment *)
    let filtered = BanalApron.bwd_filter at bot () expr () pre in
    let result = of_apron_t env vars filtered in 
    result

  let bwdfilter_underapproxwhile (t:t) (t1:t) (e:bExp) (t2:t) : t = 
    if not N.supports_underapproximation then
      raise (Invalid_argument "Underapproximation not supported by this abstract domain, use octagons or polyhedra instead");
    let env = t.env in
    let vars = t.vars in
    let expr = Function_banal_converter.of_bExp e in
    let at = to_apron_t t in
    let at1 = to_apron_t t1 in
    let at2 = to_apron_t t2 in
    (* let pre = top in  use top as pre environment *)
    let filtered = BanalApron.bwd_filter at at1 () expr Banal_domain.LOOP at2 in
    let result = of_apron_t env vars filtered in 
    result

  let lowerwiden (t1:t) (t2:t) : t = 
    if not N.supports_underapproximation then
      raise (Invalid_argument "Underapproximation not supported by this abstract domain, use octagons or polyhedra instead");
    let env = t1.env in
    let vars = t1.vars in
    let at1 = to_apron_t t1 in
    let at2 = to_apron_t t2 in
    let filtered = BanalApron.bwd_meet at1 at2 Banal_domain.WIDEN in
    let result = of_apron_t env vars filtered in 
    result

  let rec bwdfilter b e =
  	let annotate e = (e, (Lexing.dummy_pos, Lexing.dummy_pos)) in 
	(*let (e,_) = negBExp (annotate e) in *)
    match e with
    | A_TRUE -> top b.env b.vars
    | A_MAYBE -> b
    | A_FALSE -> b
    | A_bunary (o,(e,_)) ->
      (match o with
       | A_NOT -> (match e with 
	   					| A_bvar v ->  
      									let env = b.env in
      									let vars = b.vars in
      									let a = Lincons1.array_make env (List.length b.constraints) in
      									let i = ref 0 in
      									List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
      									let b = Abstract1.of_lincons_array manager env a in									
										let aa = Abstract1.forget_array manager b [| Var.of_string v.varId |] false in
										let a = Abstract1.to_lincons_array manager aa in
										let cs = ref [] in 
         								for i=0 to (Lincons1.array_length a)-1 do
           									cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         								done; { constraints = !cs; env = env; vars = vars }
						| _ -> b) )
    | A_bbinary (o,(e1,_),(e2,_)) ->
      let b1 = bwdfilter b e1 and b2 = bwdfilter b e2 in
      (match o with
       | A_AND -> meet b1 b2
       | A_OR -> join b1 b2)
    | A_rbinary (o,e1,e2) ->
      let env = b.env in
      let vars = b.vars in
      let a = Lincons1.array_make env (List.length b.constraints) in
      let i = ref 0 in
      List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
      let b = Abstract1.of_lincons_array manager env a in
      (match o with
       | A_LESS ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e2,e1))) in
         let c = Tcons1.make e Tcons1.SUP in
         let a = Tcons1.array_make env 1 in
		 Tcons1.array_set a 0 c; 
         let aa = Abstract1.of_tcons_array manager env a in
         let b = Abstract1.join manager b aa in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars }
       | A_LESS_EQUAL ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e2,e1))) in
         let c = Tcons1.make e Tcons1.SUPEQ in
         let a = Tcons1.array_make env 1 in
		 Tcons1.array_set a 0 c;
         let aa = Abstract1.of_tcons_array manager env a in
		 Abstract1.print Format.std_formatter aa;
		 Abstract1.print Format.std_formatter b;
         let b = Abstract1.join manager b aa in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars }
       | A_GREATER ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e1,e2))) in
         let c = Tcons1.make e Tcons1.SUP in
         let a = Tcons1.array_make env 1 in
		 Tcons1.array_set a 0 c;
         let aa = Abstract1.of_tcons_array manager env a in
		 Abstract1.print Format.std_formatter aa;
		 Abstract1.print Format.std_formatter b;
         let b = Abstract1.join manager b aa in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars }
       | A_GREATER_EQUAL ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e1,e2))) in
         let c = Tcons1.make e Tcons1.SUPEQ in
         let a = Tcons1.array_make env 1 in
		 Tcons1.array_set a 0 c;
         let aa = Abstract1.of_tcons_array manager env a in
         let b = Abstract1.join manager b aa in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars })


  let rec filter b e =
    match e with
    | A_TRUE -> b
    | A_MAYBE -> b
    | A_FALSE -> bot b.env b.vars
    | A_bunary (o,e) ->
      (match o with
       | A_NOT -> let (e,_) = negBExp e in filter b e)
    | A_bbinary (o,(e1,_),(e2,_)) ->
      let b1 = filter b e1 and b2 = filter b e2 in
      (match o with
       | A_AND -> meet b1 b2
       | A_OR -> join b1 b2)
    | A_rbinary (o,e1,e2) ->
      let env = b.env in
      let vars = b.vars in
      let a = Lincons1.array_make env (List.length b.constraints) in
      let i = ref 0 in
      List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
      let b = Abstract1.of_lincons_array manager env a in
      (match o with
       | A_LESS ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e2,e1))) in
         let c = Tcons1.make e Tcons1.SUP in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array manager b a in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars }
       | A_LESS_EQUAL ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e2,e1))) in
         let c = Tcons1.make e Tcons1.SUPEQ in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array manager b a in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars }
       | A_GREATER ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e1,e2))) in
         let c = Tcons1.make e Tcons1.SUP in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array manager b a in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars }
       | A_GREATER_EQUAL ->
         let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,e1,e2))) in
         let c = Tcons1.make e Tcons1.SUPEQ in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array manager b a in
         let a = Abstract1.to_lincons_array manager b in
         let cs = ref [] in
         for i=0 to (Lincons1.array_length a)-1 do
           cs := (Lincons1.array_get a i)::!cs; (*TODO: normalization *)
         done; { constraints = !cs; env = env; vars = vars })

  (**)

  let subset fmt b1 b2 = 
    let env = b1.env in
    let vars = b1.vars in
    let cs1 = ref b1.constraints in 
	Format.fprintf fmt " subset b1: \n ";
	let i = ref 1 and l = List.length !cs1 in
    List.iter (fun c ->
            C.print vars fmt c;
            if (!i = l) then () else Format.fprintf fmt " && ";
            i := !i + 1
          ) !cs1; 
    Format.fprintf fmt " subset b2: \n ";
    let cs2 = ref b2.constraints in 
	let i = ref 1 and l = List.length !cs2 in
    List.iter (fun c ->
            C.print vars fmt c;
            if (!i = l) then () else Format.fprintf fmt " && ";
            i := !i + 1
          ) !cs2; 
	meet b1 b2

  let print fmt b =
    let vars = b.vars in
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
    let b = Abstract1.of_lincons_array manager b.env a in
    let a = Abstract1.to_lincons_array manager b in
    let cs = ref [] in
    for i=0 to (Lincons1.array_length a)-1 do
      cs := (Lincons1.array_get a i)::!cs;
    done;
    match !cs with
    | [] -> Format.fprintf fmt "top"
    | x::_ ->
      if (C.isBot x) then Format.fprintf fmt "bottom" else
        let i = ref 1 and l = List.length !cs in
        List.iter (fun c ->
            C.print vars fmt c;
            if (!i = l) then () else Format.fprintf fmt " && ";
            i := !i + 1
          ) !cs
		  

  let toArr b = 
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;  
    a


  let ofArr arr env vars = 
    let cs = ref [] in
    for i=0 to (Lincons1.array_length arr)-1 do
      cs := (Lincons1.array_get arr i)::!cs;
    done; 
    { constraints = !cs; env = env; vars = vars }

		  
  let to_stringZ3 b1 b2 =
    let lines = ref [] in
    let vars = b1.vars in
    let a1 = Lincons1.array_make b1.env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a1 !i c; i := !i + 1) b1.constraints;
    let b1 = Abstract1.of_lincons_array manager b1.env a1 in
    let a1 = Abstract1.to_lincons_array manager b1 in
    let cs1 = ref [] in
    for i=0 to (Lincons1.array_length a1)-1 do
      cs1 := (Lincons1.array_get a1 i)::!cs1;
    done;
    (match !cs1 with
    | [] -> ()
    | x::_ ->
      if (C.isBot x) then () else
        (let i = ref 1 and l = List.length !cs1 in
        List.iter (fun c -> 
		    let name = "A" ^ string_of_int !i in 
            lines := !lines @ [(C.to_stringZ3 vars c name)];
            i := !i + 1
          ) !cs1)); 
    let a2 = Lincons1.array_make b2.env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter (fun c -> Lincons1.array_set a2 !j c; j := !j + 1) b2.constraints;
    let b2 = Abstract1.of_lincons_array manager b2.env a2 in
    let a2 = Abstract1.to_lincons_array manager b2 in
    let cs2 = ref [] in
    for j=0 to (Lincons1.array_length a2)-1 do
      cs2 := (Lincons1.array_get a2 j)::!cs2;
    done;
    match !cs2 with
    | [] -> []
    | x::_ ->
      if (C.isBot x) then !lines else
        (let j = ref 1 and l = List.length !cs2 in 
        let name = "B1" in 
        let line = ref "" in 
        List.iter (fun c -> 
            line := !line ^ " " ^ (C.to_stringZ3_bwd vars c name);
            j := !j + 1
          ) !cs2; 
        lines := !lines @ ["(assert (! (not (and" ^ !line ^ " ) ) :named " ^ name ^ "))"]; 
        !lines)		  



  let filter_list list b =
    let env = b.env in
    let vars = b.vars in
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let cs = ref [] in
    let i = ref 0 in
    List.iter (fun elem -> let k = int_of_string (String.make 1 (String.get elem 1)) in cs:=List.nth b.constraints (k-1)::!cs) list;	
	{ constraints = !cs; env = env; vars = vars }



  let varsLive (b:t) : var list =
    let result = ref [] in
    let cs = b.constraints in
	let vs = b.vars in
	List.iter (fun v -> 
    	for i=0 to (List.length cs)-1 do
      		if (C.var v (List.nth cs i)) then ((*print_string v.varName; print_string " here ";*) if (not (List.exists (fun el -> (String.compare el.varName v.varName == 0)) !result)) then result := v::!result)
    	done ) vs;
	!result


  let to_stringLatte b liveVars =
    let lines = ref [] in 
	let eqs = ref [] in 
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let i = ref 0 in
    List.iter (fun c -> Lincons1.array_set a !i c; i := !i + 1) b.constraints;
    let b = Abstract1.of_lincons_array manager b.env a in
    let a = Abstract1.to_lincons_array manager b in
    let cs = ref [] in
    for i=0 to (Lincons1.array_length a)-1 do
      cs := (Lincons1.array_get a i)::!cs;
    done; 
	let count = (List.length !cs) in 
    match !cs with
    | [] -> ([],[],count)
    | x::_ ->
      if (C.isBot x) then (!lines,!eqs,count) else
        (let i = ref 1 and l = List.length !cs in
        List.iter (fun c ->
			let (l,e) = C.to_stringLatte liveVars c in 
            lines := !lines @ [(l)];
			if (e) then eqs := !eqs @ [(!i)];
            i := !i + 1
          ) !cs; (!lines,!eqs,count))


end

(** Single partition of the domain of a ranking function 
    represented by the boxes numerical abstract domain. *)
module B = Numerical(
  struct 
    type lib = Box.t
    let manager = Box.manager_alloc ()
    let supports_underapproximation = false
  end)(C)

(** Single partition of the domain of a ranking function 
    represented by the octagons abstract domain. *)
module O = Numerical(
  struct 
    type lib = Oct.t 
    let manager = Oct.manager_alloc () 
    let supports_underapproximation = false
  end)(C)

(** Single partition of the domain of a ranking function 
    represented by the polyhedra abstract domain. *)
module P = Numerical(
  struct 
    type lib = Polka.loose Polka.t
    let manager = Polka.manager_alloc_loose ()
    let supports_underapproximation = true
  end)(C)
