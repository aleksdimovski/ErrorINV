(*     ********* Abstract Syntax ************      *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open Apron
open Bddapron
open IntermediateSyntax

(* types *)
type typ =
  | A_INT
  | A_UINT
  | A_BOOL

let typ_print fmt = function
  | A_INT -> Format.fprintf fmt "int"
  | A_UINT -> Format.fprintf fmt "unsigned int"
  | A_BOOL -> Format.fprintf fmt "bool"
  

(* variables *)
type var = {
  varId: string;
  varName: string;
  varTyp: typ;
}

let var_print fmt v = Format.fprintf fmt "%s{%s}" v.varId v.varName

module VarMap = Map.Make(
  struct
    type t = var
    let compare x1 x2 = compare x1.varId x2.varId
  end)

(* arithmetic binary operators *)
type aBinOp =
  | A_PLUS		(* + *)
  | A_MINUS		(* - *)
  | A_MULTIPLY	(* * *)
  | A_DIVIDE	(* / *)
  | A_MOD		(* % *)

let aBinOp_prec = function
  | A_PLUS -> 5
  | A_MINUS -> 5
  | A_MULTIPLY -> 6
  | A_DIVIDE -> 6
  | A_MOD -> 6  

let aBinOp_tostring = function
  | A_PLUS -> "+"
  | A_MINUS -> "-"
  | A_MULTIPLY -> "*"
  | A_DIVIDE -> "/"
  | A_MOD -> "%"

let aBinOp_print fmt = function
  | A_PLUS -> Format.fprintf fmt "+"
  | A_MINUS -> Format.fprintf fmt "-"
  | A_MULTIPLY -> Format.fprintf fmt "*"
  | A_DIVIDE -> Format.fprintf fmt "/"
  | A_MOD -> Format.fprintf fmt "%%"

(* arithmetic unary operators *)
type aUnOp =
  | A_UMINUS	(* - *)

let aUnOp_tostring = function
  | A_UMINUS -> "-"

let aUnOp_print fmt = function
  | A_UMINUS -> Format.fprintf fmt "-"

(* boolean binary operators *)
type bBinOp =
  | A_AND	(* && *)
  | A_OR	(* || *)

let bBinOp_prec = function
  | A_AND -> 2
  | A_OR -> 1

let negBBinOp = function
  | A_AND -> A_OR
  | A_OR -> A_AND

let bBinOp_tostring = function
  | A_AND -> "&&"
  | A_OR -> "||"

let bBinOp_print fmt = function
  | A_AND -> Format.fprintf fmt "&&"
  | A_OR -> Format.fprintf fmt "||"

(* boolean unary operators *)
type bUnOp =
  | A_NOT	(* ! *)

let bUnOp_tostring = function
  | A_NOT -> "!"

let bUnOp_print fmt = function
  | A_NOT -> Format.fprintf fmt "!"

(* relational binary operators *)
type rBinOp =
  | A_LESS			(* < *)
  | A_LESS_EQUAL		(* <= *)
  | A_GREATER			(* > *)
  | A_GREATER_EQUAL	(* >= *)

let rBinOp_prec = function
  | A_LESS -> 4
  | A_LESS_EQUAL -> 4
  | A_GREATER -> 4
  | A_GREATER_EQUAL -> 4

let negRBinOp = function
  | A_LESS -> A_GREATER_EQUAL
  | A_LESS_EQUAL -> A_GREATER
  | A_GREATER -> A_LESS_EQUAL
  | A_GREATER_EQUAL -> A_LESS

let rBinOp_tostring = function
  | A_LESS -> "<"
  | A_LESS_EQUAL -> "<="
  | A_GREATER -> ">"
  | A_GREATER_EQUAL -> ">="

let rBinOp_print fmt = function
  | A_LESS -> Format.fprintf fmt "<"
  | A_LESS_EQUAL -> Format.fprintf fmt "<="
  | A_GREATER -> Format.fprintf fmt ">"
  | A_GREATER_EQUAL -> Format.fprintf fmt ">="

(* arithmetic expressions *)
type aExp =
  | A_RANDOM	(* ? *)
  | A_URANDOM
  | A_var of var
  | A_const of int
  | A_interval of int * int
  | A_aunary of aUnOp * (aExp annotated)
  | A_abinary of aBinOp * (aExp annotated) * (aExp annotated)

let rec aExp_invertible x e =
  match e with
  | A_var y -> (compare x.varId y.varId) = 0
  | A_aunary (_,(e,_)) -> aExp_invertible x e
  | A_abinary (_,(e1,_),(e2,_)) -> (aExp_invertible x e1) || (aExp_invertible x e2)
  | _ -> false

let aExp_prec = function
  | A_aunary (_,_) -> 99
  | A_abinary (o,_,_) -> aBinOp_prec o
  | _ -> 100

let rec aExp_to_apron e =
  match e with
  | A_RANDOM -> Texpr1.Cst (Coeff.Interval Interval.top)
  | A_URANDOM -> Texpr1.Cst (Coeff.i_of_int 0 65535)
  | A_var x -> Texpr1.Var (Var.of_string x.varId)
  | A_const i -> Texpr1.Cst (Coeff.s_of_int i)
  | A_interval (i1,i2) -> Texpr1.Cst (Coeff.i_of_int i1 i2)
  | A_aunary (o,(e,_)) ->
    let e = aExp_to_apron e in
    (match o with
     | A_UMINUS -> Texpr1.Unop (Texpr1.Neg,e,Texpr1.Int,Texpr1.Zero))
  | A_abinary (o,(e1,_),(e2,_)) ->
    let e1 = aExp_to_apron e1 in
    let e2 = aExp_to_apron e2 in
    (match o with
     | A_PLUS -> Texpr1.Binop (Texpr1.Add,e1,e2,Texpr1.Int,Texpr1.Zero)
     | A_MINUS -> Texpr1.Binop (Texpr1.Sub,e1,e2,Texpr1.Int,Texpr1.Zero)
     | A_MULTIPLY -> Texpr1.Binop (Texpr1.Mul,e1,e2,Texpr1.Int,Texpr1.Zero)
     | A_DIVIDE -> Texpr1.Binop (Texpr1.Div,e1,e2,Texpr1.Int,Texpr1.Zero)
	 | A_MOD -> Texpr1.Binop (Texpr1.Mod,e1,e2,Texpr1.Int,Texpr1.Zero))

  
  
let rec aExp_to_bddapron env cond e =
  match e with
  | A_RANDOM -> (Expr1.Apron.cst env cond (Coeff.s_of_int 0), 1)
  | A_URANDOM -> (Expr1.Apron.cst env cond (Coeff.s_of_int 0), 3)
  | A_var x -> (Expr1.Apron.var env cond (x.varId), 0)
  | A_const i -> (Expr1.Apron.cst env cond (Coeff.s_of_int i), 0)
  | A_interval (i1,i2) -> (Expr1.Apron.cst env cond (Coeff.s_of_int i2), 2)
  | A_aunary (o,(e,_)) ->
    let e = (fst (aExp_to_bddapron env cond e)) in
    (match o with
     | A_UMINUS -> (Expr1.Apron.negate cond e, 0) )
  | A_abinary (o,(e1,_),(e2,_)) ->
    let e1 = (fst (aExp_to_bddapron env cond e1)) in
    let e2 = (fst (aExp_to_bddapron env cond e2)) in
    (match o with
     | A_PLUS -> (Expr1.Apron.add cond e1 e2, 0)
     | A_MINUS -> (Expr1.Apron.sub cond e1 e2, 0)
     | A_MULTIPLY -> (Expr1.Apron.mul cond e1 e2, 0)
     | A_DIVIDE -> (Expr1.Apron.div cond e1 e2, 0)
	 | A_MOD -> (Expr1.Apron.gmod cond e1 e2, 0)
	 )

let rec aExp_isEq e1 e2 =
  match e1, e2 with
  | A_RANDOM, A_RANDOM -> true
  | A_URANDOM, A_URANDOM -> true
  | A_var x1, A_var x2 -> String.equal (x1.varId) (x2.varId)
  | A_const i, A_const j -> (i=j)
  | A_interval (i1,i2), A_interval (j1,j2) -> (i1=j1) && (i2=j2)
  | A_aunary (o1,(e1,_)), A_aunary (o2,(e2,_)) ->
    let b = aExp_isEq e1 e2 in
    (match o1,o2 with
     | A_UMINUS, A_UMINUS -> b 
     | _ -> false )
  | A_abinary (o1,(e1,_),(e2,_)), A_abinary (o2,(f1,_),(f2,_)) ->
    let b1 = aExp_isEq e1 f1 in
    let b2 = aExp_isEq e2 f2 in
    (match o1,o2 with
     | A_PLUS, A_PLUS -> (b1 && b2)
     | A_MINUS, A_MINUS -> (b1 && b2)
     | A_MULTIPLY, A_MULTIPLY -> (b1 && b2)
     | A_DIVIDE, A_DIVIDE -> (b1 && b2)
     | A_MOD, A_MOD -> (b1 && b2)
     | _, _ -> false )
  | _ -> false


let rec aExp_print fmt (e,_) =
  match e with
  | A_RANDOM -> Format.fprintf fmt "?"
  | A_URANDOM -> Format.fprintf fmt "u?"
  | A_var v -> var_print fmt v
  | A_const i -> Format.fprintf fmt "%i" i
  | A_interval (i1,i2) -> Format.fprintf fmt "[%i,%i]" i1 i2
  | A_aunary (o,e1) ->
    Format.fprintf fmt "%a" aUnOp_print o;
    if aExp_prec (fst e1) <= aExp_prec e
    then Format.fprintf fmt "(%a)" aExp_print e1
    else Format.fprintf fmt "%a" aExp_print e1
  | A_abinary (o,e1,e2) ->
    if aExp_prec (fst e1) <= aExp_prec e
    then Format.fprintf fmt "(%a) " aExp_print e1
    else Format.fprintf fmt "%a " aExp_print e1;
    Format.fprintf fmt "%a" aBinOp_print o;
    if aExp_prec (fst e2) <= aExp_prec e
    then Format.fprintf fmt " (%a)" aExp_print e2
    else Format.fprintf fmt " %a" aExp_print e2


(* boolean expressions *)
type bExp =
  | A_TRUE
  | A_MAYBE	(* ? *)
  | A_FALSE
  | A_bvar of var
  | A_bunary of bUnOp * (bExp annotated)
  | A_bbinary of bBinOp * (bExp annotated) * (bExp annotated)
  | A_rbinary of rBinOp * (aExp annotated) * (aExp annotated)

let bExp_prec = function
  | A_bunary (_,_) -> 99
  | A_bbinary (o,_,_) -> bBinOp_prec o
  | A_rbinary (o,_,_) -> rBinOp_prec o
  | _ -> 100

let rec negBExp (b,a) =
  match b with
  | A_TRUE -> (A_FALSE,a)
  | A_MAYBE -> (A_MAYBE,a)
  | A_FALSE -> (A_TRUE,a)
  | A_bvar v -> (A_bunary (A_NOT,(A_bvar v,a)),a)
  | A_bunary (o,b) ->
    (match o with
     | A_NOT -> b)
  | A_bbinary (o,b1,b2) -> (A_bbinary (negBBinOp o,negBExp b1,negBExp b2),a)
  | A_rbinary (o,a1,a2) -> (A_rbinary (negRBinOp o,a1,a2),a)


let rec bExp_to_bddapron env cond b =
  match b with
  | A_TRUE -> Expr1.Bool.dtrue env cond
  | A_MAYBE -> Expr1.Bool.dtrue env cond
  | A_FALSE -> Expr1.Bool.dfalse env cond 
  | A_bvar v -> Expr1.Bool.var env cond (v.varName)
  | A_bunary (o,(e1,_)) ->
    let e = bExp_to_bddapron env cond e1 in
    (match o with
     | A_NOT -> Expr1.Bool.dnot cond e )
  | A_bbinary (o,(e1,_),(e2,_)) ->
    let e1 = bExp_to_bddapron env cond e1 in
    let e2 = bExp_to_bddapron env cond e2 in
    (match o with
     | A_AND -> Expr1.Bool.dand cond e1 e2
     | A_OR -> Expr1.Bool.dor cond e1 e2 )
  | A_rbinary (o,(e1,_),(e2,_)) ->	 
    let e1 = (fst (aExp_to_bddapron env cond e1)) in
    let e2 = (fst (aExp_to_bddapron env cond e2)) in  
    ( match o with
     | A_LESS -> Expr1.Apron.sup cond (Expr1.Apron.sub cond e2 e1)
	 | A_LESS_EQUAL -> Expr1.Apron.supeq cond (Expr1.Apron.sub cond e2 e1)
	 | A_GREATER -> Expr1.Apron.sup cond (Expr1.Apron.sub cond e1 e2)
	 | A_GREATER_EQUAL -> Expr1.Apron.supeq cond (Expr1.Apron.sub cond e1 e2)
	)


let rec bExp_to_bddapron2 env cond e =
  match e with
  | A_TRUE -> (Expr1.Apron.cst env cond (Coeff.s_of_int 1), 0)
  | A_MAYBE -> (aExp_to_bddapron env cond (A_interval (0,1)))
  | A_FALSE -> (Expr1.Apron.cst env cond (Coeff.s_of_int 0), 0)
  | A_bvar x -> (Expr1.Apron.var env cond (x.varId), 0)
  | A_bunary (o,(e1,_)) ->
    let e = (fst (bExp_to_bddapron2 env cond e1)) in
    (match o with
  | A_NOT -> (Expr1.Apron.ite cond (Expr1.Apron.eq cond e) (Expr1.Apron.cst env cond (Coeff.s_of_int 1)) (Expr1.Apron.cst env cond (Coeff.s_of_int 0)), 0) )
  | A_bbinary (o,(e1,_),(e2,_)) ->
    let e1 = (fst (bExp_to_bddapron2 env cond e1)) in
    let e2 = (fst (bExp_to_bddapron2 env cond e2)) in
    (match o with
     | A_AND -> (Expr1.Apron.mul cond e1 e2, 0)
     | A_OR -> (Expr1.Apron.add cond e1 e2, 0) )
  | A_rbinary (o,(e1,_),(e2,_)) ->	 
    let e1 = (fst (aExp_to_bddapron env cond e1)) in
    let e2 = (fst (aExp_to_bddapron env cond e2)) in  
    ( match o with
     | A_LESS -> (Expr1.Apron.ite cond (Expr1.Apron.sup cond (Expr1.Apron.sub cond e2 e1)) (Expr1.Apron.cst env cond (Coeff.s_of_int 1)) (Expr1.Apron.cst env cond (Coeff.s_of_int 0)),0) 
	 | A_LESS_EQUAL -> (Expr1.Apron.ite cond (Expr1.Apron.supeq cond (Expr1.Apron.sub cond e2 e1)) (Expr1.Apron.cst env cond (Coeff.s_of_int 1)) (Expr1.Apron.cst env cond (Coeff.s_of_int 0)),0) 
	 | A_GREATER -> (Expr1.Apron.ite cond ( Expr1.Apron.sup cond (Expr1.Apron.sub cond e1 e2)) (Expr1.Apron.cst env cond (Coeff.s_of_int 1)) (Expr1.Apron.cst env cond (Coeff.s_of_int 0)),0) 
	 | A_GREATER_EQUAL -> (Expr1.Apron.ite cond (Expr1.Apron.supeq cond (Expr1.Apron.sub cond e1 e2)) (Expr1.Apron.cst env cond (Coeff.s_of_int 1)) (Expr1.Apron.cst env cond (Coeff.s_of_int 0)), 0)
	)     


let rec bExp_to_apron env man e =
  match e with
  | A_TRUE -> Texpr1.Cst (Coeff.s_of_int 1)
  | A_MAYBE -> Texpr1.Cst (Coeff.i_of_int 0 1)
  | A_FALSE -> Texpr1.Cst (Coeff.s_of_int 0)
  | A_bvar x -> Texpr1.Var (Var.of_string x.varId)
  | A_bunary (o,(e1,_)) ->
    let e = bExp_to_apron env man e1 in
    (match o with
  | A_NOT -> let e = Texpr1.of_expr env e in
         let c = Tcons1.make e Tcons1.SUP in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array man (Abstract1.top man env) a in 
         if (Abstract1.is_bottom man b) then (Texpr1.Cst (Coeff.s_of_int 0)) else (Texpr1.Cst (Coeff.s_of_int 1)) 			    )
  | A_bbinary (o,(e1,_),(e2,_)) ->
    let e1 = bExp_to_apron env man e1 in
    let e2 = bExp_to_apron env man e2 in
    (match o with
     | A_AND -> Texpr1.Binop (Texpr1.Mul,e1,e2,Texpr1.Int,Texpr1.Zero)
     | A_OR -> Texpr1.Binop (Texpr1.Add,e1,e2,Texpr1.Int,Texpr1.Zero) )
  | A_rbinary (o,(e1,e1a),(e2,e2a)) ->	  
    ( match o with
     | A_LESS -> let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,(e2,e2a),(e1,e1a)))) in
         let c = Tcons1.make e Tcons1.SUP in 
         Texpr1.to_expr (Tcons1.get_texpr1 c)
         (*let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array man (Abstract1.top man env) a in 
         if (Abstract1.is_bottom man b) then (Texpr1.Cst (Coeff.s_of_int 0)) else (Texpr1.Cst (Coeff.s_of_int 1)) *)
	 | A_LESS_EQUAL -> let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,(e2,e2a),(e1,e1a)))) in
         let c = Tcons1.make e Tcons1.SUPEQ in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array man (Abstract1.top man env) a in 
         if (Abstract1.is_bottom man b) then (Texpr1.Cst (Coeff.s_of_int 0)) else (Texpr1.Cst (Coeff.s_of_int 1)) 
	 | A_GREATER -> let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,(e1,e1a),(e2,e2a)))) in
         let c = Tcons1.make e Tcons1.SUP in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array man (Abstract1.top man env) a in 
         if (Abstract1.is_bottom man b) then (Texpr1.Cst (Coeff.s_of_int 0)) else (Texpr1.Cst (Coeff.s_of_int 1))
	 | A_GREATER_EQUAL -> let e = Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS,(e1,e1a),(e2,e2a)))) in
         let c = Tcons1.make e Tcons1.SUPEQ in
         let a = Tcons1.array_make env 1 in
         Tcons1.array_set a 0 c;
         let b = Abstract1.meet_tcons_array man (Abstract1.top man env) a in 
         if (Abstract1.is_bottom man b) then (Texpr1.Cst (Coeff.s_of_int 0)) else (Texpr1.Cst (Coeff.s_of_int 1))
	)      


let rec bExp_isEq b1 b2 =
  match b1, b2 with
  | A_TRUE, A_TRUE -> true
  | A_MAYBE, A_MAYBE -> true
  | A_FALSE, A_FALSE -> true 
  | A_bvar v1, A_bvar v2 -> String.equal (v1.varName) (v2.varName)
  | A_bunary (o1,(e1,_)), A_bunary (o2,(e2,_)) ->
    let r1 = bExp_isEq e1 e2 in
    (match o1,o2 with
     | A_NOT, A_NOT -> r1 
     | _ -> false     )
  | A_bbinary (o1,(e1,_),(e2,_)), A_bbinary (o2,(f1,_),(f2,_)) ->
    let r1 = bExp_isEq e1 f1 in
    let r2 = bExp_isEq e2 f2 in
    (match o1, o2 with
     | A_AND, A_AND -> r1 && r2 
     | A_OR, A_OR -> r1 && r2 
     | _ -> false )
  | A_rbinary (o1,(e1,_),(e2,_)), A_rbinary (o2,(f1,_),(f2,_)) ->	 
    let r1 = aExp_isEq e1 f1 in
    let r2 = aExp_isEq e2 f2 in  
    ( match o1,o2 with
     | A_LESS, A_LESS -> r1 && r2
     | A_LESS_EQUAL, A_LESS_EQUAL -> r1 && r2 
     | A_GREATER, A_GREATER -> r1 && r2 
     | A_GREATER_EQUAL, A_GREATER_EQUAL -> r1 && r2 
     | _ -> false )
   | _ -> false


let rec bExp_print_aux fmt e =
  match e with
  | A_TRUE -> Format.fprintf fmt "true"
  | A_MAYBE -> Format.fprintf fmt "?"
  | A_FALSE -> Format.fprintf fmt "false"
  | A_bvar v -> var_print fmt v
  | A_bunary (o,e1) ->
    Format.fprintf fmt "%a" bUnOp_print o;
    if bExp_prec (fst e1) <= bExp_prec e
    then Format.fprintf fmt "(%a)" bExp_print_aux (fst e1)
    else Format.fprintf fmt "%a" bExp_print_aux (fst e1)
  | A_bbinary (o,e1,e2) ->
    if bExp_prec (fst e1) <= bExp_prec e
    then Format.fprintf fmt "(%a) " bExp_print_aux (fst e1)
    else Format.fprintf fmt "%a " bExp_print_aux (fst e1);
    Format.fprintf fmt "%a" bBinOp_print o;
    if bExp_prec (fst e2) <= bExp_prec e
    then Format.fprintf fmt " (%a)" bExp_print_aux (fst e2)
    else Format.fprintf fmt " %a" bExp_print_aux (fst e2)
  | A_rbinary (o,e1,e2) ->
    if aExp_prec (fst e1) <= bExp_prec e
    then Format.fprintf fmt "(%a) " aExp_print e1
    else Format.fprintf fmt "%a " aExp_print e1;
    Format.fprintf fmt "%a" rBinOp_print o;
    if aExp_prec (fst e2) <= bExp_prec e
    then Format.fprintf fmt " (%a)" aExp_print e2
    else Format.fprintf fmt " %a" aExp_print e2

let bExp_print fmt b = bExp_print_aux fmt (fst b)

(* expressions *)
type exp =
  | A_arithmetic of (aExp annotated)
  | A_boolean of (bExp annotated)
  | A_stmt

let rec aInterval_to_bddapron env cond e =
  (match e with
  | A_arithmetic (e1,ea) -> (match e1 with | A_interval (i1,i2) -> Expr1.Apron.cst env cond (Coeff.s_of_int i1)
  					    | _ -> raise (Invalid_argument "aInterval") )
  | _ -> raise (Invalid_argument "aInterval") )

let rec exp_print_aux fmt e =
  match e with
  | A_arithmetic (e,ea) -> aExp_print fmt (e,ea)
  | A_boolean (e,ea) -> bExp_print fmt (e,ea)
  | _ ->  Format.fprintf fmt " not exp to print "
  
let exp_print fmt b = exp_print_aux fmt (fst b)
  
(* properties *)
module StringMap = Map.Make(struct type t=string let compare=compare end)

type property = (bExp annotated) StringMap.t

let property_print fmt p =
  let (u,p) = StringMap.partition (fun l _ -> l = "") p in
  if (StringMap.cardinal p) > 0
  then StringMap.iter (fun l e -> Format.fprintf fmt "%s -> %a\n" l bExp_print e) p
  else Format.fprintf fmt "%a\n" bExp_print (StringMap.find "" u)

(* statements *)
type stmt =
  | A_label of (string annotated)
  | A_return
  | A_assign of (aExp annotated) * (exp annotated)
  | A_assert of (bExp annotated)
  | A_if of (bExp annotated) * block * block
  | A_ifdef of (bExp annotated) * block * block
  | A_while of label * (bExp annotated) * block
  | A_call of string * (stmt annotated) list (* function call *)
  | A_recall of string * (stmt annotated) list (* recursive call *)

and block =
  | A_empty of label
  | A_block of label * (stmt annotated) * block

and label = int

type statements = stmt annotated list

let rec stmt_print ind fmt (s,_) =
  match s with
  | A_label (l,_) -> Format.fprintf fmt "%s%s:\n" ind l
  | A_return -> Format.fprintf fmt "%sreturn\n" ind
  | A_assign (v,e) -> Format.fprintf fmt "%s%a := %a\n" ind aExp_print v exp_print e
  | A_assert b -> Format.fprintf fmt "%sassert( %a )\n" ind bExp_print b
  | A_if (b,s1,s2) ->
    Format.fprintf fmt "%sif ( %a ) then\n%a%s      else\n%a%s      endif\n"
      ind bExp_print b
      (block_print (ind ^ "  ")) s1 ind	
      (block_print (ind ^ "  ")) s2 ind
  | A_ifdef (b,s1,s2) ->
    Format.fprintf fmt "%s#if ( %a ) \n%a%s      #else\n%a%s      #endif\n"
      ind bExp_print b
      (block_print (ind ^ "  ")) s1 ind	
      (block_print (ind ^ "  ")) s2 ind	  
  | A_while (l,b,s1) ->
    Format.fprintf fmt "%swhile %a ( %a ) do\n%a%s      od\n"
      ind label_print l bExp_print b
      (block_print (ind ^ "  ")) s1 ind
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

and block_print ind fmt b =
  match b with
  | A_empty l -> Format.fprintf fmt "%a\n" label_print l
  | A_block (l,s,b) ->
    Format.fprintf fmt "%a %a%a" label_print l (stmt_print ind) s (block_print ind) b

and label_print fmt l = if (l < 10) then Format.fprintf fmt "[ %i:]" l else Format.fprintf fmt "[%i:]" l

let label_of_block (block:block) : label = match block with
  | A_empty l -> l
  | A_block (l, _ , _) -> l

(* functions *)
type func = {
  funcName: string;
  funcTyp: var option;
  funcArgs: var list;
  funcVars: var StringMap.t;
  funcBody: block;
}

let function_print fmt f =
  match f.funcTyp with
  | None ->
    Format.fprintf fmt "void ";
    Format.fprintf fmt "%s( " f.funcName;
    List.iter (fun v -> Format.fprintf fmt "%a %a; " typ_print v.varTyp var_print v) f.funcArgs;
    Format.fprintf fmt "):\n";
    block_print "" fmt f.funcBody
  | Some v ->
    Format.fprintf fmt "%a " typ_print v.varTyp;
    Format.fprintf fmt "%s( " f.funcName;
    List.iter (fun v -> Format.fprintf fmt "%a %a; " typ_print v.varTyp var_print v) f.funcArgs;
    Format.fprintf fmt "):\n";
    block_print "" fmt f.funcBody

(* programs *)
type prog = (var StringMap.t) * block * (func StringMap.t)

let prog_print fmt (_,b,fs) = block_print "" fmt b; StringMap.iter (fun _ f -> function_print fmt f) fs

(* utility *)

let annotate e = (e, (Lexing.dummy_pos, Lexing.dummy_pos))
