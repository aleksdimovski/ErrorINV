(***************************************************)
(*                                                 *)
(*               Domain Partition                  *)
(*                                                 *)
(*             Aleksandar Dimovski                 *)
(*          Mother Teresa Uni, Skopje              *)
(*                   2018 - 2019                   *)
(*                                                 *)
(***************************************************)

open AbstractSyntax
open Apron
open Constraints


(** Signature for a single partition of the domain of a ranking function. *)
module type PARTITION = sig
  module C : CONSTRAINT

  type t
  val constraints : t -> C.t list
  val env : t -> Environment.t
  val vars : t -> var list
  val varsLive : t -> var list

  val bot : Environment.t -> var list -> t
  val inner : Environment.t -> var list -> C.t list -> t
  val top : Environment.t -> var list -> t
  
  val supports_underapproximation: bool 
  val isBot : t -> bool
  val isLeq : t -> t -> bool

  val toArr : t -> Apron.Lincons1.earray	(* this function extracts the earray from an PARTITION element*)
  val ofArr : Apron.Lincons1.earray -> Environment.t -> var list -> t  (* this function converts an earray to PARTITION element*)

  val join : t -> t -> t
  val widen : t -> t -> t
  val meet : t -> t -> t
  val lowerwiden : t -> t -> t
  val subset : Format.formatter -> t -> t -> t 

  val fwdAssign : t -> aExp * aExp -> t
  val bwdAssign : t -> aExp * aExp -> t
  val fwdAssign_bool : t -> aExp * bExp -> t
  val bwdAssign_bool : t -> aExp * bExp -> t  
  val bwdAssign_underapprox : t -> aExp * exp -> t
  
  val project : t -> aExp -> t 
  
  val filter : t -> bExp -> t
  val bwdfilter : t -> bExp -> t
  val bwdfilter_underapprox : t -> bExp -> t
  val bwdfilter_underapproxwhile : t -> t -> bExp -> t -> t

  val print : Format.formatter -> t -> unit
  val to_stringZ3 : t -> t -> string list
  val filter_list : string list -> t -> t
  val to_stringLatte : t -> var list -> (string list * int list * int)

end
