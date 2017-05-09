(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../LICENSE for authorship and licensing information    *)

open X86Types
open AbstrInstr
open AD.DS
open NumAD.DS

(** Flag abstract domain: keeps track of the relationship of flags and
    variable values.  *)

module type S = 
sig
  include AD.S

  (** Initializes an empty FlagAD by specifying how variable names
      are printed *)
  val init : (var->string) -> t

  (** Create new variable *)
  val new_var : t -> var -> t

  (** Delete variable *)
  val delete_var : t -> var -> t

  (** Log the current values of a variable to the log file. For automated testing *)
  val log_var : t -> var -> unit

  (** [get_var env var] returns the current values of a variable
      [var], in form of a Map from values of [var] to environments in
      which [var] has that value. This interface can be used to
      capture relational information between variables (but could be
      substituted by a simpler/more efficient one for non-relational
      domains) *)
  val get_var : t -> var -> (t NumMap.t) add_top
    
  (** [set_var env var l h] sets the value of [var] to be in the
      interval [l,h] *)
  val set_var : t -> var -> int64 -> int64 -> t

  (** Meet operation *)
  val meet : t -> t -> t 

  (** [update_var env dst mskdst src msksrc op arg3] performs operation
      [op] on [dst] and [src], where the masks [mskdst] and [msksrc]
      specify whether 8 or 32 bit of the operand are involved. 
      [arg3] is an optional argument currently only used for 3-argument IMUL. *)
  val update_val : t -> var -> mask -> cons_var -> mask -> abstr_op -> int64 option -> bool option -> t
	
  (** Version of update_val which discards the effect that the update has on the flags. 
	Currently used for supporting Push and Pop which do not affect the flags but whose semantics is 
	implemented by reusing arithmetic instructions that would usually change the flags.**)
  val update_val_noflags : t -> var -> mask -> cons_var -> mask -> abstr_op -> t		
	
	(** version of update_val which updates two destination variables. Currently it
	is used for division which stores the result in one variable and the remainder in 
	another variable.*)	
	val update_val_twodst: t -> var -> mask -> var -> mask -> cons_var -> mask -> abstr_op -> t 
  
  (** [updval_set env flags dst mask op] performs a Set-instruction *)
  val updval_set : t -> var -> mask -> cc -> t

  (** Returns a pair of environments overapproximating the
      true/false cases of condition *)
  val test : t -> condition -> (t add_bottom)*(t add_bottom)
  
end

(** Creates a flag abstract domain from a numeric abstract domain *)
module Make :
  functor (V : ValAD.S) -> S
