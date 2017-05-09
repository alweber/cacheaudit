(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../LICENSE for authorship and licensing information    *)

open X86Types
open AD.DS

(** Architecture abstract domain: keeps track of the global state (currently:
    logical memory and caches), for use with an iterator *)

module type S =
sig
  include AD.S

  (** Creates an ArchitectureAD with given parameters. More specifically, in 
      [init cm sv dcp icp ba]     
       - [cm] is the executable,
       - [sv] are initial values of memory locations and registers,
       - [dcp] and [icp] are the configurations of data and instruction caches, and
       - [ba] is the base address of instructions.
  *)
    val init: X86Headers.t -> (((int64 * int64 * int64) list)*((reg32 * int64 * int64) list)) -> CacheAD.cache_param -> CacheAD.cache_param option -> int64 -> bool -> bool-> t
 
    
  (** For an op32 expression, returns a finite list of possible
      values, each value associated with an approximation of the
      corresponding memory states leading to that particular value. In
      case no finite list can be determied, returns Top. {b TODO: Is
      "get_offset" really a descriptive name? Why offset?}  *)
  val get_vals: t -> op32 -> (int,t) finite_set
    
  (** Returns an overapproximation of the environments in which the condition holds,
      followed by an overapproximation of the environments in which it doesn't. *)
  val test : t -> condition -> (t add_bottom)*(t add_bottom)
    
  (** Records a call and its effects on the stack. The first argument is the 
      address of the call, the second one is the return address. *)
  val call : t -> op32 -> int -> (int,t) finite_set 

  (** Records a return (and its effect on the stack). *)
  val return : t -> (int,t) finite_set

  (** Interpret an instruction, if the particular instruction cannot be handled 
      here, pass it to the next module *)
  val interpret_instruction : t -> X86Types.instr -> t
  

  (** Records the addresses of operations, which is required for instruction caches *)
  val read_instruction: t -> int -> t

  (** Signals from the iterator to the cache the time consumed by an
      instruction *)
  val elapse : t -> int -> t

end

(** Creates an ArchitectureAD with separate caches for data (represented by a StackAD) and instructions (represented by a CacheAD) *)
module MakeSeparate :
  functor (ST : StackAD.S) ->
    functor (IC : CacheAD.S) -> S

(** Creates an ArchitectureAD with shared cache for instruction and data *)
module MakeShared : functor (ST : StackAD.S) -> S

(** Creates an ArchitectureAD with data cache only *)
module MakeDataOnly : functor (ST : StackAD.S) -> S
