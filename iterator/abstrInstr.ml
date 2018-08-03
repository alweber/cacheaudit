(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../LICENSE for authorship and licensing information    *)

(** Module defining types for the abstract instructions used by the 
[Iterator] to communicate with the abstract domains *)

type flag_op = Acmp | Atest 
            (* | ADfset of X86Types.flag*bool *)

type abstr_op = Aarith of X86Types.arith_op | Amov | Aexchg 
	| AShld  | AShrd 
	| Ashift of X86Types.shift_op | Aflag of flag_op
  | Aimul | Aset
	| Adiv | Aimullong | Amullong | Anot | Acmov of X86Types.cc
  | Acdq | Absr

type stack_op = Apop | Apush

(* type varop = Op of X86Types.arith_op | Move  *)

