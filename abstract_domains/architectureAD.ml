(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../LICENSE for authorship and licensing information    *)

open X86Types
open AD.DS
open Logger


(* Architecture abstract domain. Right now it allows two different caches for instructions and data *)

let instruction_addr_base = ref (Int64.of_int 0)



module type S =
  sig
    include AD.S
    val init: X86Headers.t -> (((int64 * int64 * int64) list)*((reg32 * int64 * int64) list)) -> CacheAD.cache_param -> CacheAD.cache_param option -> int64 -> bool -> bool-> t
    val get_vals: t -> op32 -> (int,t) finite_set
    val test : t -> condition -> (t add_bottom)*(t add_bottom)
    val call : t -> op32 -> int -> (int,t) finite_set 
    val return : t -> (int,t) finite_set
    val interpret_instruction : t -> X86Types.instr -> t
    val read_instruction: t -> int -> t
    val elapse : t -> int -> t
  end



module MakeSeparate (ST: StackAD.S) (IC: CacheAD.S) = struct

  type t = {
    call_ad: ST.t;
    inst_ad: IC.t
  }

  let init concr_mem start_values data_cache_params inst_cache_params addr_base acc accd = 
    instruction_addr_base := addr_base;
    {
      call_ad = ST.init concr_mem start_values data_cache_params acc accd;
      inst_ad = IC.init (match inst_cache_params with
          Some(params) -> params
        | _ -> failwith "No/Invalid parameters supplied to instruction cache") acc accd
    }

  let subs_e env call_env = {env with call_ad=call_env}
  let subs_finite_set env fs = match fs with
    | Top(v) -> Top(subs_e env v)
    | Finite(l) -> Finite (List.map (fun (n,e) -> (n,subs_e env e)) l)

  
  let join env env2 = 
    let call_ad = ST.join env.call_ad env2.call_ad in
    let inst_ad = IC.join env.inst_ad env2.inst_ad in
    {call_ad = call_ad; inst_ad = inst_ad}
  
  let widen env env2 =
    let call_ad = ST.widen env.call_ad env2.call_ad in
    let inst_ad = IC.widen env.inst_ad env2.inst_ad in
    {call_ad = call_ad; inst_ad = inst_ad}

  let subseteq env env2 = ST.subseteq env.call_ad env2.call_ad && IC.subseteq env.inst_ad env2.inst_ad

  let test env cond = 
    let subs_nb = function
    | Bot -> Bot
    | Nb(v) -> Nb(subs_e env v) in
    let (l,r) = (ST.test env.call_ad cond) in
    (subs_nb l,subs_nb r)

  (* Redirect all usual stack calls to the stackAD *)
  let get_vals env op = subs_finite_set env (ST.get_vals env.call_ad op)
  let interpret_instruction env i = subs_e env (ST.interpret_instruction env.call_ad i)
  let call env op n = subs_finite_set env (ST.call env.call_ad op n)
  let return env = subs_finite_set env (ST.return env.call_ad)
  let print form env = (*match get_log_level ArchitectureLL with
    | Quiet -> ST.print form env.call_ad; IC.print form env.inst_ad
    | _ -> *)
    Format.fprintf form "@[<v 0>@;@;@;------ Data Cache -----@;@;%a@;@;@;-- Instruction Cache --@;@;%a@;@;-----------------------@;@;@;@]"
    ST.print env.call_ad IC.print env.inst_ad

  let print_delta env1 form env2 = match get_log_level ArchitectureLL with
    | Debug -> 
    Format.fprintf form "@[<v 0>@;@;@;------ Data Cache changes -----@;@;%a@;@;@;-- Instruction Cache changes --@;@;%a@;@;-----------------------@;@;@;@]"
    (ST.print_delta env1.call_ad) env2.call_ad (IC.print_delta env1.inst_ad) env2.inst_ad
    | _ -> ST.print_delta env1.call_ad form env2.call_ad; IC.print_delta env1.inst_ad form env2.inst_ad

  let elapse env t = {
    call_ad = ST.elapse env.call_ad t;
    inst_ad = IC.elapse env.inst_ad t
  }
  
  (* Note: in the following "touch" we only do reads *)
  let read_instruction env addr = { env with inst_ad = (IC.touch env.inst_ad (Int64.add (Int64.of_int addr) !instruction_addr_base) NumAD.DS.Read) }


end

module MakeShared (ST: StackAD.S) = struct

  type t = ST.t

  let init concr_mem start_values data_cache_params inst_cache_params addr_base =
    instruction_addr_base := addr_base;
    ST.init concr_mem start_values data_cache_params

  (* Redirect all usual stack calls to the stackAD *)
  let join = ST.join
  let widen = ST.widen
  let subseteq = ST.subseteq
  let get_vals = ST.get_vals
  let test = ST.test
  let interpret_instruction = ST.interpret_instruction
  let call = ST.call
  let return = ST.return
  let elapse = ST.elapse
  let print form env = ST.print form env
    
  let print_delta env1 form env2 = ST.print_delta env1 form env2
  
  (* Note: in the following "touch" we only do reads *)
  let read_instruction env addr = ST.touch env (Int64.add (Int64.of_int addr) !instruction_addr_base) NumAD.DS.Read

end


module MakeDataOnly (ST: StackAD.S) = struct
  include MakeShared (ST)

  let read_instruction env addr = env 
end


