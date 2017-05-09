(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../../LICENSE for authorship and licensing information *)

open Big_int
open AD.DS
open Logger
open NumAD.DS


type cache_st = H | M | N | HM
(* Hit, Miss, No access, Hit or Miss *)
    
let duration_H, duration_M, duration_N = 3,20,1

let max_times = 10000000




module Make (CA : CacheAD.S) = struct
  
  type 'a parent_t = Root | Single of 'a | Couple of 'a * 'a
 

  type t = {
    cache : CA.t;
    times: IntSet.t add_top;
  }
  
  
  (* Calculates a hash given the current value of a node *)
  (* and the unique IDs of the parents*)
  let hash_node_parents value parent_UIDs = 
    Hashtbl.hash (value, parent_UIDs)

        
  
  let uid = ref 0
  


  let init cache_param acc accd=
    { cache = CA.init cache_param acc accd; times = Nt (IntSet.singleton 0)} 
        
  let get_single_parent = function
    | Single p -> p
    | _ -> failwith "TraceAD: only single parent is expected"
  

  let join_times times1 times2 = 
    match times1,times2 with
    | Nt tms1,Nt tms2 ->
      let tms = IntSet.union tms1 tms2 in
      if IntSet.cardinal tms < max_times then Nt tms else Tp
    | _,_ -> Tp
  
  let join env1 env2 =
    let cache = CA.join env1.cache env2.cache in
    let times = join_times env1.times env2.times in
    {cache = cache; times = times}
        
  let widen env1 env2 = 
    let cache = CA.widen env1.cache env2.cache in
    (* join_times goes to top at some point *)
    let times = join_times env1.times env2.times in
    {cache = cache; times = times}
  
  
  let subseteq env1 env2 = 
    let subeq_times = match env1.times,env2.times with
    | Nt tms1,Nt tms2 -> IntSet.subset tms1 tms2
    | _,Tp -> true
    | _,_ -> false in 
    (CA.subseteq env1.cache env2.cache) &&
    subeq_times
  
  let print fmt env =
    CA.print fmt env.cache;		
    Format.fprintf fmt "\n# times: ";
    match env.times with 
    | Tp -> Format.fprintf fmt "too imprecise to tell"
    | Nt tms ->
      let numtimes = float_of_int (IntSet.cardinal tms) in
      Format.fprintf fmt "%f, %f bits\n" 
        numtimes ((log10 numtimes)/.(log10 2.))
      

    (* N.B. This way of counting traces*)
    (* does not consider possible Error-states; *)
    
  let print_delta  env1 fmt env2 = 
    (* TODO: implement printing of delta of traces and times *)
    CA.print_delta env1.cache fmt env2.cache
  
  let print_status status = Printf.printf "status: %s\n"
        (match status with
        | H -> "Hit"
        | M -> "Miss"
        | HM -> "HorM"
        | N -> "None")
  
  let add_time time times = 
    match times with 
    | Tp -> Tp
    | Nt tms -> Nt (IntSet.fold (fun x tms ->
        IntSet.add (x + time) tms) tms IntSet.empty)
  
  let add_time_status status times = 
    match status with
    | H -> add_time duration_H times
    | M -> add_time duration_M times
    | N -> add_time duration_N times
    | HM -> 
      join_times (add_time duration_M times) (add_time duration_H times)
  
  
  let touch env addr rw =
    let c_hit,c_miss = CA.touch_hm env.cache addr rw in
    (* determine if status it is H or M or HM *)
    let cache,status = match c_hit,c_miss with
    | Bot,Bot -> raise Bottom
    | Nb c,Bot -> (c,H)
    | Bot,Nb c -> (c,M)
    | Nb c1,Nb c2   -> (CA.join c1 c2,HM) in
    if (get_log_level TraceLL = Debug) then 
      print_status status;
    (* Assume that because write-through cache is being used,*)
    (* a write-hit is perceived by attacker as a miss *)
    let status = if rw = Write && (status = H || status = HM) then M
      else status in
    let times = add_time_status status env.times in
    {cache = cache; times = times}

  (* Hitmiss tracking for touch_hm *)
  let touch_hm env addr rw =
    let c_hit,c_miss = CA.touch_hm env.cache addr rw in
    let nu_hit = match c_hit with
      | Nb c -> 
	Nb {  cache = c ;
  	    times = add_time_status H env.times}
      | Bot -> Bot
    in
    let nu_miss = match c_miss with
      | Nb c -> 
	Nb {  cache = c ;
  	    times = add_time_status M env.times}
      | Bot -> Bot
    in (nu_hit,nu_miss)




  let elapse env time = 
    let times = add_time time env.times in
    (* elapse is called after each instruction and adds an "N"-node; *)
    (* in the traces two consecutive N's will correspond to "no cache access"*)
    let times = add_time_status N times in
    {env with times = times}

  let count_cache_states env = CA.count_cache_states env.cache 

end

