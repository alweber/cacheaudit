(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../LICENSE for authorship and licensing information    *)

open X86Types
open AbstrInstr
open AD.DS
open NumAD.DS
open Logger

module type S = 
  sig

  include AD.S
  val init : (var->string) -> t
  val new_var : t -> var -> t
  val delete_var : t -> var -> t
  val log_var : t -> var -> unit
  val get_var : t -> var -> (t NumMap.t) add_top
  val set_var : t -> var -> int64 -> int64 -> t
  val meet : t -> t -> t (*TODO: should be add_bottom *)
  val update_val : t -> var -> mask -> cons_var -> mask -> abstr_op -> int64 option -> bool option -> t
  val update_val_noflags : t -> var -> mask -> cons_var -> mask -> abstr_op -> t	
	val update_val_twodst: t -> var -> mask -> var -> mask -> cons_var -> mask -> abstr_op -> t 	
  val updval_set : t -> var -> mask -> cc -> t
  val test : t -> condition -> (t add_bottom)*(t add_bottom)
  end

module Make (V: ValAD.S) = struct
  
  type t = V.t FlagMap.t
  
  let is_bottom env = FlagMap.is_empty env
	
  let print_flag flgs fmt env = 
    Format.fprintf fmt "@[<2>When CF is %B and ZF is %B and SF is %B and OF is %B, @,%a@]"
              flgs.cf flgs.zf flgs.sf flgs.o_f V.print env

 
			
	let print_delta_flag flgs st1 fmt st2 = match st1,st2 with
    | Bot, Bot -> ()
    | Bot, Nb env -> begin match get_log_level FlagLL with
      | Debug -> Format.fprintf fmt "@[New case: CF %B, ZF %B, SF %B, OF %B: @, @,%a@]"
             flgs.cf flgs.zf flgs.sf flgs.o_f V.print env 
      | _ -> ()
      end
    | Nb env, Bot -> begin match get_log_level FlagLL with
      | Debug -> Format.fprintf fmt "@[The case CF %B, ZF %B, SF %B, OF %B is no longer possible@]"
             flgs.cf flgs.zf flgs.sf flgs.o_f
      | _ -> ()
      end
    | Nb env1, Nb env2 -> begin match get_log_level FlagLL with
      | Debug -> if env1 != env2 then
             Format.fprintf fmt "@[Case CF %B, ZF %B, SF %B, OF %B: @, @,%a@]" flgs.cf flgs.zf flgs.sf flgs.o_f
             (V.print_delta env1) env2
      | _ -> Format.fprintf fmt "@[%a@]" (V.print_delta env1) env2
      end

  let print fmt st =
    if is_bottom st then Format.fprintf fmt "Flag domain is empty!@."
    else 
      Format.fprintf fmt "@[<hov 0>";
      FlagMap.iter (fun flgs vals -> print_flag flgs fmt vals) st;
      Format.fprintf fmt "@]"


  let print_delta st1 fmt st2 = 
    let get_values flgs fmap = try( 
          Nb (FlagMap.find flgs fmap)
        ) with Not_found -> Bot in
			let flgs_ttff, flgs_tfff, flgs_ftff, flgs_ffff, 
					flgs_ttft, flgs_tfft, flgs_ftft, flgs_ffft, 
					flgs_tttf, flgs_tftf, flgs_fttf, flgs_fftf, 
					flgs_tttt, flgs_tftt, flgs_fttt, flgs_fftt  = 
					{cf = true; zf = true; sf = false; o_f = false}, {cf = true; zf = false; sf = false; o_f = false}, 
					{cf = false; zf = true; sf = false; o_f = false}, {cf = false; zf = false; sf = false; o_f = false},
					{cf = true; zf = true; sf = false; o_f = true}, {cf = true; zf = false; sf = false; o_f = true}, 
					{cf = false; zf = true; sf = false; o_f = true}, {cf = false; zf = false; sf = false; o_f = true},	
					{cf = true; zf = true; sf = true; o_f = false}, {cf = true; zf = false; sf = true; o_f = false}, 
					{cf = false; zf = true; sf = true; o_f = false}, {cf = false; zf = false; sf = true; o_f = false},																				
					{cf = true; zf = true; sf = true; o_f = true}, {cf = true; zf = false; sf = true; o_f = true}, 
					{cf = false; zf = true; sf = true; o_f = true}, {cf = false; zf = false; sf = true; o_f = true}
					in
    Format.fprintf fmt "@[%a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a @; %a@]"
      (print_delta_flag flgs_ttff (get_values flgs_ttff st1)) (get_values flgs_ttff st2)
      (print_delta_flag flgs_tfff (get_values flgs_tfff st1)) (get_values flgs_tfff st2)
      (print_delta_flag flgs_ftff (get_values flgs_ftff st1)) (get_values flgs_ftff st2)
      (print_delta_flag flgs_ffff (get_values flgs_ffff st1)) (get_values flgs_ffff st2)		
      (print_delta_flag flgs_ttft (get_values flgs_ttft st1)) (get_values flgs_ttft st2)
      (print_delta_flag flgs_tfft (get_values flgs_tfft st1)) (get_values flgs_tfft st2)
      (print_delta_flag flgs_ftft (get_values flgs_ftft st1)) (get_values flgs_ftft st2)
      (print_delta_flag flgs_ffft (get_values flgs_ffft st1)) (get_values flgs_ffft st2)
      (print_delta_flag flgs_tttf (get_values flgs_tttf st1)) (get_values flgs_tttf st2)
      (print_delta_flag flgs_tftf (get_values flgs_tftf st1)) (get_values flgs_tftf st2)
      (print_delta_flag flgs_fttf (get_values flgs_fttf st1)) (get_values flgs_fttf st2)
      (print_delta_flag flgs_fftf (get_values flgs_fftf st1)) (get_values flgs_fftf st2)
      (print_delta_flag flgs_tttt (get_values flgs_tttt st1)) (get_values flgs_tttt st2)
      (print_delta_flag flgs_tftt (get_values flgs_tftt st1)) (get_values flgs_tftt st2)
      (print_delta_flag flgs_fttt (get_values flgs_fttt st1)) (get_values flgs_fttt st2)
      (print_delta_flag flgs_fftt (get_values flgs_fftt st1)) (get_values flgs_fftt st2)																					
			
      
  
  let init v2s = FlagMap.add initial_flags (V.init v2s) FlagMap.empty

(* Component-wise join *)
  
  let join env1 env2 = fmap_combine env1 env2 V.join

(* Component-wise meet *)

  let meet env1 env2 = let res = 
    FlagMap.merge (fun _ a b -> 
        match a,b with 
        | _ , None | None, _ -> None
        | Some x, Some y -> 
          begin match V.meet x y with
          | Bot -> None
          | Nb nenv -> Some nenv
          end
      ) env1 env2 in
    if is_bottom res then raise Bottom
    else res
      

(* Component-wise widening. *)
 let widen env1 env2 = fmap_combine env1 env2 V.widen

  let new_var st var = FlagMap.map (fun x -> V.new_var x var) st

  let delete_var st var = FlagMap.map (fun x -> V.delete_var x var) st

  let set_var st var l h = FlagMap.map (fun x -> V.set_var x var l h) st
 
  let log_var env v = let _ = FlagMap.map (fun x -> V.log_var v x; x) env in ()

  
  exception Is_Top
  let get_var st var = try(
    let res = 
      FlagMap.fold (fun flgs vals f_nmap -> 
        let v_nmap = match V.get_var vals var with 
        | Tp -> raise Is_Top 
        | Nt v_nmap -> v_nmap in
        NumMap.fold (fun num num_venv f_nmap -> 
          let f_nmap = if (NumMap.mem num f_nmap) then f_nmap 
            else (NumMap.add num FlagMap.empty f_nmap) in
          let flgenv = NumMap.find num f_nmap in
          NumMap.add num (FlagMap.add flgs num_venv flgenv) f_nmap 
        ) v_nmap f_nmap
      ) st NumMap.empty in
    Nt res
  ) with Is_Top -> Tp
    

 let subseteq st1 st2 = 
  FlagMap.for_all (fun flgs vals -> 
    FlagMap.mem flgs st2 && V.subseteq vals (FlagMap.find flgs st2)) st1

  let test_bot st = if is_bottom st then Bot else Nb st

  let test st cond = 
    let part1,part2 = match cond with
    (* B <-> CF set *)
    | B -> FlagMap.partition (fun flgs _ -> flgs.cf) st
    (* BE (below or equal) <-> CF or ZF set *)
    | BE -> FlagMap.partition (fun flgs _ -> flgs.cf || flgs.zf) st
    (* Z <-> ZF set *)  
    | Z -> FlagMap.partition (fun flgs _ -> flgs.zf) st
		 (* S <-> SF set *)
		| S -> FlagMap.partition (fun flgs _ -> flgs.sf) st
		(* O <-> OF set *)
		| O -> FlagMap.partition (fun flgs _ -> flgs.o_f) st
		(* LE (less or equal) <-> SF<>OF or ZF set *)
    | LE -> FlagMap.partition (fun flgs _ -> (flgs.sf <> flgs.o_f) || flgs.zf) st
		(* L (less) <-> SF<>OF *)
    | L -> FlagMap.partition (fun flgs _ -> (flgs.sf <> flgs.o_f)) st
    | _ -> failwith "Unsupported flag in test" in
    test_bot part1, test_bot part2


  (* For operations that do not change flags (e.g. Mov) update_val treats states independently and joins after update.
     For operations that do change flags, update_val joins before the operations 
     Further precision could be gained by separately treating operations (Inc) that leave some flags untouched *)
  let update_val env var mkvar cvar mkcvar op arg3 isimm_option = 
    match op with
    | Amov -> FlagMap.mapi (fun flgs vals -> 
        let fopmap = V.update_val vals flgs var mkvar cvar mkcvar op arg3 isimm_option in
          assert (FlagMap.cardinal fopmap = 1); 
          FlagMap.find flgs fopmap 
          ) env		
		| Anot -> FlagMap.mapi (fun flgs vals -> 
			(*Not does not change the flags. It is implemented using Xor which does change the flags. Hence,*)
			(* we discard the resulting flags and join all possible results for each initial flag valuation.*)
        let fopmap = V.update_val vals flgs var mkvar cvar mkcvar (Aarith Xor) arg3 isimm_option in
          assert (FlagMap.cardinal fopmap >= 1); 
					let _, some_result = FlagMap.choose fopmap in
          FlagMap.fold (fun flgs' vals' accumulator -> V.join accumulator vals'
					) fopmap some_result					
					) env		
    | _ -> let res =
        FlagMap.fold (fun flgs vals newmap -> 
            join newmap (V.update_val vals flgs var mkvar cvar mkcvar op arg3 isimm_option)
          ) env FlagMap.empty in
        if is_bottom res then raise Bottom;
        res
				
  let update_val_noflags env var mkvar cvar mkcvar op = 
    match op with				
		| Aarith Add | Aarith Sub -> FlagMap.mapi (fun flgs vals -> 
        let fopmap = V.update_val vals flgs var mkvar cvar mkcvar op None None in
          assert (FlagMap.cardinal fopmap = 1); 
					let _, some_result = FlagMap.choose fopmap in
          FlagMap.fold (fun flgs' vals' accumulator -> V.join accumulator vals'
					) fopmap some_result					
					) env		
		| _ -> assert false		
		
	let update_val_twodst env dst1var dst1mask dst2var dst2mask svar smask op =					
    match op with
		| Adiv | Aimullong | Amullong -> let res =
        FlagMap.fold (fun flgs vals newmap -> 
            join newmap (V.update_val_twodst vals flgs dst1var dst1mask dst2var dst2mask svar smask op)
          ) env FlagMap.empty in
        if is_bottom res then raise Bottom;
        res				
			| _ -> failwith "flagAD: The only supported operations with two destination operands are division and multiplication."
				
  let updval_set env var mask cc = let res =
    FlagMap.fold (fun flgs vals newmap -> 
            join newmap (V.updval_set vals flgs var mask cc)
          ) env FlagMap.empty in
        if is_bottom res then raise Bottom;
        res

end
