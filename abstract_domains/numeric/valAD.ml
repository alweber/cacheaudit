(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../../LICENSE for authorship and licensing information *)
open X86Types
  
open AbstrInstr
  
open AD.DS
  
open NumAD.DS
  
open Logger
  
(* We use a module for the options so that we can have different instances in the same analysis *)
module type VALADOPT =
  sig val max_get_var_size : int
         val max_set_size : int
            end
  
module ValADOptForMemory =
  struct let max_get_var_size = 256

            let max_set_size = 32
               end
  
let logFile = ref None
  
module type S =
  sig
    include AD.S
      
    val init : (var -> string) -> t
      
    val new_var : t -> var -> t
      
    val delete_var : t -> var -> t
      
    val log_var : var -> t -> unit
      
    val get_var : t -> var -> (t NumMap.t) add_top
      
    val set_var : t -> var -> int64 -> int64 -> t
      
    val is_var : t -> var -> bool
      
    val var_names : t -> NumSet.t
      
    val meet : t -> t -> t add_bottom
      
    val update_val :
      t ->
        flags_t ->
          var ->
            mask ->
              cons_var ->
                mask ->
                  AbstrInstr.abstr_op ->
                    int64 option -> bool option -> t FlagMap.t
      
    val update_val_twodst :
      t ->
        flags_t ->
          var ->
            mask ->
              var ->
                mask ->
                  cons_var -> mask -> AbstrInstr.abstr_op -> t FlagMap.t
      
    val updval_set :
      t -> flags_t -> var -> mask -> X86Types.cc -> t FlagMap.t
      
  end
  
module Make (O : VALADOPT) =
  struct
    (* A basic variable contains a 32 bits unsigned integer. *)
    (* Type of the abstract elements representing one variable *)
    type var_t = | FSet of NumSet.t | Interval of int64 * int64
    
    let min_elt = 0L
      
    let max_elt = 0xffffffffL
      
    let two32 = 0x100000000L
      
    let top = Interval (min_elt, max_elt)
      
    let is_top l h = (l = min_elt) && (h = max_elt)

    let rec interval_to_set l h =
      if l > h
      then NumSet.empty
      else NumSet.add l (interval_to_set (Int64.succ l) h)
      
    let set_to_interval s = Interval ((NumSet.min_elt s), (NumSet.max_elt s))
      
    let zero = FSet (NumSet.singleton 0L)
      
    let range_over (l, h) r =
      let range = Int64.sub h l
      in (range > (Int64.of_int max_int)) || ((Int64.to_int range) > r)
      
    type t = var_t VarMap.t
    
    let var_names env =
      let (keys, _) = List.split (VarMap.bindings env)
      in List.fold_left (fun set elt -> NumSet.add elt set) NumSet.empty keys
      
    (* TODO put this into the type t *)
    let variable_naming = ref (fun x -> "")
      
    let pp_var_vals fmt =
      function
      | FSet vals ->
          (Format.fprintf fmt "@[{";
           NumSet.iter (fun v -> Format.fprintf fmt "%Ld @," v) vals;
           Format.fprintf fmt "}@]")
      | Interval (l, h) ->
          if is_top l h
          then Format.fprintf fmt "Top"
          else Format.fprintf fmt "@[[%Ld, %Ld]@]" l h
      
    let var_vals_equal x1 x2 =
      match (x1, x2) with
      | (FSet s1, FSet s2) -> NumSet.equal s1 s2
      | (Interval (l1, h1), Interval (l2, h2)) -> (l1 = l2) && (h1 = h2)
      | (FSet s1, Interval (l2, h2)) | (Interval (l2, h2), FSet s1) ->
          ((NumSet.min_elt s1) = l2) &&
            (((NumSet.max_elt s1) = h2) &&
               (NumSet.equal s1 (interval_to_set l2 h2)))
      
    let print_one_var fmt v vals =
      Format.fprintf fmt "@[%s in %a@]@;" (!variable_naming v) pp_var_vals
        vals
      
    let log_var v env =
      let file =
        match !logFile with
        | None -> let f = open_out "log.txt" in (logFile := Some f; f)
        | Some f -> f in
      let log_var_vals =
        function
        | FSet vals ->
            (Printf.fprintf file "{";
             NumSet.iter (fun v -> Printf.fprintf file "%Ld " v) vals;
             Printf.fprintf file "}")
        | Interval (l, h) ->
            if is_top l h
            then Printf.fprintf file "Top"
            else Printf.fprintf file "[%Ld, %Ld]" l h
      in
        (Printf.fprintf file "%s " (!variable_naming v);
         log_var_vals (VarMap.find v env);
         Printf.fprintf file "\n")
      
    let print fmt env =
      (Format.fprintf fmt "@[<hov 0>";
       VarMap.iter (print_one_var fmt) env;
       Format.fprintf fmt "@]")
      
    (* We just print differing and new variables *)
    let print_delta env1 fmt env2 =
      match get_log_level ValLL with
      | Debug ->
          (Format.fprintf fmt "@[";
           VarMap.iter
             (fun v vals ->
                try
                  let old_vals = VarMap.find v env1
                  in
                    if not (var_vals_equal old_vals vals)
                    then print_one_var fmt v vals
                    else ()
                with | Not_found -> print_one_var fmt v vals)
             env2;
           Format.fprintf fmt "@]")
      | _ -> ()
      
    (* truncate a [number] to its [numbits] least significant bits *)
    let truncate numbits number =
      match numbits with
      | 32 -> Int64.logand number 0xFFFFFFFFL
      | 8 -> Int64.logand number 0xFFL
      | _ -> failwith "truncate: wrong argument"
      
    let set_map f set =
      NumSet.fold (fun x -> NumSet.add (f x)) set NumSet.empty
      
    (* Mask values and shift them to the right *)
    let apply_mask mask shift x =
      Int64.shift_right_logical (Int64.logand mask x) shift
      
    let mask_vals mask v =
      match mask with
      | NoMask -> v
      | Mask msk ->
          let (cv_mask, cv_shift) = mask_to_intoff msk in
          let am = apply_mask cv_mask cv_shift
          in
            (match v with
             | FSet s -> FSet (set_map am s)
             | Interval (l, h) -> Interval (0L, 0xFFL)
								)
      
			
    (* Flag setting functions *)
    let is_cf _ _ res = (res < min_elt) || (res > max_elt)
    let is_zf res = (truncate 32 res) = 0L     
	  let is_sf _ _ res = Some ((Int64.shift_right_logical (truncate 32 res) 31) = 1L)		
    let is_of dst _ res =
      Some ((Int64.shift_right_logical (truncate 32 dst) 31) <>
        (Int64.shift_right_logical (truncate 32 res) 31))			
			
		let is_of_sub dst src res =
      Some (((Int64.shift_right_logical (truncate 32 dst) 31) <>
        (Int64.shift_right_logical (truncate 32 res) 31))	&&
				((Int64.shift_right_logical (truncate 32 dst) 31) <>
        (Int64.shift_right_logical (truncate 32 src) 31)))				

			
			
		(*functions for setting flags after shift operations*)			
    let is_cf_shift sop original offset result =
      let carry =
        match sop with
        | Shl | Rol -> Int64.logand result (Int64.shift_left Int64.one 32)
        | Shr | Sar | Ror ->
            let mask =
              Int64.shift_left Int64.one (Int64.to_int (Int64.pred offset))
            in Int64.logand mask original
      in carry <> Int64.zero
		let is_sf_shift sop previous_sf original offset result =
			if offset = 0L then Some previous_sf else
			match sop with 
			| Rol | Ror -> Some previous_sf
			| Shl | Sar | Shr -> (is_sf original offset result)      
		let is_of_shift sop previous_of original offset result =
			if offset = 0L then Some previous_of else
			match sop with
			| Shr | Sar -> if offset = 1L then (Some false) else None
			| Shl | Rol | Ror -> if offset = 1L 
				then Some ((is_sf result result result) <> (is_sf original original original)) else None
			
		let is_cf_nop previous_cf _ _ _ = previous_cf	
			
		(*functions for setting flags after logic operations*)
		let is_cf_logic _ _ _ = false
		let is_of_logic _ _ _ = Some false
		let is_zf_logic_32 res = is_zf res 
		let is_sf_logic_32 a b res = is_sf a b res 		
		let is_zf_logic_8 res = (truncate 8 res) = 0L
    let is_sf_logic_8 _ _ res = (Int64.shift_right_logical (truncate 8 res) 7) = 1L

	
								
      
    (* for 32 bits operations *)
    (* set_or_interval given two bounds either returns an interval or a set if its size is less than O.max_set_size *)
    let set_or_interval l h =
      if range_over (l, h) O.max_set_size
      then Interval (l, h)
      else FSet (interval_to_set l h)
      
    let init v2s = (variable_naming := v2s; VarMap.empty)
      
    let new_var m v = VarMap.add v top m
      
    let delete_var m v = VarMap.remove v m
      
    let is_var m vn = VarMap.mem vn m
      
    let get_var m v =
      try
        match VarMap.find v m with
        | FSet l ->
            Nt
              (NumSet.fold
                 (fun vl env ->
                    NumMap.add vl
                      (VarMap.add v (FSet (NumSet.singleton vl)) m) env)
                 l NumMap.empty)
        | Interval (l, h) ->
            if range_over (l, h) O.max_get_var_size
            then Tp
            else
              (let rec f l h =
                 if l > h
                 then NumMap.empty
                 else
                   NumMap.add l (VarMap.add v (FSet (NumSet.singleton l)) m)
                     (f (Int64.succ l) h)
               in Nt (f l h))
      with
      | Not_found ->
          failwith
            (Printf.sprintf "valAD.get_var: non-existent variable %Lx\n" v)
      
    let set_var m v l h = VarMap.add v (set_or_interval l h) m
      
    let get_vals c m =
      match c with
      | Cons cs -> FSet (NumSet.singleton (truncate 32 cs))
      | VarOp v ->
          (try VarMap.find v m
           with | Not_found -> failwith "valAD.get_vals: inexistent variable")
      
    let same_vars v cv = match cv with | VarOp v2 -> v = v2 | Cons _ -> false
      
    let var_join x y =
      match (x, y) with
      | (FSet s1, FSet s2) ->
          let s = NumSet.union s1 s2
          in
            if (NumSet.cardinal s) > O.max_set_size
            then set_to_interval s
            else FSet s
      | (Interval (l, h), FSet s) | (FSet s, Interval (l, h)) ->
          Interval ((min l (NumSet.min_elt s)), (max h (NumSet.max_elt s)))
      | (Interval (l1, h1), Interval (l2, h2)) ->
          Interval ((min l1 l2), (max h1 h2))
      
    let join (x : t) (y : t) =
      let f k a b =
        match (a, b) with
        | (Some c, Some d) -> Some (var_join c d)
        | (* f should never enter this case *) _ ->
            (Printf.printf "Missing: %Lx\n" k; assert false)
      in (* Disjoint variables *) VarMap.merge f x y
      
    let var_meet x y =
      match (x, y) with
      | (FSet s1, FSet s2) ->
          let s = NumSet.inter s1 s2
          in if NumSet.is_empty s then raise Bottom else FSet s
      | (Interval (l, h), FSet s) | (FSet s, Interval (l, h)) ->
          let rs = NumSet.filter (fun x -> (x >= l) && (x <= h)) s
          in if NumSet.is_empty rs then raise Bottom else FSet rs
      | (Interval (l1, h1), Interval (l2, h2)) ->
          let l = max l1 l2 in
          let h = min h1 h2
          in
            if l > h
            then raise Bottom
            else
              if range_over (l, h) O.max_set_size
              then Interval (l, h)
              else FSet (interval_to_set l h)
      
    let meet x y =
      let f k a b =
        match (a, b) with
        | (Some c, Some d) -> Some (var_meet c d)
        | (* f should never enter this case *) (_, None) | (None, _) ->
            failwith "Disjoint variables in valAD.meet"
      in try Nb (VarMap.merge f x y) with | Bottom -> Bot
      
    let var_widen x y =
      match (x, y) with
      | (FSet s1, FSet s2) ->
          let s = NumSet.union s1 s2
          in
            if (NumSet.cardinal s) > O.max_set_size
            then set_to_interval s
            else FSet s
      | (Interval (l, h), FSet s) | (FSet s, Interval (l, h)) ->
          Interval ((min l (NumSet.min_elt s)), (max h (NumSet.max_elt s)))
      | (Interval (l1, h1), Interval (l2, h2)) ->
          let l = if l2 < l1 then min_elt else l1 in
          let h = if h2 > h1 then max_elt else h1 in Interval (l, h)
      
    let widen x y = (*let pp_one_var v fmt k = print_one_var fmt k v in*)
      let f k a b =
        match (a, b) with
        | (Some c, Some d) -> Some (var_widen c d)
        | (* f should never enter this case *) (_, None) | (None, _) ->
            failwith "Disjoint variables in valAD.widen"
      in VarMap.merge f x y
      
    let var_subseteq x y =
      match (x, y) with
      | (FSet s1, FSet s2) -> NumSet.subset s1 s2
      | (FSet s, Interval (l, h)) ->
          ((NumSet.min_elt s) >= l) && ((NumSet.max_elt s) <= h)
      | (Interval (l, h), FSet s) ->
          let res = ref true in
          let i = ref l
          in
            (while !res && (!i <= h) do res := NumSet.mem !i s;
               i := Int64.succ !i done;
             !res)
      | (Interval (l1, h1), Interval (l2, h2)) -> (l1 >= l2) && (h1 <= h2)
      
    exception Not_included
      
    let subseteq x y =
      let f k a b =
        match (a, b) with
        | (Some c, Some d) ->
            if var_subseteq c d then None else raise Not_included
        | (Some c, _) -> raise Not_included
        | (_, Some d) -> None
        | (_, _) -> None
      in try (ignore (VarMap.merge f x y); true) with | Not_included -> false
      
    (* lifts to interval representation if needed *)
    let lift_to_interval s =
      if (NumSet.cardinal s) > O.max_set_size
      then set_to_interval s
      else FSet s
      
    let fmap_find_with_defval key defval fm =
      try FlagMap.find key fm with | Not_found -> defval
      
    let perform_op op dstset srcset cf_test zf_test sf_test of_test =
      let compute_op dst =
        NumSet.fold
          (fun src (dmap, smap, rmap) ->
             let result = op dst src in
	            match (sf_test dst src result),(of_test dst src result) with 
						  | Some new_sf, Some new_of ->
							let flags =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = new_sf;
                 o_f = new_of;
               } in
             let dvals = fmap_find_with_defval flags NumSet.empty dmap in
             let dstmap = FlagMap.add flags (NumSet.add dst dvals) dmap in
             let svals = fmap_find_with_defval flags NumSet.empty smap in
             let srcmap = FlagMap.add flags (NumSet.add src svals) smap in
             let rvals = fmap_find_with_defval flags NumSet.empty rmap in
             let resmap =
               FlagMap.add flags (NumSet.add (truncate 32 result) rvals) rmap
             in (dstmap, srcmap, resmap)
						| Some new_sf, None -> 
							let flags1 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = new_sf;
                 o_f = true;
               } in
							let flags2 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = new_sf;
                 o_f = false;
               } in							
             let dvals1 = fmap_find_with_defval flags1 NumSet.empty dmap in
             let dvals2 = fmap_find_with_defval flags2 NumSet.empty dmap in						
             let dstmap = FlagMap.add flags1 (NumSet.add dst dvals1) (FlagMap.add flags2 (NumSet.add dst dvals2) dmap) in					
						 let svals1 = fmap_find_with_defval flags1 NumSet.empty smap in						
             let svals2 = fmap_find_with_defval flags2 NumSet.empty smap in
             let srcmap = FlagMap.add flags1 (NumSet.add src svals1) (FlagMap.add flags2 (NumSet.add src svals2) smap) in					
             let rvals1 = fmap_find_with_defval flags1 NumSet.empty rmap in						
             let rvals2 = fmap_find_with_defval flags2 NumSet.empty rmap in
             let resmap =
               FlagMap.add flags1 (NumSet.add (truncate 32 result) rvals1) (FlagMap.add flags2 (NumSet.add (truncate 32 result) rvals2) rmap)
             in (dstmap, srcmap, resmap)						
						| None, Some new_of -> 
							let flags1 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = true;
                 o_f = new_of;
               } in
							let flags2 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = false;
                 o_f = new_of;
               } in							
             let dvals1 = fmap_find_with_defval flags1 NumSet.empty dmap in
             let dvals2 = fmap_find_with_defval flags2 NumSet.empty dmap in						
             let dstmap = FlagMap.add flags1 (NumSet.add dst dvals1) (FlagMap.add flags2 (NumSet.add dst dvals2) dmap) in					
						 let svals1 = fmap_find_with_defval flags1 NumSet.empty smap in						
             let svals2 = fmap_find_with_defval flags2 NumSet.empty smap in
             let srcmap = FlagMap.add flags1 (NumSet.add src svals1) (FlagMap.add flags2 (NumSet.add src svals2) smap) in					
             let rvals1 = fmap_find_with_defval flags1 NumSet.empty rmap in						
             let rvals2 = fmap_find_with_defval flags2 NumSet.empty rmap in
             let resmap =
               FlagMap.add flags1 (NumSet.add (truncate 32 result) rvals1) (FlagMap.add flags2 (NumSet.add (truncate 32 result) rvals2) rmap)
             in (dstmap, srcmap, resmap)							
										
						| None, None -> 
							let flags1 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = true;
                 o_f = true;
               } in
							let flags2 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = false;
                 o_f = true;
               } in				
							let flags3 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = true;
                 o_f = false;
               } in
							let flags4 =
               {
                 cf = cf_test dst src result;
                 zf = zf_test result;
                 sf = false;
                 o_f = false;
               } in	
             let dvals1 = fmap_find_with_defval flags1 NumSet.empty dmap in
             let dvals2 = fmap_find_with_defval flags2 NumSet.empty dmap in					
             let dvals3 = fmap_find_with_defval flags3 NumSet.empty dmap in
             let dvals4 = fmap_find_with_defval flags4 NumSet.empty dmap in																
             let dstmap = 
							FlagMap.add flags3 (NumSet.add dst dvals3)
							(FlagMap.add flags4 (NumSet.add dst dvals4)							
							(FlagMap.add flags1 (NumSet.add dst dvals1)
							(FlagMap.add flags2 (NumSet.add dst dvals2) dmap))) in												
						 let svals1 = fmap_find_with_defval flags1 NumSet.empty smap in						
             let svals2 = fmap_find_with_defval flags2 NumSet.empty smap in
						 let svals3 = fmap_find_with_defval flags3 NumSet.empty smap in						
             let svals4 = fmap_find_with_defval flags4 NumSet.empty smap in						
             let srcmap = 
							FlagMap.add flags4 (NumSet.add src svals4) 
							(FlagMap.add flags3 (NumSet.add src svals3) 
							(FlagMap.add flags1 (NumSet.add src svals1) 
						  (FlagMap.add flags2 (NumSet.add src svals2) smap))) in					
             let rvals1 = fmap_find_with_defval flags1 NumSet.empty rmap in						
             let rvals2 = fmap_find_with_defval flags2 NumSet.empty rmap in
             let rvals3 = fmap_find_with_defval flags3 NumSet.empty rmap in						
             let rvals4 = fmap_find_with_defval flags4 NumSet.empty rmap in												
             let resmap =
               FlagMap.add flags4 (NumSet.add (truncate 32 result) rvals4)							
               (FlagMap.add flags3 (NumSet.add (truncate 32 result) rvals3)							
               (FlagMap.add flags1 (NumSet.add (truncate 32 result) rvals1) 
							 (FlagMap.add flags2 (NumSet.add (truncate 32 result) rvals2) rmap)))
             in (dstmap, srcmap, resmap)								
						)									
		       srcset (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
      let (dstmap, srcmap, resmap) =
        NumSet.fold
          (fun dst (new_d, new_s, new_r) ->
             let (dstvals, srcvals, resvals) = compute_op dst
             in
               ((fmap_combine dstvals new_d NumSet.union),
                (fmap_combine srcvals new_s NumSet.union),
                (fmap_combine resvals new_r NumSet.union)))
          dstset (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
      let dstmap = FlagMap.map (fun nums -> lift_to_interval nums) dstmap in
      let srcmap = FlagMap.map (fun nums -> lift_to_interval nums) srcmap in
      let resmap = FlagMap.map (fun nums -> lift_to_interval nums) resmap
      in (dstmap, srcmap, resmap)
      
     
    let perform_op_int8 op dstset dmask srcset smask cf_test zf_test sf_test
                        of_test =
      let (s_mask, s_shift) = mask_to_intoff smask in
      let (d_mask, d_shift) = mask_to_intoff dmask in
      let compute_op dst =
        NumSet.fold
          (fun src (dmap, smap, rmap) ->
             (*compute the result for the 8-bit values*)
             let src_shifted_masked =
               Int64.shift_right (Int64.logand src s_mask) s_shift in
             let dst_shifted_masked =
               Int64.shift_right (Int64.logand dst d_mask) d_shift in
             let res_8bit =
               truncate 8 (op dst_shifted_masked src_shifted_masked) in
             (*embed the result into the remaining bits of the destination variable*)
             let dst_rest = Int64.logand (Int64.lognot d_mask) dst in
             let res8_shifted = Int64.shift_left res_8bit d_shift in
             let result = Int64.logor dst_rest res8_shifted in
             (*The flags refer to the 8-bit result*)
             match of_test dst src res_8bit with | Some new_of ->
							let flags =
               {
                 cf = cf_test dst src res_8bit;
                 zf = zf_test res_8bit;
                 sf = sf_test dst src res_8bit;
                 o_f = new_of;
               } in
             let dvals = fmap_find_with_defval flags NumSet.empty dmap in
             let dstmap = FlagMap.add flags (NumSet.add dst dvals) dmap in
             let svals = fmap_find_with_defval flags NumSet.empty smap in
             let srcmap = FlagMap.add flags (NumSet.add src svals) smap in
             let rvals = fmap_find_with_defval flags NumSet.empty rmap in
             (*the truncation to 32 is not really necessary for xor, but should not harm*)
             let resmap =
               FlagMap.add flags (NumSet.add (truncate 32 result) rvals) rmap
             in (dstmap, srcmap, resmap)
						| None -> 
							let flags1 =
               {
                 cf = cf_test dst src res_8bit;
                 zf = zf_test res_8bit;
                 sf = sf_test dst src res_8bit;
                 o_f = true;
               } in
							let flags2 =
               {
                 cf = cf_test dst src res_8bit;
                 zf = zf_test res_8bit;
                 sf = sf_test dst src res_8bit;
                 o_f = false;
               } in							
             let dvals1 = fmap_find_with_defval flags1 NumSet.empty dmap in
             let dvals2 = fmap_find_with_defval flags2 NumSet.empty dmap in						
             let dstmap = FlagMap.add flags1 (NumSet.add dst dvals1) (FlagMap.add flags2 (NumSet.add dst dvals2) dmap) in					
						 let svals1 = fmap_find_with_defval flags1 NumSet.empty smap in						
             let svals2 = fmap_find_with_defval flags2 NumSet.empty smap in
             let srcmap = FlagMap.add flags1 (NumSet.add src svals1) (FlagMap.add flags2 (NumSet.add src svals2) smap) in
						
             let rvals1 = fmap_find_with_defval flags1 NumSet.empty rmap in						
             let rvals2 = fmap_find_with_defval flags2 NumSet.empty rmap in
             (*the truncation to 32 is not really necessary for xor, but should not harm*)
             let resmap =
               FlagMap.add flags1 (NumSet.add (truncate 32 result) rvals1) (FlagMap.add flags2 (NumSet.add (truncate 32 result) rvals2) rmap)
             in (dstmap, srcmap, resmap)						
						)						
          srcset (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
      let (dstmap, srcmap, resmap) =
        NumSet.fold
          (fun dst (new_d, new_s, new_r) ->
             let (dstvals, srcvals, resvals) = compute_op dst
             in
               ((fmap_combine dstvals new_d NumSet.union),
                (fmap_combine srcvals new_s NumSet.union),
                (fmap_combine resvals new_r NumSet.union)))
          dstset (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
      let dstmap = FlagMap.map (fun nums -> lift_to_interval nums) dstmap in
      let srcmap = FlagMap.map (fun nums -> lift_to_interval nums) srcmap in
      let resmap = FlagMap.map (fun nums -> lift_to_interval nums) resmap
      in (dstmap, srcmap, resmap)
      
    (* Functions used by update_val *)
    let arithop_to_int64op =
      function
      | Add -> Int64.add
      | Addc -> Int64.add
      | And -> Int64.logand
      | CmpOp ->
          failwith "CmpOp should be handled by flagop instead of memop"
      | Or -> Int64.logor
      | Sub -> Int64.sub
      | Subb -> Int64.sub
      | Xor -> Int64.logxor
			| Inc -> Int64.add
			| Dec -> Int64.sub
			| Neg ->  (fun x y -> Int64.sub y x)
      
    let make_set_from_list =
      List.fold_left (fun s x -> NumSet.add x s) NumSet.empty
      
    type position = | TT | TF | FT | FF
    
    (* Wrapper function for var_meet; we need the intersection without raising Bottom *)
    let var_meet_ab x y = try Nb (var_meet x y) with | Bottom -> Bot
      
    (* Applies op to each element of the FSet or the bounds of the Interval *)
    let mapt op =
      function
      | FSet s -> FSet (set_map op s)
      | Interval (l, h) -> Interval ((op l), (op h))
      
    (* Functions for bitwise interval operations 
   * Based on http://www.cs.utah.edu/~regehr/papers/lctes06_2/ *)
    let coef x k = let twok = Int64.shift_left 1L k in Int64.div x twok
      
    (* Zeroes the k-th bit of the interval *)
    let killBit interval k =
      let even x = (Int64.rem x 2L) = 0L in
      let twok = Int64.shift_left 1L k
      in
        match interval with
        | Interval (l, h) ->
            let ch = coef h k in
            let cl = coef l k in
            let ub =
              if even ch
              then h
              else
                if l < (Int64.mul ch twok)
                then Int64.mul ch twok
                else Int64.sub h twok in
            let lb =
              if not (even cl)
              then Int64.sub l twok
              else
                if h >= (Int64.mul twok (Int64.succ cl))
                then Int64.mul cl twok
                else l
            in Interval (lb, ub)
        | _ -> raise (Invalid_argument "killBit")
      
    let isBitSet x bit =
      (Int64.logand (Int64.shift_left 1L bit) x) <> Int64.zero
      
    let get_bounds =
      function
      | Interval (l, h) -> (l, h)
      | _ -> raise (Invalid_argument "get_bounds")
      
    (* Function to compute the "contributing" bits of the interval *)
    let loopBound ai bi bound =
      let testbound = bound (get_bounds bi) in
      let newai = ref ai
      in
        (for i = 31 downto 0 do
           if isBitSet testbound i then newai := killBit !newai i else ()
         done;
         bound (get_bounds !newai))

      
    (* Bitwise or for intervals *)
    let interval_or a b =
      match (a, b) with
      | (Interval (al, ah), Interval (bl, bh)) ->
          let (lma, lmb) = ((loopBound a b fst), (loopBound b a fst)) in
          let (hma, hmb) = ((loopBound a b snd), (loopBound b a snd)) in
          let lowerBound = min (Int64.logor al lmb) (Int64.logor bl lma) in
          let upperBound = max (Int64.logor ah hmb) (Int64.logor ah hma)
          in Interval (lowerBound, upperBound)
      | (_, _) -> raise (Invalid_argument "interval_or")

      
    (* Bitwise not for intervals *)
    let interval_not =
      function
      | Interval (l, h) ->
          let f x = truncate 32 (Int64.lognot x) in Interval ((f h), (f l))
      | _ -> raise (Invalid_argument "interval_not")
          
    (* Bitwise and for intervals defined using or and not *)
    let interval_and a b = (* a & b = not (not a | not b) *)
      interval_not (interval_or (interval_not a) (interval_not b))
      
    (* interval_operation takes an operation and two intervals and returns the resulting
   * interval after applying the operation (which must be monotonic) *)
    let interval_operation oper x y =
      match (x, y) with
      | (Interval (dl, dh), Interval (sl, sh)) ->
          let bound f =
            List.fold_left f (oper dl sl)
              [ oper dl sh; oper dh sl; oper dh sh ] in
          let (lb, ub) = ((bound min), (bound max))
          in (assert (ub >= lb); Interval (lb, ub))
      | (_, _) -> raise (Invalid_argument "interval_operation")
      
    let to_interval = function | FSet s -> set_to_interval s | i -> i
      
    (* interval_arith takes a flg : position = {TT,...,FF}, an arith_op aop,
   * the Int64 operation oper and two intervals *)
    let interval_arith env aop oper dstvar dst_vals src_vals =
      let (dst_vals, src_vals) =
        ((to_interval dst_vals), (to_interval src_vals)) in
      let retmap = FlagMap.empty in (* Interval after operation *)
      let inter =
        match aop with
        | Add | Addc | Sub | Subb | Neg->
            interval_operation oper dst_vals src_vals
        | And | Or | Xor ->
            (match aop with
             | And -> interval_and dst_vals src_vals
             | Or -> interval_or dst_vals src_vals
             | Xor -> (* a xor b = (a & not b) or (b & not a) *)
                 let f a b = interval_and a (interval_not b)
                 in interval_or (f dst_vals src_vals) (f src_vals dst_vals)
             | _ -> assert false)
        | _ -> assert false in
      (* Can set ZF only if result only contains zero *)
      let retmap =
        match var_meet_ab inter (FSet (NumSet.singleton min_elt)) with
        | Nb z ->
					(match aop with
					| And | Or | Xor ->		
						(FlagMap.add { cf = false; zf = true; sf = false; o_f = false; } z
              retmap)						
					| Add | Addc | Sub | Subb | Neg ->	
						(FlagMap.add { cf = false; zf = true; sf = true; o_f = false; } z					
						(FlagMap.add { cf = false; zf = true; sf = false; o_f = false; } z
						(FlagMap.add { cf = false; zf = true; sf = false; o_f = true; } z
            (FlagMap.add { cf = false; zf = true; sf = true; o_f = true; } z
              retmap))))
					| _ -> assert false)
        | _ -> retmap in
      let meetNormal =
        var_meet_ab inter (Interval ((Int64.succ min_elt), max_elt)) in
      (* Can set not CF and not ZF if interval is in normal range *)
      (* not CF not ZF if no zero and no under *)
      let retmap =
        match meetNormal with
        | Nb n ->
					(match aop with
					| And | Or | Xor ->
					FlagMap.add { cf = false; zf = false; sf = true; o_f = false; } n 				
					(FlagMap.add { cf = false; zf = false; sf = false; o_f = false; }  					
              n retmap)						
					| Add | Addc | Sub | Subb | Neg->							
					FlagMap.add { cf = false; zf = false; sf = true; o_f = false; } n 
					(FlagMap.add { cf = false; zf = false; sf = false; o_f = true; } n 					
					(FlagMap.add { cf = false; zf = false; sf = false; o_f = false; } n 					
            (FlagMap.add { cf = false; zf = false; sf = true; o_f = true; }
              n retmap)))
					| _ -> assert false)
        | _ -> retmap in
      let modulo_add x = Int64.sub x two32 in
      let modulo_sub x = Int64.add two32 x in
      let retmap =
        match aop with
        | Add | Addc -> (* Can set CF & ZF only if result is 2^32 *)
            (match var_meet_ab inter (FSet (NumSet.singleton two32)) with
             | Nb z2 ->
							(FlagMap.add { cf = true; zf = true; sf = false; o_f = false; } (mapt modulo_add z2)
							(FlagMap.add { cf = true; zf = true; sf = false; o_f = true; } (mapt modulo_add z2) retmap))
             | _ -> retmap)
        | _ -> retmap in
      let retmap =
        match aop with
        | Add | Addc ->
            let meetOver =
              var_meet_ab inter
                (Interval ((Int64.succ two32),
                   (Int64.sub (Int64.add two32 two32) 2L)))
            in
              (* Can set CF & not ZF if ub is > than 2^32 and does not contain zero *)
              (match (meetNormal, meetOver) with
               | (Nb n, Nb o) ->
								   FlagMap.add
                     { cf = true; zf = false; sf = true; o_f = true; }
                     (var_join n (mapt modulo_add o))
									(FlagMap.add
                     { cf = true; zf = false; sf = true; o_f = false; }
                     (var_join n (mapt modulo_add o))
								  (FlagMap.add
                     { cf = true; zf = false; sf = false; o_f = false; }
                     (var_join n (mapt modulo_add o))
                  (FlagMap.add
                     { cf = true; zf = false; sf = false; o_f = true; }
                     (var_join n (mapt modulo_add o)) retmap)))
               | (Bot, Nb o) ->
                   FlagMap.add
                     { cf = true; zf = false; sf = false; o_f = false; }
                     (mapt modulo_add o) 							
                   (FlagMap.add
                     { cf = true; zf = false; sf = true; o_f = false; }
                     (mapt modulo_add o) 
                   (FlagMap.add
                     { cf = true; zf = false; sf = true; o_f = true; }
                     (mapt modulo_add o) 																																																																														
                   (FlagMap.add
                     { cf = true; zf = false; sf = false; o_f = true; }
                     (mapt modulo_add o) retmap)))
               | (_, _) -> retmap)
        | Sub | Subb | Neg ->
            let meetUnder =
              var_meet_ab inter
                (Interval ((Int64.sub 1L two32),(Int64.pred min_elt)))
            in
              (* CF not ZF if under *)
              (match meetUnder with
               | Nb u ->
                   FlagMap.add
                     { cf = true; zf = false; sf = true; o_f = false; }
                     (mapt modulo_sub u)
                   (FlagMap.add
                     { cf = true; zf = false; sf = false; o_f = false; }
                     (mapt modulo_sub u)
                   (FlagMap.add
                     { cf = true; zf = false; sf = true; o_f = true; }
                     (mapt modulo_sub u)																																																														
                   (FlagMap.add
                     { cf = true; zf = false; sf = false; o_f = true; }
                     (mapt modulo_sub u) retmap)))
               | _ -> retmap)
        | _ -> retmap
      in FlagMap.map (fun nums -> VarMap.add dstvar nums env) retmap
      
    let bool_to_int64 = function | true -> 1L | false -> 0L
      
    (* Stores the new values of the dstvar (possibly updated from the computation)*)
    (* as well as the src_cvar values if the source is a variable.*)
    (* Both values are partitioned into the ones corresponding to any of the *)
    (* possible flag combinations *)
    let store_vals env dstvar dstmap src_cvar srcmap =
      FlagMap.mapi
        (fun flgs dvals ->
           let env =
             match src_cvar with
             | VarOp var -> VarMap.add var (FlagMap.find flgs srcmap) env
             | Cons _ -> env
           in VarMap.add dstvar dvals env)
        dstmap
      
    (* Implements the effects of arithmetic operations *)
    let arith env flgs_init dstvar dst_vals srcvar src_vals aop =
      match aop with
      | Xor when same_vars dstvar srcvar -> (*Then the result is 0 *)
          (*CF and OF are always 0 after logic operations. ZF is 1 because the result is 0.*)
          (* SF is 0 because the result is 0*)
          FlagMap.singleton
            { cf = false; zf = true; sf = false; o_f = false; }
            (VarMap.add dstvar zero env)
      | _ ->
          (* Add carry flag value to operation if it's either Addc or Subb *)
          let oper x y =
            let y =
              (match aop with
               | Addc | Subb -> Int64.add y (bool_to_int64 flgs_init.cf)
               | _ -> y)
            in arithop_to_int64op aop x y
          in
            (match (dst_vals, src_vals) with
             | (FSet dset, FSet sset) ->
                 let (_, srcmap, resmap) =
                   (match aop with
										| Inc | Dec ->
											perform_op oper dset sset (is_cf_nop flgs_init.cf) is_zf is_sf is_of
										| Xor | And | Or ->
                        perform_op oper dset sset is_cf_logic is_zf_logic_32 is_sf_logic_32
                          is_of_logic
										| Neg -> 			
                        perform_op oper dset sset is_cf is_zf is_sf (fun dst src res -> is_of src dst res)
												 (*Negation is implemented by substrating from dst from src. *)
												(* Hence, dst and src must be passed to is_of in reverse order.*)
          					 | Addc | Add ->
                        perform_op oper dset sset is_cf is_zf is_sf is_of
										 | Subb | Sub ->
											  perform_op oper dset sset is_cf is_zf is_sf is_of_sub
										| CmpOp -> failwith "valAD: CmpOp should not be handeled by function arith")
                 in store_vals env dstvar resmap srcvar srcmap
             | (_, _) ->
                 (* We convert sets into intervals in order to perform the operations;
   * interval_arith may return either FSet or Interval *)
                 interval_arith env aop oper dstvar dst_vals src_vals)
      
    (* Implements the effects of 8-bit arithmetic operations *)
    let arith_int8 env flgs_init dstvar dmask dst_vals srcvar smask src_vals
                   aop =
      match aop with
      | Xor ->
          let oper x y = arithop_to_int64op aop x y
          in
            (match (dst_vals, src_vals) with
             | (FSet dset, FSet sset) ->
                 (*perform operation on values from masked registers*)
                 let (_, srcmap, resmap) =
                   perform_op_int8 oper dset dmask sset smask
                     is_cf_logic is_zf_logic_8 is_sf_logic_8 is_of_logic
                 in store_vals env dstvar resmap srcvar srcmap
             | (_, _) ->
                 (*Return top for all flag combinations that can be caused by Xor. To make this more precise, a solution*)
                 (* is needed for combining the 8-bit result with the remaining bits of the source register/memory location*)
                 let top_env = VarMap.add dstvar top env in
                 let fm =
                   FlagMap.singleton
                     { cf = false; zf = true; sf = false; o_f = false; }
                     top_env in
                 let fm =
                   FlagMap.add
                     { cf = false; zf = false; sf = false; o_f = false; }
                     top_env fm
                 in
                   FlagMap.add
                     { cf = false; zf = false; sf = true; o_f = false; }
                     top_env fm)
      | Inc | Dec ->
          (* This is a very coarse grained over approximation: we say
             everything is possible, even changes to values outside of the
             affected 8 bit result, i.e. the unaffected parts of the 32
             bit internal result.
           *)
          let top_env = VarMap.add dstvar top env in
          (* SF and ZF can never be both true at once. *)
          let fm = FlagMap.singleton { cf = flgs_init.cf; zf = false; sf = false; o_f = false; } top_env in
          let fm = FlagMap.add       { cf = flgs_init.cf; zf = false; sf = false; o_f = true;  } top_env fm in
          let fm = FlagMap.add       { cf = flgs_init.cf; zf = false; sf = true;  o_f = false; } top_env fm in
          let fm = FlagMap.add       { cf = flgs_init.cf; zf = false; sf = true;  o_f = true;  } top_env fm in
          let fm = FlagMap.add       { cf = flgs_init.cf; zf = true;  sf = false; o_f = false; } top_env fm in
          let fm = FlagMap.add       { cf = flgs_init.cf; zf = true;  sf = false; o_f = true;  } top_env fm in
          fm
      | And | Or | Addc | Add | Subb | Sub ->
          (* This is a very coarse grained over approximation: we say
             everything is possible, even changes to values outside of the
             affected 8 bit result, i.e. the unaffected parts of the 32
             bit internal result.
           *)
          let top_env = VarMap.add dstvar top env in
          (* SF and ZF can never be both true at once. *)
          let fm = FlagMap.singleton { cf = false; zf = false; sf = false; o_f = false; } top_env in
          let fm = FlagMap.add       { cf = false; zf = false; sf = false; o_f = true;  } top_env fm in
          let fm = FlagMap.add       { cf = false; zf = false; sf = true;  o_f = false; } top_env fm in
          let fm = FlagMap.add       { cf = false; zf = false; sf = true;  o_f = true;  } top_env fm in
          let fm = FlagMap.add       { cf = false; zf = true;  sf = false; o_f = false; } top_env fm in
          let fm = FlagMap.add       { cf = false; zf = true;  sf = false; o_f = true;  } top_env fm in
          let fm = FlagMap.add       { cf = true;  zf = false; sf = false; o_f = false; } top_env fm in
          let fm = FlagMap.add       { cf = true;  zf = false; sf = false; o_f = true;  } top_env fm in
          let fm = FlagMap.add       { cf = true;  zf = false; sf = true;  o_f = false; } top_env fm in
          let fm = FlagMap.add       { cf = true;  zf = false; sf = true;  o_f = true;  } top_env fm in
          let fm = FlagMap.add       { cf = true;  zf = true;  sf = false; o_f = false; } top_env fm in
          let fm = FlagMap.add       { cf = true;  zf = true;  sf = false; o_f = true;  } top_env fm in
          fm
      | _ -> failwith ("valAD: 8-bit arithmetic not implemented for " ^ (X86Util.arith_op_to_string aop))
      
    let imul env flgs_init dstvar dst_vals srcvar src_vals aop arg3 =
      match (dst_vals, src_vals) with
      | (FSet dset, FSet sset) -> 
				  (* sign flag is undefined *)
          let test_sf _ _ _ = None in 
          let test_zf _ = false in
          (* carry flag is set when result has to be truncated *)
          let test_cf _ _ res =
            (res < (Int64.of_int32 Int32.min_int)) ||
              (res > (Int64.of_int32 Int32.max_int)) in						
          let test_of _ _ res =
            let sign_lower = 
							((Int64.shift_right_logical (Int64.logand res 0xFFFFFFFFL) 31) <> 0L) in
						let res_upper = 
							(Int64.logand (Int64.shift_right_logical res 32) 0xFFFFFFFFL) in
						if sign_lower then Some (res_upper <> 0xFFFFFFFFL)
						else Some (res_upper <> 0L) in
          (* for 32 bits operations *)
          let (_, srcmap, resmap) =
            (match arg3 with
             | None -> (* 2 operands: do dst = dst * src *)
                 perform_op Int64.mul dset sset test_cf test_zf test_sf
                   test_of
             | Some imm -> (* 3 operands: do dst = src * imm*)
                 let immset = NumSet.singleton imm
                 in
                   perform_op Int64.mul sset immset test_cf test_zf test_sf
                     test_of)
          in store_vals env dstvar resmap srcvar srcmap
      | (_, _) -> (* For the time being we return top, *)
          (* until a more precise solution is implemented*)
          let top_env = VarMap.add dstvar top env in
          (*in multiplication, the setting behavior of carry flag is as same as that of overflow flag*)
          let retmap =
            FlagMap.singleton
              { cf = false; zf = false; sf = false; o_f = false; } top_env
          in
					let retmap = 
						FlagMap.add { cf = false; zf = false; sf = true; o_f = false; } top_env retmap in 
		  		let retmap = 
						FlagMap.add { cf = true; zf = false; sf = true; o_f = true; } top_env retmap in 
          FlagMap.add { cf = true; zf = false; sf = false; o_f = true; }
              top_env retmap
							
      
    let div env flgs_init dst1var dst1vals dst1mask dst2var dst2vals dst2mask
            svar svals smask =
			if (smask <> NoMask || dst1mask <> NoMask || dst2mask <> NoMask)
		  then failwith "Division is only supported for 32b."
			else
      match (dst1vals, dst2vals, svals) with
      | (FSet d1set, FSet d2set, FSet sset) ->
				   (*combine the results for each value of s*)
            let compute_op_s d1val d2val sset =
              NumSet.fold
                (fun sval (d1map, d2map, smap) ->
								if (d1val < 0L || d2val < 0L || sval < 0L) then failwith "Only unsigned division is supported." else
									(*If one would like to add support for 8-bit division, it could make sense to move the combination of the parts of the divident out of compute_op_s and*)
									(* perform it on the set of possible values to obtain a set of possible combinations*)
								let dividend = Int64.logor (Int64.shift_left (Int64.logand d1val 0xFFFFFFFFL) 32) (Int64.logand d2val 0xFFFFFFFFL) in
								let divisor = if (Int64.logand sval 0xFFFFFFFFL) <> 0L then (Int64.logand sval 0xFFFFFFFFL) else failwith "valAD: Division by 0."	in
								(*The handling of division by 0 could be unnecessarily restrictive if 0 is only among the possible values due to overapproximantion.*)	
								let quotient = Int64.div dividend divisor in								
								let remainder = Int64.rem dividend divisor in	
								if Int64.logand 0xFFFFFFFF00000000L quotient <> 0L then failwith "valAD: Quotient of division too large." else
  								 (*the flags are not affected by div*) 
								   (*the remainder is written to the first destination variable*)
                   let d1vals = fmap_find_with_defval flgs_init NumSet.empty d1map in
 							     let dest1map = 
											if (remainder < 0L) then
											(*if the remainder is negative, we consider the negative remainder and also the corresponding positive remainder possible*)
											(* to ensure that we safely overapproximate the actual implementation of the remainder computation*)
											FlagMap.add flgs_init (NumSet.add (Int64.add remainder divisor) (NumSet.add remainder d1vals)) smap
											else FlagMap.add flgs_init (NumSet.add remainder d1vals) smap in
									 (*the quotient is written to the second destination variable*)									
    							 let d2vals = fmap_find_with_defval flgs_init NumSet.empty d2map in
     							 let dest2map = FlagMap.add flgs_init (NumSet.add quotient d2vals) d2map in
   								 let svals = fmap_find_with_defval flgs_init NumSet.empty smap in
   								 let sourcemap = FlagMap.add flgs_init (NumSet.add sval svals) smap
     							 in (dest1map, dest2map, sourcemap)	
								)
                sset (FlagMap.empty, FlagMap.empty, FlagMap.empty) in								
            (*combine the results for each value of the d2*)
            let compute_op_d2 d1val d2set sset =
              NumSet.fold
                (fun d2val (new_d1, new_d2, new_s) ->
                   let (d1vals, d2vals, svals) = compute_op_s d1val d2val sset
                   in
                     ((fmap_combine d1vals new_d1 NumSet.union),
                      (fmap_combine d2vals new_d2 NumSet.union),
                      (fmap_combine svals new_s NumSet.union)))
                d2set (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
					  (*combine the results for each value of d1*)
            let (d1map, d2map, smap) =
              NumSet.fold
                (fun d1val (new_d1, new_d2, new_s) ->
                   let (d1vals, d2vals, svals) = compute_op_d2 d1val d2set sset
                   in
                     ((fmap_combine d1vals new_d1 NumSet.union),
                      (fmap_combine d2vals new_d2 NumSet.union),
                      (fmap_combine svals new_s NumSet.union)))
                d1set (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
            (*maps from flag combinations to possible values*)
            (*Convert sets to intervals if they are too large*)
            let d1map =
              FlagMap.map (fun nums -> lift_to_interval nums) d1map in
            let d2map =
              FlagMap.map (fun nums -> lift_to_interval nums) d2map in
            let smap =
              FlagMap.map (fun nums -> lift_to_interval nums) smap in
							
            (*return the flag map which maps the flag combinations to the valueADs with the values of d1, d2 and*)
            (* s from which the flag combination can result. If the s was an immediate, it is discarded.*)
            let new_flag_env =
              FlagMap.mapi
                (fun flgs d1vals ->
                   let env =
										(match svar with
            				 | VarOp var -> VarMap.add var (FlagMap.find flgs smap) env
            				 | Cons _ -> env) in
                   let env =
                     VarMap.add dst2var (FlagMap.find flgs d2map) env                   
                   in VarMap.add dst1var d1vals env)
                d1map
            in
              new_flag_env				
				
      | (_, _, _) -> (* For the time being we return top, *)
          (* until a more precise solution is implemented*)
          let top_env = VarMap.add dst2var top (VarMap.add dst1var top env)
          in FlagMap.singleton flgs_init top_env
	
		let signextend_32_to_64 val32 = if Int64.logand (Int64.shift_right_logical val32 31) 0x1L <> 0L then (Int64.logor 0XFFFFFFFF00000000L val32) else val32					
    let zeroextend_32_to_64 val32 = Int64.logand val32 0xFFFFFFFFL
										
    let mulimullong env flgs_init dst1var dst1vals dst1mask dst2var dst2vals dst2mask
            svar svals smask signed =
			if (smask <> NoMask || dst1mask <> NoMask || dst2mask <> NoMask)
		  then failwith "Imul to two destinations is only supported for 32b."
			else
      match (dst1vals, dst2vals, svals) with
      | (FSet d1set, FSet d2set, FSet sset) ->
				   (*combine the results for each value of s*)
            let compute_op_s d1val d2val sset =
              NumSet.fold
                (fun sval (d1map, d2map, smap) ->		
									let op1 = if signed then signextend_32_to_64 sval else zeroextend_32_to_64 sval in
									let op2 = if signed then signextend_32_to_64 d2val else zeroextend_32_to_64 d2val in									
									let result = Int64.mul op1 op2 in
									let lower = Int64.logand result 0xFFFFFFFFL in
									let upper = Int64.shift_right_logical (Int64.logand result 0xFFFFFFFF00000000L) 32 in													
                  let new_cfof  =
                    let sign_lower = ((Int64.shift_right_logical (Int64.logand result 0xFFFFFFFFL) 31) <> 0L) in
						        let res_upper = (Int64.logand (Int64.shift_right_logical result 32) 0xFFFFFFFFL) in
					        	if signed && sign_lower then (res_upper <> 0xFFFFFFFFL)
				         		else (res_upper <> 0L) 
										in

									(*SF and ZF are undefined*)
									let flags1 = {cf = new_cfof; o_f = new_cfof; sf = true; zf = true} in
									let flags2 = {cf = new_cfof; o_f = new_cfof; sf = true; zf = false} in
									let flags3 = {cf = new_cfof; o_f = new_cfof; sf = false; zf = true} in
									let flags4 = {cf = new_cfof; o_f = new_cfof; sf = false; zf = false} in

								   (*the upper part of the result is written to the first destination variable*)
                   let d1vals = fmap_find_with_defval flgs_init NumSet.empty d1map in
 							     let dest1map =
											 FlagMap.add flags4 (NumSet.add upper d1vals) 
											 (FlagMap.add flags3 (NumSet.add upper d1vals) 											
											 (FlagMap.add flags2 (NumSet.add upper d1vals) 											
											 (FlagMap.add flags1 (NumSet.add upper d1vals) smap))) in
									 (*the lower part of the result is written to the second destination variable*)									
    							 let d2vals = fmap_find_with_defval flgs_init NumSet.empty d2map in
     							 let dest2map = 
											 FlagMap.add flags4 (NumSet.add lower d2vals)
											 (FlagMap.add flags3 (NumSet.add lower d2vals)											
											 (FlagMap.add flags2 (NumSet.add lower d2vals) 	
											 (FlagMap.add flags1 (NumSet.add lower d2vals) d2map))) in
   								 let svals = fmap_find_with_defval flgs_init NumSet.empty smap in
   								 let sourcemap = 
											 FlagMap.add flags4 (NumSet.add sval svals) 
											 (FlagMap.add flags3 (NumSet.add sval svals) 									
											 (FlagMap.add flags2 (NumSet.add sval svals) 	
											 (FlagMap.add flags1 (NumSet.add sval svals) smap)))
     							 in (dest1map, dest2map, sourcemap)	
								)
                sset (FlagMap.empty, FlagMap.empty, FlagMap.empty) in								
            (*combine the results for each value of the d2*)
            let compute_op_d2 d1val d2set sset =
              NumSet.fold
                (fun d2val (new_d1, new_d2, new_s) ->
                   let (d1vals, d2vals, svals) = compute_op_s d1val d2val sset
                   in
                     ((fmap_combine d1vals new_d1 NumSet.union),
                      (fmap_combine d2vals new_d2 NumSet.union),
                      (fmap_combine svals new_s NumSet.union)))
                d2set (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
					  (*combine the results for each value of d1*)
            let (d1map, d2map, smap) =
              NumSet.fold
                (fun d1val (new_d1, new_d2, new_s) ->
                   let (d1vals, d2vals, svals) = compute_op_d2 d1val d2set sset
                   in
                     ((fmap_combine d1vals new_d1 NumSet.union),
                      (fmap_combine d2vals new_d2 NumSet.union),
                      (fmap_combine svals new_s NumSet.union)))
                d1set (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
            (*maps from flag combinations to possible values*)
            (*Convert sets to intervals if they are too large*)
            let d1map =
              FlagMap.map (fun nums -> lift_to_interval nums) d1map in
            let d2map =
              FlagMap.map (fun nums -> lift_to_interval nums) d2map in
            let smap =
              FlagMap.map (fun nums -> lift_to_interval nums) smap in
							
            (*return the flag map which maps the flag combinations to the valueADs with the values of d1, d2 and*)
            (* s from which the flag combination can result. If the s was an immediate, it is discarded.*)
            let new_flag_env =
              FlagMap.mapi
                (fun flgs d1vals ->
                   let env =
										(match svar with
            				 | VarOp var -> VarMap.add var (FlagMap.find flgs smap) env
            				 | Cons _ -> env) in
                   let env =
                     VarMap.add dst2var (FlagMap.find flgs d2map) env                   
                   in VarMap.add dst1var d1vals env)
                d1map
            in
              new_flag_env				
				
     
      | (_, _, _) -> 
          let top_env = VarMap.add dst2var top (VarMap.add dst1var top env)
          in (*CF and OF are set to the same value*)
					let fm = FlagMap.singleton {cf = true; o_f = true; sf = true; zf = true} top_env in
					let fm = FlagMap.add {cf = true; o_f = true; sf = true; zf = false} top_env fm in
				  let fm = FlagMap.add {cf = true; o_f = true; sf = false; zf = true} top_env fm in
					let fm = FlagMap.add {cf = true; o_f = true; sf = false; zf = false} top_env fm in
					let fm = FlagMap.add {cf = false; o_f = false; sf = true; zf = true} top_env fm in
					let fm = FlagMap.add {cf = false; o_f = false; sf = true; zf = false} top_env fm in
					let fm = FlagMap.add {cf = false; o_f = false; sf = false; zf = true} top_env fm in
					FlagMap.add {cf = false; o_f = false; sf = false; zf = false} top_env fm	
				
					

    let cdq env flags dstvar dvals srcvar svals =
      let env_clear = FlagMap.singleton flags (VarMap.add dstvar (FSet (NumSet.singleton 0x00000000L)) env) in
      let env_set   = FlagMap.singleton flags (VarMap.add dstvar (FSet (NumSet.singleton 0xFFFFFFFFL)) env) in
      let env_both  = fmap_combine env_clear env_set join in
      match (dvals, svals) with
      | (_, FSet sset) ->
          let exists_pos, exists_neg =
            NumSet.fold (fun value (exists_pos, exists_neg) ->
                if (Int64.logand value 0x80000000L <> 0L)
                then (exists_pos, true)
                else (true, exists_neg)
              ) sset (false, false) in
          (* For the time being we simply return either all bits set or all cleared. *)
          (match (exists_pos, exists_neg) with
           | (true,  true)  -> env_both
           | (true,  false) -> env_clear
           | (false, true)  -> env_set
           | (false, false) -> failwith "valAD: cdq: neither positive nor negative in set case")
      | (_, _) ->
          (* For the time being we simply return either all bits set or all cleared. *)
          env_both
    (* interval_flag_test takes two intervals and a flag combination and returns
     * the corresponding intervals *)
    let interval_flag_test env arith_op dstvar dvals srcvar svals =
      match arith_op with
      | And ->
          (* TODO: There is room for precision improvements here. For example,
                   when the sign is not set for both dvals and svals, there is
                   no possibility of sign flag being set. *)
          let flgs1 = { cf = false; zf = false; sf = false; o_f = false; } in
          let flgs2 = { cf = false; zf = true;  sf = false; o_f = false; } in
          let flgs3 = { cf = false; zf = false; sf = true;  o_f = false; } in
          ((FlagMap.add flgs3 dvals (FlagMap.add flgs2 dvals (FlagMap.add flgs1 dvals FlagMap.empty))),
           (FlagMap.add flgs3 svals (FlagMap.add flgs2 svals (FlagMap.add flgs1 svals FlagMap.empty))))
      | Sub ->
      let (dvals, svals) = ((to_interval dvals), (to_interval svals)) in
      let (dl, dh) = get_bounds dvals in
      let (sl, sh) = get_bounds svals in
      (* Intersection between the two intervals *)
      let meetZF = var_meet_ab dvals svals in
      let ndh = min dh (Int64.pred sh) in
      let nsl = max (Int64.succ dl) sl in
      let nsh = min (Int64.pred dh) sh in
      let ndl = max dl (Int64.succ sl) in
      let (dstmap, srcmap) = (FlagMap.empty, FlagMap.empty) in
      let (dstmap, srcmap) =
        if (ndh < dl) || (nsl > sh)
        then (dstmap, srcmap)
        else
              (* We should have [dl, min(dh,sh-1)] and [max(dl+1,sl), sh] *)
              (let flgs1 = { cf = true; zf = false; sf = false; o_f = false; } in
							 let flgs2 = { cf = true; zf = false; sf = true; o_f = false; } in
							 let flgs3 = { cf = true; zf = false; sf = false; o_f = true; } in
							 let flgs4 = { cf = true; zf = false; sf = true; o_f = true; } in
							 let dst_si = (set_or_interval dl ndh) in
							 let src_si = (set_or_interval nsl sh) in
                 (FlagMap.add flgs4 dst_si(FlagMap.add flgs3 dst_si 
										(FlagMap.add flgs2 dst_si (FlagMap.add flgs1 dst_si dstmap))),
                  FlagMap.add flgs4 src_si (FlagMap.add flgs3 src_si 
										(FlagMap.add flgs2 src_si (FlagMap.add flgs1 src_si srcmap)))
									)) in
          let (dstmap, srcmap) =
            if (ndl > dh) || (nsh < sl)
            then (dstmap, srcmap)
            else
              (let flgs1 = { cf = false; zf = false; sf = false; o_f = false; } in
							 let flgs2 = { cf = false; zf = false; sf = true; o_f = false; } in
							 let flgs3 = { cf = false; zf = false; sf = false; o_f = true; } in
							 let flgs4 = { cf = false; zf = false; sf = true; o_f = true; } in
							 let dst_si = (set_or_interval ndl dh) in
							 let src_si = (set_or_interval sl nsh) in
                 (FlagMap.add flgs4 dst_si(FlagMap.add flgs3 dst_si 
										(FlagMap.add flgs2 dst_si (FlagMap.add flgs1 dst_si dstmap))),
                  FlagMap.add flgs4 src_si (FlagMap.add flgs3 src_si 
										(FlagMap.add flgs2 src_si (FlagMap.add flgs1 src_si srcmap)))))							
          in
            (* meet <> empty then ZF can be set *)
            (match meetZF with
            | Bot -> (dstmap, srcmap)
            | Nb z ->
                let flgs1 = { cf = false; zf = true; sf = false; o_f = false; } in
								let flgs2 = { cf = false; zf = true; sf = true; o_f = false; } in
								let flgs3 = { cf = false; zf = true; sf = false; o_f = true; } in
								let flgs4 = { cf = false; zf = true; sf = true; o_f = true; } in
                (FlagMap.add flgs4 z (FlagMap.add flgs3 z (FlagMap.add flgs2 z
									(FlagMap.add flgs1 z dstmap))),							
								 FlagMap.add flgs4 z (FlagMap.add flgs3 z (FlagMap.add flgs2 z
									(FlagMap.add flgs1 z dstmap)))))
      | _ ->
          failwith "valAD: TEST/CMP with unexpected arithmetic operation in interval case."
       
    (* perform TEST or CMP *)
    let test_cmp env flags fop dstvar dvals dmask srcvar svals smask =
			match (dmask,smask) with
			| (NoMask, NoMask) ->
        (let arith_op = match fop with | Atest -> And | Acmp -> Sub in
        let (dstmap, srcmap) =
          match (dvals, svals) with
          | (FSet dset, FSet sset) ->
              let oper = arithop_to_int64op arith_op in
              let (dstmap, srcmap, _) =
                (match arith_op with
                 | And ->
                     perform_op oper dset sset is_cf_logic is_zf_logic_32 is_sf_logic_32 is_of_logic
                 | Sub -> perform_op oper dset sset is_cf is_zf is_sf is_of_sub
                 | _ ->
                     failwith
                       "valAD: TEST/CMP with unexpected arithmetic operation.")
              in (dstmap, srcmap)
          | (_, _) -> interval_flag_test env arith_op dstvar dvals srcvar svals
        in store_vals env dstvar dstmap srcvar srcmap)
			 | (_,_) -> 
					match fop with 
					| Atest -> (*SF and ZF cannot be true at the same time, CF and OF are always false*)
						FlagMap.add {cf = false; zf = true; sf = false; o_f = false} env
						(FlagMap.add {cf = false; zf = false; sf = true; o_f = false} env
						(FlagMap.singleton {cf = false; zf = false; sf = false; o_f = false} env))						
					|	Acmp -> (*SF and ZF cannot be true at the same time*)
			     	FlagMap.add {cf = false; zf = false; sf = false; o_f = false} env
			      (FlagMap.add {cf = false; zf = false; sf = false; o_f = true} env				
				    (FlagMap.add {cf = false; zf = false; sf = true; o_f = false} env
				    (FlagMap.add {cf = false; zf = false; sf = true; o_f = true} env
				    (FlagMap.add {cf = false; zf = true; sf = false; o_f = false} env
				    (FlagMap.add {cf = false; zf = true; sf = false; o_f = true} env
				    (FlagMap.add {cf = true; zf = false; sf = false; o_f = false} env
				    (FlagMap.add {cf = true; zf = false; sf = false; o_f = true} env					 
				    (FlagMap.add {cf = true; zf = false; sf = true; o_f = false} env
			      (FlagMap.add {cf = true; zf = false; sf = true; o_f = true} env
			    	(FlagMap.add {cf = true; zf = true; sf = false; o_f = false} env
				    (FlagMap.singleton {cf = true; zf = true; sf = false; o_f = true} env)))))))))))
      
    let rotate_left value offset =
      let bin = Int64.shift_left value offset in
      let bout = Int64.shift_right_logical value (32 - offset)
      in Int64.logor (truncate 32 bin) (truncate 32 bout)
      
    let rotate_right value offset =
      let bin = Int64.shift_right_logical value offset in
      let bout = Int64.shift_left value (32 - offset)
      in Int64.logor (truncate 32 bin) (truncate 32 bout)
      
    let shift_operator =
      function
      | Shl -> (fun x o -> Int64.shift_left x (Int64.to_int o))
      | Shr -> (fun x o -> Int64.shift_right_logical x (Int64.to_int o))
      | (* In order to preserve the sign, we need to convert to int32 *) Sar
          ->
          (fun value off ->
             Int64.of_int32
               (Int32.shift_right (Int64.to_int32 value) (Int64.to_int off)))
      | Ror -> (fun x o -> rotate_right x (Int64.to_int o))
      | Rol -> (fun x o -> rotate_left x (Int64.to_int o))
      
    (* Shift the values of the variable dst using the offsets given by soff *)
    let shift env flags sop dstvar vals offs_var off_vals mk =
      let offsets = mask_vals mk off_vals in
      let oper3 = shift_operator sop in
      let oper = oper3 in
      let top_env = VarMap.add dstvar top env
      in
        match (vals, offsets) with
        | (FSet dset, FSet offs_set) ->
            let cf_test = is_cf_shift sop in
            let (_, srcmap, resmap) =
              (match sop with
               | Shl | Rol | Ror ->
                   perform_op oper dset offs_set cf_test is_zf (is_sf_shift sop flags.sf) (is_of_shift sop flags.o_f)				 
               | Sar | Shr ->
                   perform_op oper dset offs_set cf_test is_zf (is_sf_shift sop flags.sf) (is_of_shift sop flags.o_f))
            in store_vals env dstvar resmap offs_var srcmap
        | (Interval (l, h), FSet offs_set) ->
            (* This doesn't work with rotate; return Top if rotate *)
            let newenv =
              let bound f b sup =
                NumSet.fold (fun offs r -> f (oper b offs) r) offs_set sup in
              let (lb, ub) = ((bound min l max_elt), (bound max h min_elt))
              in
                (match sop with
                 | Ror | Rol -> top_env
                 | _ ->
                     if ub < lb
                     then env
                     else VarMap.add dstvar (Interval (lb, ub)) env) in
            (*SHL, SAR, SHR*)
            (*can potentially be made more precise by considering special cases depending of possible offsets*)
            let fm =
              FlagMap.singleton
                { cf = true; zf = true; sf = false; o_f = false; } newenv in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = false; o_f = false; }
                newenv fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = false; o_f = false; }
                newenv fm in
            let fm =
              FlagMap.add
                { cf = false; zf = false; sf = false; o_f = false; } newenv
                fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = true; o_f = false; }
                newenv fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = true; o_f = false; }
                newenv fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = true; o_f = false; }
                newenv fm in
            let fm =
              FlagMap.add { cf = false; zf = false; sf = true; o_f = false; }
                newenv fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = true; o_f = true; }
                newenv fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = true; o_f = true; }
                newenv fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = true; o_f = true; }
                newenv fm in
            let fm =
              FlagMap.add { cf = false; zf = false; sf = true; o_f = true; }
                newenv fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = false; o_f = true; }
                newenv fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = false; o_f = true; }
                newenv fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = false; o_f = true; }
                newenv fm
            in
              FlagMap.add { cf = false; zf = false; sf = false; o_f = true; }
                newenv fm
        | (_, _) ->
            let fm =
              FlagMap.singleton
                { cf = true; zf = true; sf = false; o_f = false; } top_env in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = false; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = false; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add
                { cf = false; zf = false; sf = false; o_f = false; } top_env
                fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = false; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = true; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = true; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = true; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = false; sf = true; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = false; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = false; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = false; o_f = true; }
                top_env fm
            in
              FlagMap.add { cf = false; zf = false; sf = false; o_f = true; }
                top_env fm
      
    (* Implements the effects of MOV *)
    let mov env flags dstvar mkvar dst_vals srcvar mkcvar src_vals =
      let new_env =
        match (mkvar, mkcvar) with
        | (* 32 bits -> 32 bits MOV and 8 -> 32 : MOVZX *) (NoMask, msk) ->
            let src_vals = mask_vals msk src_vals
            in VarMap.add dstvar src_vals env
        | (* 8 -> 8 : MOVB *) (Mask mkv, Mask mkc) ->
            (match (dst_vals, src_vals) with
             | (FSet ds, FSet ss_unmasked) ->
                 let (c_mask, c_shift) = mask_to_intoff mkc in
                 (* Nullify everything but the 8 bits corresponding to the mask *)
                 let ss_shifted =
                   set_map (fun x -> Int64.logand x c_mask) ss_unmasked in
                 (* Then shift it to the first 8 bits *)
                 let ss =
                   set_map (fun x -> Int64.shift_right x c_shift) ss_shifted in
                 let (v_mask, v_shift) = mask_to_intoff mkv in
                 (* Align cv values in order to write them into v *)
                 let cvSet =
                   set_map (fun x -> Int64.shift_left x v_shift) ss in
                 (* Nullify the 8 bits corresponding to the mask *)
                 let varSet =
                   set_map (fun x -> Int64.logand (Int64.lognot v_mask) x) ds in
                 (* Create a list of set combining all the posible values with the mask in place *)
                 let doOp x = set_map (fun y -> Int64.logor x y) varSet in
                 let setList =
                   NumSet.fold (fun x r -> (doOp x) :: r) cvSet [] in
                 (* Unite all the sets *)
                 let finalSet =
                   List.fold_left NumSet.union NumSet.empty setList
                 in VarMap.add dstvar (lift_to_interval finalSet) env
             | (_, _) -> VarMap.add dstvar top env)
        | (_, _) -> failwith "ValAD.move: operation from 32 bits to 8 bits"
      in FlagMap.singleton flags new_env
      
    (* Implements the effects of CMOV, which depends on the status of sf flag *)
    let cmov cc env flags dstvar mkvar dst_vals srcvar mkcvar src_vals =
			if cc <> (true, S) then failwith "valAD: Cmov only implemented for condition S." else
			match flags.sf with
      | true ->
          let new_env =
            (match (mkvar, mkcvar) with
             | (* 32 bits -> 32 bits MOV and 8 -> 32 : MOVZX *) (NoMask, msk)
                 ->
                 let src_vals = mask_vals msk src_vals
                 in VarMap.add dstvar src_vals env
             | (* 8 -> 8 : MOVB *) (Mask mkv, Mask mkc) ->
                 (match (dst_vals, src_vals) with
                  | (FSet ds, FSet ss_unmasked) ->
                      let (c_mask, c_shift) = mask_to_intoff mkc in
                      (* Nullify everything but the 8 bits corresponding to the mask *)
                      let ss_shifted =
                        set_map (fun x -> Int64.logand x c_mask) ss_unmasked in
                      (* Then shift it to the first 8 bits *)
                      let ss =
                        set_map (fun x -> Int64.shift_right x c_shift)
                          ss_shifted in
                      let (v_mask, v_shift) = mask_to_intoff mkv in
                      (* Align cv values in order to write them into v *)
                      let cvSet =
                        set_map (fun x -> Int64.shift_left x v_shift) ss in
                      (* Nullify the 8 bits corresponding to the mask *)
                      let varSet =
                        set_map
                          (fun x -> Int64.logand (Int64.lognot v_mask) x) ds in
                      (* Create a list of set combining all the posible values with the mask in place *)
                      let doOp x =
                        set_map (fun y -> Int64.logor x y) varSet in
                      let setList =
                        NumSet.fold (fun x r -> (doOp x) :: r) cvSet [] in
                      (* Unite all the sets *)
                      let finalSet =
                        List.fold_left NumSet.union NumSet.empty setList
                      in VarMap.add dstvar (lift_to_interval finalSet) env
                  | (_, _) -> VarMap.add dstvar top env)
             | (_, _) ->
                 failwith "ValAD.move: operation from 32 bits to 8 bits")
          in  FlagMap.singleton flags new_env
      | false -> let new_env = env in FlagMap.singleton flags new_env
      
    let store_shld_shrd sval smap pval pmap oval omap flags' result =
      let svals = fmap_find_with_defval flags' NumSet.empty smap in
      let shiftmap =
        FlagMap.add flags'
          (match result with
           | Some res -> NumSet.add (truncate 32 res) svals
           | None -> interval_to_set min_elt max_elt)
          (*This could slow down the analysis. Potential solution:*)
          (* Make shiftmap etc. maps to sets or intervals (type var_t)*)
          (*  to avoid slowdown by converting top set to interval*) smap in
      let ovals = fmap_find_with_defval flags' NumSet.empty omap in
      let offsetmap = FlagMap.add flags' (NumSet.add oval ovals) omap in
      let pvals = fmap_find_with_defval flags' NumSet.empty pmap in
      let patternmap = FlagMap.add flags' (NumSet.add pval pvals) pmap
      in (shiftmap, patternmap, offsetmap)
      

	let bsr env flags dstvar dvals mkvar srcvar svals mkcvar =
		match (mkvar, mkcvar) with
		| NoMask, NoMask ->
				(match (dvals, svals) with
					| FSet dvalset, FSet svalset ->
							let compute_op dst =
								NumSet.fold
									(fun src (smap, rmap) ->
										(*Implementation based on "Formal Specification of the x86
											Instruction Set Architecture" by Ulan Degenbaev*)
												let num_leading_zeroes =
													if (Int64.logand src 0xFFFF0000L) <> 0L
													then (*first 0 in first half of bitstring*)
														(if (Int64.logand src 0xFF000000L) <> 0L
															then 	(*first 0 in first byte*)
															(if (Int64.logand src 0xF0000000L) <> 0L
																then (*first 0 in 1st half of first byte*)
																(if (Int64.logand src 0x80000000L) <> 0L then 0
																	else (if (Int64.logand src 0x40000000L) <> 0L then 1
																		else (if (Int64.logand src 0x20000000L) <> 0L then 2
																			else (if (Int64.logand src 0x10000000L) <> 0L then 3 else 4)
																		)))
																else (*first 0 in 2nd half of first byte*) 4 +
																(if (Int64.logand src 0x8000000L) <> 0L then 0
																	else (if (Int64.logand src 0x4000000L) <> 0L then 1
																		else (if (Int64.logand src 0x2000000L) <> 0L then 2
																			else (if (Int64.logand src 0x1000000L) <> 0L then 3 else 4)
																		))))
															else (*first 0 in second byte*) 8 +
															(if (Int64.logand src 0x00F00000L) <> 0L
																then (*first 0 in 1st half of second byte*)
																(if (Int64.logand src 0x800000L) <> 0L then 0
																	else (if (Int64.logand src 0x400000L) <> 0L then 1
																		else (if (Int64.logand src 0x200000L) <> 0L then 2
																			else (if (Int64.logand src 0x100000L) <> 0L then 3 else 4)
																		)))
																else (*first 0 in 2nd half of second byte*) 4 +
																(if (Int64.logand src 0x80000L) <> 0L then 0
																	else (if (Int64.logand src 0x40000L) <> 0L then 1
																		else (if (Int64.logand src 0x20000L) <> 0L then 2
																			else (if (Int64.logand src 0x10000L) <> 0L then 3 else 4)
																		)))))
													else (*first 0 in second half of bitstring*) 16 +
													(if (Int64.logand src 0x0000FF00L) <> 0L
														then 	(*first 0 in third byte*)
														(if (Int64.logand src 0x0000F000L) <> 0L
															then (*first 0 in 1st half of third byte*)
															(if (Int64.logand src 0x8000L) <> 0L then 0
																else (if (Int64.logand src 0x4000L) <> 0L then 1
																	else (if (Int64.logand src 0x2000L) <> 0L then 2
																		else (if (Int64.logand src 0x1000L) <> 0L then 3 else 4)
																	)))
															else (*first 0 in 2nd half of third byte*) 4 +
															(if (Int64.logand src 0x800L) <> 0L then 0
																else (if (Int64.logand src 0x400L) <> 0L then 1
																	else (if (Int64.logand src 0x200L) <> 0L then 2
																		else (if (Int64.logand src 0x100L) <> 0L then 3 else 4)
																	))))
														else (*first 0 in fourth byte*) 8 +
														(if (Int64.logand src 0x000000F0L) <> 0L
															then (*first 0 in 1st half of fourth byte*)
															(if (Int64.logand src 0x80L) <> 0L then 0
																else (if (Int64.logand src 0x40L) <> 0L then 1
																	else (if (Int64.logand src 0x20L) <> 0L then 2
																		else (if (Int64.logand src 0x10L) <> 0L then 3 else 4)
																	)))
															else (*first 0 in 2nd half of fourth byte*) 4 +
															(if (Int64.logand src 0x8L) <> 0L then 0
																else (if (Int64.logand src 0x4L) <> 0L then 1
																	else (if (Int64.logand src 0x2L) <> 0L then 2
																		else (if (Int64.logand src 0x1L) <> 0L then 3 else 4)
																	))))) in
												let index_first_one = 32 - num_leading_zeroes in
												let result = if (truncate 32 src) <> 0L then (Int64.of_int index_first_one) else dst in
												let flags =
													{
														cf = flags.cf;
														zf = is_zf src;
														sf = flags.sf;
														o_f = flags.o_f;
													} in
												let svals = fmap_find_with_defval flags NumSet.empty smap in
												let srcmap = FlagMap.add flags (NumSet.add src svals) smap in
												let rvals = fmap_find_with_defval flags NumSet.empty rmap in
												let resmap =
													FlagMap.add flags (NumSet.add (truncate 32 result) rvals) rmap
												in (srcmap, resmap)
									)
									svalset (FlagMap.empty, FlagMap.empty) in
							let (srcmap, resmap) =
								NumSet.fold
									(fun dst (new_s, new_r) ->
												let (srcvals, resvals) = compute_op dst
												in
												((fmap_combine srcvals new_s NumSet.union),
													(fmap_combine resvals new_r NumSet.union)))
									dvalset (FlagMap.empty, FlagMap.empty) in
							let srcmap = FlagMap.map (fun nums -> lift_to_interval nums) srcmap in
							let resmap = FlagMap.map (fun nums -> lift_to_interval nums) resmap
							in store_vals env dstvar resmap srcvar srcmap
					
					| (_, _) ->
							let top_env = VarMap.add dstvar top env in
							let fm =
								FlagMap.singleton
									{ cf = flags.cf; zf = true; sf = flags.sf; o_f = flags.o_f; }
									top_env in
							FlagMap.add
								{ cf = flags.cf; zf = false; sf = flags.sf; o_f = flags.o_f; }
								top_env fm)
		| (_, _) -> failwith "valAD: BSR only implemented for 32b."
    (*bolean isimm_option captures whether the integer passed as parameter "offset" is an immediate (true) or the integer encoding of a variable (false)*)
    let shld_shrd op env flags svar svals smask patternvar patternvals
                  patternmask offset 
                  isimm_option =
      let patternvar = consvar_to_var patternvar in
      let isimm =
        match isimm_option with
        | Some b -> b
        | None ->
            failwith
              "valAD: A SHLD/SHRD operation is missing the information about the type of offset." in
      let offsetvals =
        match offset with
        | Some off ->
            if isimm
            then FSet (NumSet.singleton off)
            else VarMap.find off env
        | None ->
            failwith "valAD: SHLD/SHRD operation with no possible offsets."
      in
        match (svals, patternvals, offsetvals) with
        | (FSet sv, (*values of register to be shifted*) FSet pv,
           (*values of pattern to shift in*) FSet ov) ->
            (*values of shift offset*)
            (*compute the result and flags for one specific value to be shifted, pattern and offset,*)
            (* return None for undefined result or flags*)
            let compute_op flags toshift pattern offset =
              (match (smask, patternmask) with
               | (NoMask, NoMask) ->
                   let result =
                     if offset = 0L
                     then Some toshift
                     else
                       if offset = 32L
                       then Some pattern
                       else
                         if offset > 32L
                         then None
                         else
                           (match op with
                            | AShld ->
                                let upper =
                                  Int64.logand
                                    (Int64.shift_left toshift
                                       (Int64.to_int offset))
                                    0xFFFFFFFFL in
                                let lower =
                                  Int64.shift_right_logical
                                    (Int64.shift_left pattern
                                       (Int64.to_int (Int64.sub 64L offset)))
                                    (Int64.to_int (Int64.sub 64L offset))
                                in
                                  Some (Int64.logor upper lower)
                            | AShrd ->
                                let upper =
                                  Int64.logand
                                    (Int64.shift_left pattern
                                       (Int64.to_int (Int64.sub 32L offset)))
                                    0xFFFFFFFFL in
                                let lower =
                                  Int64.shift_right_logical toshift
                                    (Int64.to_int offset)
                                in Some (Int64.logor upper lower)
                            | _ ->
                                failwith
                                  "valAD: SHLD/SHRD instruction with operator other than SHLD/SHRD.") in
                   let flags' =
                     if offset = 0L
                     then
                       ((Some flags.cf), (Some flags.zf), (Some flags.sf),
                        (Some flags.o_f))
                     else
                       if offset > 32L
                       then
                         (let (cf, zf, sf, o_f) = (None, None, None, None)
                          in (cf, zf, sf, o_f))
                       else
                         (let cf =
                            match op with
                            | AShld ->
                                let bitpos = Int64.sub 32L offset in
                                let mask =
                                  Int64.shift_left Int64.one
                                    (Int64.to_int bitpos)
                                in Some ((Int64.logand mask toshift) <> 0L)
                            | AShrd ->
                                let bitpos = Int64.sub offset 1L in
                                let mask =
                                  Int64.shift_left Int64.one
                                    (Int64.to_int bitpos)
                                in Some ((Int64.logand mask toshift) <> 0L)
                            | _ ->
                                failwith
                                  "valAD: SHLD/SHRD instruction with operator other than SHLD/SHRD." in
                          let zf =
                            match result with
                            | None -> None
                            | Some res -> Some (is_zf res) in
                          let sf =
                            match result with
                            | None -> None
                            | Some res -> (is_sf toshift toshift res) in
                          let o_f =
                            if offset = 1L
                            then
                              (match (op, result) with
                               | (AShld, Some res) ->
                                   (is_of toshift toshift res)
                               | (AShrd, Some res) -> (Some false)
                               | (AShld, None) -> None
                               | (AShrd, None) -> None
                               | _ ->
                                   failwith
                                     "valAD: SHLD/SHRD instruction with operator other than SHLD/SHRD.")
                            else None
                          in (cf, zf, sf, o_f))
                   in (result, flags')
               | _ -> failwith "valAD: SHLD/SHRD only implemented for 32bit.") in
            (*combine the results for each value of the offset*)
            let compute_op_off sval pval ov =
              NumSet.fold
                (fun oval (smap, pmap, omap) ->
                   let oval = Int64.logand 0x0000001FL oval in
                   let (result, (cf, zf, sf, o_f)) =
                     compute_op flags sval pval oval
                   in
                     match (cf, zf, sf, o_f) with
                     | (Some cfv, Some zfv, Some sfv, Some ofv) ->
                         let fl =
                           { cf = cfv; zf = zfv; sf = sfv; o_f = ofv; }
                         in
                           store_shld_shrd sval smap pval pmap oval omap fl
                             result
                     | (Some cfv, Some zfv, Some sfv, None) ->
                         let fl1 =
                           { cf = cfv; zf = zfv; sf = sfv; o_f = false; } in
                         let fl2 =
                           { cf = cfv; zf = zfv; sf = sfv; o_f = true; } in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl1
                             result
                         in
                           store_shld_shrd sval smap pval pmap oval omap fl2
                             result
                     | (None, None, None, None) ->
                         let fl1 =
                           { cf = true; sf = true; zf = true; o_f = true; } in
                         let fl2 =
                           { cf = false; sf = true; zf = true; o_f = true; } in
                         let fl3 =
                           { cf = true; sf = false; zf = true; o_f = true; } in
                         let fl4 =
                           { cf = false; sf = false; zf = true; o_f = true; } in
                         let fl5 =
                           { cf = true; sf = true; zf = false; o_f = true; } in
                         let fl6 =
                           { cf = false; sf = true; zf = false; o_f = true; } in
                         let fl7 =
                           { cf = true; sf = false; zf = false; o_f = true; } in
                         let fl8 =
                           { cf = false; sf = false; zf = false; o_f = true;
                           } in
                         let fl9 =
                           { cf = true; sf = true; zf = true; o_f = false; } in
                         let fl10 =
                           { cf = false; sf = true; zf = true; o_f = false; } in
                         let fl11 =
                           { cf = true; sf = false; zf = true; o_f = false; } in
                         let fl12 =
                           { cf = false; sf = false; zf = true; o_f = false;
                           } in
                         let fl13 =
                           { cf = true; sf = true; zf = false; o_f = false; } in
                         let fl14 =
                           { cf = false; sf = true; zf = false; o_f = false;
                           } in
                         let fl15 =
                           { cf = true; sf = false; zf = false; o_f = false;
                           } in
                         let fl16 =
                           { cf = false; sf = false; zf = false; o_f = false;
                           } in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl1
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl2
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl3
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl4
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl5
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl6
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl7
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl8
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl9
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl10
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl11
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl12
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl13
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl14
                             result in
                         let (smap, pmap, omap) =
                           store_shld_shrd sval smap pval pmap oval omap fl15
                             result
                         in
                           store_shld_shrd sval smap pval pmap oval omap fl16
                             result
                     | _ ->
                         failwith
                           "valAD: Unexpected flag combination resulting from SHLD/SHRD.")
                ov (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
            (*combine the results for each value of the pattern to be shifted in*)
            let compute_op_pat sval pv ov =
              NumSet.fold
                (fun pval (new_s, new_p, new_o) ->
                   let (svals, pvals, ovals) = compute_op_off sval pval ov
                   in
                     ((fmap_combine svals new_s NumSet.union),
                      (fmap_combine pvals new_p NumSet.union),
                      (fmap_combine ovals new_o NumSet.union)))
                pv (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
            (*combine the results for each value of the register to be shifted*)
            let (smap, pmap, omap) =
              NumSet.fold
                (fun sval (new_s, new_p, new_o) ->
                   let (svals, pvals, ovals) = compute_op_pat sval pv ov
                   in
                     ((fmap_combine svals new_s NumSet.union),
                      (fmap_combine pvals new_p NumSet.union),
                      (fmap_combine ovals new_o NumSet.union)))
                sv (FlagMap.empty, FlagMap.empty, FlagMap.empty) in
            (*maps from flag combinations to possible values of the register to *)
            (* be shifted / the pattern / the offset*)
            (*Convert sets to intervals if they are too large*)
            let smap =
              FlagMap.map (fun nums -> lift_to_interval nums) smap in
            let pmap =
              FlagMap.map (fun nums -> lift_to_interval nums) pmap in
            let omap =
              FlagMap.map (fun nums -> lift_to_interval nums) omap in
            (*return the flag map which maps the flag combinations to the valueADs with the values of pattern, offset and*)
            (* shifted register from which the flag combination can result. If the offset was an immediate, it is discarded.*)
            (* The shifted register values are written last becasue they overwrite the pattern or offset values*)
            (* if the same register was used for two parameters *)
            let new_flag_env =
              FlagMap.mapi
                (fun flgs svals ->
                   let env =
                     VarMap.add patternvar (FlagMap.find flgs pmap) env in
                   let env =
                     if not isimm
                     then
                       (match offset with
                        | Some off ->
                            VarMap.add off (FlagMap.find flgs omap) env
                        | None ->
                            failwith
                              "valAD: SHLD/SHRD operation with no possible offsets.")
                     else env
                   in VarMap.add svar svals env)
                smap
            in
              new_flag_env
        | (*Set all flag combinations to the top environment until more preise support is needed.*)
            (_, _, _) ->
            let top_env = VarMap.add svar top env in
            let fm =
              FlagMap.singleton
                { cf = true; zf = true; sf = false; o_f = false; } top_env in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = false; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = false; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add
                { cf = false; zf = false; sf = false; o_f = false; } top_env
                fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = false; sf = true; o_f = false; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = false; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = false; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = false; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = false; sf = false; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = true; sf = true; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = true; zf = false; sf = true; o_f = true; }
                top_env fm in
            let fm =
              FlagMap.add { cf = false; zf = true; sf = true; o_f = true; }
                top_env fm
            in
              FlagMap.add { cf = false; zf = false; sf = true; o_f = true; }
                top_env fm
      
    let update_val env flags dstvar mkvar srcvar mkcvar op arg3 isimm_option
                   =
      (if (op <> AShld) && (op <> AShrd)
       then assert (isimm_option = None)
       else ();
       let dvals = VarMap.find dstvar env in
       let svals = get_vals srcvar env
       in
         if op = Amov
         then mov env flags dstvar mkvar dvals srcvar mkcvar svals
         else
           (match op with
            | Acmov cc ->
                cmov cc env flags dstvar mkvar dvals srcvar mkcvar svals
            | Aarith aop ->
                (match (mkvar, mkcvar) with
                 | (NoMask, NoMask) ->
                     arith env flags dstvar dvals srcvar svals aop
                 | (Mask dmask, Mask smask) ->
                     arith_int8 env flags dstvar dmask dvals srcvar smask svals aop
                 | (_, _) ->
                     failwith
                       "valAD: arithmetic between 8-bit and 32-bit values is not implemented")
 					  | Absr -> bsr env flags dstvar dvals mkvar srcvar svals mkcvar
            | Ashift sop ->
                shift env flags sop dstvar dvals srcvar svals mkcvar
            | AShld ->
                shld_shrd op env flags dstvar dvals mkvar srcvar svals mkcvar
                  arg3 isimm_option
            | AShrd ->
                shld_shrd op env flags dstvar dvals mkvar srcvar svals mkcvar
                  arg3 isimm_option
            | Aflag fop ->
                test_cmp env flags fop dstvar dvals mkvar srcvar svals mkcvar
            | Aimul -> imul env flags dstvar dvals srcvar svals op arg3
            | Acdq ->
                (match (mkvar, mkcvar) with
                 | (NoMask, NoMask) ->
                     cdq env flags dstvar dvals srcvar svals
                 | (_, _) ->
                     failwith
                       "valAD: cdq is only implemented for 32bit values")
            | _ -> assert false))
      
    let updval_set env flags dstvar mask cc =
      let dvals = VarMap.find dstvar env
      in
        match dvals with
        | FSet dset ->
            let msk =
              (match mask with | NoMask -> assert false | Mask msk -> msk) in
            let (v_mask, v_shift) = mask_to_intoff msk in
            let newval =
              (match cc with
               | (true, B) -> (* SETC/SETB/SETNAE *)
                   bool_to_int64 flags.cf
               | (true, L) -> (* SETL/SETNGE *)
                   bool_to_int64 (flags.sf <> flags.o_f)
               | (false, LE) -> (* SETG/SETNLE *)
                   bool_to_int64 ((not flags.zf) && (flags.sf == flags.o_f))
               | _ -> failwith "ValAD: SET with an unsupported condition") in
            let newval = Int64.shift_left newval v_shift in
            let val_set = set_map (fun x -> Int64.logor newval (Int64.logand (Int64.lognot v_mask) x)) dset in
                   let new_env = VarMap.add dstvar (FSet val_set) env
                   in FlagMap.singleton flags new_env
        | _ -> (* For the time being we return top, *)
            (* until a more precise solution is implemented*)
            let top_env = VarMap.add dstvar top env
            in FlagMap.singleton flags top_env
      
    let update_val_twodst env flags dst1var dst1mask dst2var dst2mask svar
                          smask op =
      let dst1vals = VarMap.find dst1var env in
      let dst2vals = VarMap.find dst2var env in
      let svals = get_vals svar env
      in
        match op with
        | Adiv ->
            div env flags dst1var dst1vals dst1mask dst2var dst2vals dst2mask
              svar svals smask
        | Aimullong ->
            mulimullong env flags dst1var dst1vals dst1mask dst2var dst2vals dst2mask
              svar svals smask true
        | Amullong ->
            mulimullong env flags dst1var dst1vals dst1mask dst2var dst2vals dst2mask 
              svar svals smask false											
        | _ ->
            failwith
              "valAD: The only supported operation with two destination operands is division."
      
  end
  
