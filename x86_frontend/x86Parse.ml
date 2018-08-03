(* Copyright (c) 2013-2014, IMDEA Software Institute.         *)
(* See ../LICENSE for authorship and licensing information    *)

(* Copyright (c) 2005, Regents of the University of California
 * All rights reserved.
 *
 * Author: Adam Chlipala
 * Extended by: Goran Doychev, Boris Koepf, Laurent Mauborgne, Johannes Schickel, Alexandra Weber   
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 *   this list of conditions and the following disclaimer.
 * - Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * - Neither the name of the University of California, Berkeley nor the names of
 *   its contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR 
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *)

(* Parsing opcodes *)

open AsmUtil
open X86Types
open X86Util
open Printf

exception Parse of string

let file_base_offset = ref 0


  
let rec read_instr_body bits seg_override =
  let position = get_byte bits in
  let byte, bits = read_uint bits 8 in

  let arith_to_rm aop =
    let dst, bits, spare = read_rm32_with_spare bits seg_override in
    Arith (aop, dst, Reg (int_to_reg32 spare)), bits in

  let arith_from_rm aop =
    let src, bits, spare = read_rm32_with_spare bits seg_override in
    Arith (aop, Reg (int_to_reg32 spare), src), bits in

  let shift doRest =
    let dst, bits, spare = read_rm32_with_spare bits seg_override in
    let sop = int_to_shift_op spare in
    let offset, bits = doRest bits in
    Shift (sop, dst, offset), bits in
  (*printf "Byte = %x\n" byte;*)
  
  if byte = 0x65 then 
    (* GS segment override *)
    read_instr_body bits (Some GS)
  else if byte = 0x66 then
    (* 16-bit mode instruction *)
    raise (Parse (Printf.sprintf "Unsupported 16-bit instruction at position 0x%x" position))
 else if byte >= 0x40 && byte < 0x40 + nRegs32 then
    Inc (Reg (int_to_reg32 (byte - 0x40))), bits
  else if byte >= 0x48 && byte < 0x48 + nRegs32 then
    Dec (Reg (int_to_reg32 (byte - 0x48))), bits
  else if byte >= 0x50 && byte < 0x50 + nRegs32 then
    Push (Reg (int_to_reg32 (byte - 0x50))), bits
  else if byte >= 0x58 && byte < 0x58 + nRegs32 then
    Pop (Reg (int_to_reg32 (byte - 0x58))), bits
  else if byte >= 0x70 && byte < 0x70 + nCcs then
    let loc = get_byte bits + 1 in
    let imm, bits = read_int32 bits 8 in
    Jcc (int_to_cc (byte - 0x70), Int64.add (Int64.of_int (!file_base_offset + loc)) imm), bits
  else if byte >= 0xB8 && byte < 0xB8 + nRegs32 then
    let imm, bits = read_uint32 bits 32 in
    Mov (Reg (int_to_reg32 (byte - 0xB8)), Imm imm), bits
  else if byte > 0x90 && byte < 0x90 + nRegs32 then
    Exchange(int_to_reg32 (byte - 0x90), EAX), bits
  else match byte with
    0x00 -> 
      let dst, bits, spare = read_rm8_with_spare bits seg_override in
      Arithb (Add, dst, Reg (int_to_reg8 spare)), bits
  | 0x01 ->
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      Arith (Add, dst, Reg (int_to_reg32 spare)), bits
  | 0x02 -> 
      let src, bits, spare = read_rm8_with_spare bits seg_override in
      Arithb (Add, Reg (int_to_reg8 spare), src), bits
  | 0x03 ->
      let src, bits, spare = read_rm32_with_spare bits seg_override in
      Arith (Add, Reg (int_to_reg32 spare), src), bits
  | 0x04 -> 
        let imm, bits = read_uint32 bits 8 in
        Arithb(Add, Reg AL, Imm imm), bits
  | 0x05 -> 
    let imm, bits = read_uint32 bits 32 in
    Arith(Add, Reg EAX, Imm imm), bits
	| 0x07 -> 
		Pop (Reg (int_to_reg32 (segment_reg_to_int ES))), bits
	| 0x08 -> 
      let dst, bits, spare = read_rm8_with_spare bits seg_override in
      Arithb (Or, dst, Reg (int_to_reg8 spare)), bits
  | 0x09 -> arith_to_rm Or
  | 0x0B -> arith_from_rm Or
  | 0x0D ->
        let imm, bits = read_uint32 bits 32 in
        Arith(Or, Reg EAX, Imm imm), bits
	| 0x11 -> 
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      Arith (Addc, dst, Reg (int_to_reg32 spare)), bits
	| 0x13 -> 
		  let src, bits, spare = read_rm32_with_spare bits seg_override in
      Arith (Addc, Reg (int_to_reg32 spare), src), bits		
	| 0x18 -> 
		let dst, bits, spare = read_rm8_with_spare bits seg_override in
    Arithb (Subb, dst, Reg (int_to_reg8 spare)), bits
  | 0x19 -> arith_to_rm Subb
	| 0x1B ->
		let src, bits, spare = read_rm32_with_spare bits seg_override in
   	 Arith (Subb, Reg (int_to_reg32 spare), src), bits
  | 0x1C -> let imm, bits = read_uint32 bits 8 in
        Arithb(Subb, Reg AL, Imm imm), bits
  | 0x21 -> arith_to_rm And
  | 0x23 -> arith_from_rm And
  | 0x25 -> let disp, bits = read_int32 bits 32 in
      Arith (And, Reg EAX, Imm disp), bits
  | 0x29 -> arith_to_rm Sub
  | 0x2B -> arith_from_rm Sub
  | 0x2C -> let imm, bits = read_uint32 bits 8 in
        Arithb(Sub, Reg AL, Imm imm), bits
  | 0x2D -> let imm, bits = read_uint32 bits 32 in
        Arith(Sub, Reg EAX, Imm imm), bits
	| 0x30 -> 
		let dst, bits, spare = read_rm8_with_spare bits seg_override in
		let src = Reg (int_to_reg8 spare) in
		Arithb(Xor, dst, src),bits
  | 0x31 -> arith_to_rm Xor
  | 0x33 -> arith_from_rm Xor
  | 0x34 -> let imm, bits = read_uint32 bits 8 in
        Arithb(Xor, Reg AL, Imm imm), bits
  | 0x35 -> 
    let imm, bits = read_uint32 bits 32 in
    Arith(Xor, Reg EAX, Imm imm), bits
  | 0x39 ->
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      Cmp(dst, Reg(int_to_reg32 spare)), bits
  | 0x3B ->
      let src, bits, spare = read_rm32_with_spare bits seg_override in
      Cmp(Reg(int_to_reg32 spare), src), bits
	| 0x3C ->
      let imm, bits = read_uint32 bits 8 in
			Cmpb(Reg AL, Imm imm), bits
  | 0x3D ->
      let disp, bits = read_int32 bits 32 in
      Cmp (Reg EAX, Imm disp), bits
  | 0x69 -> 
    let src, bits, dst = read_rm32_with_spare bits seg_override in
    let imm, bits = read_int32 bits 32 in
      Imul ((int_to_reg32 dst), src, Some imm), bits
  | 0x68 ->
      let imm, bits = read_uint32 bits 32 in
      Push (Imm imm), bits
  | 0x6A ->
      let imm, bits = read_uint32 bits 8 in
      Push (Imm imm), bits
  | 0x6B -> 
    let src, bits, dst = read_rm32_with_spare bits seg_override in
    let imm, bits = read_int32 bits 8 in
      Imul ((int_to_reg32 dst), src, Some imm), bits				
  | 0x80 ->
      let dst, bits, spare = read_rm8_with_spare bits seg_override in
      let aop = int_to_arith_op spare in
      let disp, bits = read_int32 bits 8 in
      Arithb (aop, dst, Imm disp), bits
  | 0x81 ->
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      let aop = int_to_arith_op spare in
      let disp, bits = read_int32 bits 32 in
      Arith (aop, dst, Imm disp), bits
  | 0x83 ->
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      let disp, bits = read_int32 bits 8 in
        let aop = int_to_arith_op spare in
        Arith (aop, dst, Imm disp), bits
	| 0x84 ->    (* test *)
			let dst, bits, spare = read_rm8_with_spare bits seg_override in			
			Testb(dst, Reg(int_to_reg8 spare)), bits
  | 0x85 ->
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      Test(dst, Reg(int_to_reg32 spare)), bits
  | 0x88 ->
      let dst, bits, spare = read_rm8_with_spare bits seg_override in
      Movb (dst, Reg (int_to_reg8 spare)), bits
  | 0x89 ->
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      Mov (dst, Reg (int_to_reg32 spare)), bits
  | 0x8A ->
      let src, bits, spare = read_rm8_with_spare bits seg_override in
      Movb (Reg (int_to_reg8 spare), src), bits
  | 0x8B ->
      let src, bits, spare = read_rm32_with_spare bits seg_override in
      Mov (Reg (int_to_reg32 spare), src), bits
  | 0x8D ->
      let gop, bits, spare = read_rm32_with_spare bits seg_override in
      begin match gop with
        Address addr -> Lea (int_to_reg32 spare, addr), bits
      | _ -> raise (Parse "Weird LEA operand")
      end
  | 0x90 -> Skip, bits
  | 0x99 -> Cdq, bits
  | 0xA0 ->
      let imm, bits = read_uint32 bits 32 in
      Movb (Reg AL, Address {addrDisp = imm; addrBase = None; addrIndex = None; segBase = None}), bits
  | 0xA1 ->
      let imm, bits = read_uint32 bits 32 in
      Mov (Reg EAX, Address {addrDisp = imm; addrBase = None; addrIndex = None; 
      segBase = seg_override}), bits
  | 0xA2 ->
      let imm, bits = read_uint32 bits 32 in
      Movb (Address {addrDisp = imm; addrBase = None; addrIndex = None; segBase = None}, Reg AL), bits
  | 0xA3 ->
      let imm, bits = read_uint32 bits 32 in
      Mov (Address {addrDisp = imm; addrBase = None; addrIndex = None; segBase = None}, Reg EAX), bits
  | 0xA9 -> 
			let imm, bits = read_uint32 bits 32 in
      Test (Reg EAX, Imm imm), bits
  | 0xC1 -> shift (fun bits ->
      let imm, bits = read_uint32 bits 8 in
      Imm imm, bits)
  | 0xC3 -> Ret, bits
  | 0xC6 ->
      let dst, bits, spare = read_rm8_with_spare bits seg_override in
      begin match spare with
        0 ->
          let imm, bits = read_uint32 bits 8 in
          Movb (dst, Imm imm), bits
      | _ -> raise (Parse (Printf.sprintf "Unknown 0xC6 instruction 0x%x at position 0x%x" spare position))

      end
  | 0xC7 ->
      let dst, bits, spare = read_rm32_with_spare bits seg_override in
      begin match spare with
        0 ->
          let imm, bits = read_uint32 bits 32 in
          Mov (dst, Imm imm), bits
      | _ -> raise (Parse (Printf.sprintf "Unknown 0xC7 instruction 0x%x at position 0x%x" spare position))
      end
  | 0xC9 -> Leave, bits
  | 0xD1 -> 
      shift (fun bits -> Imm (Int64.of_int 1), bits)
  | 0xD3 -> shift (fun bits -> Reg CL, bits)
  | 0xE8 ->
      let loc = get_byte bits + 4 in
      let imm, bits = read_int32 bits 32 in
      Call (Imm (Int64.add (Int64.of_int (!file_base_offset + loc)) imm)), bits
  | 0xE9 ->
      let loc = get_byte bits + 4 in
      let imm, bits = read_int32 bits 32 in
      Jmp (Imm(Int64.add (Int64.of_int (!file_base_offset + loc)) imm)), bits
  | 0xEB ->
      let loc = get_byte bits + 1 in
      let imm, bits = read_int32 bits 8 in
      Jmp (Imm(Int64.add (Int64.of_int (!file_base_offset + loc)) imm)), bits
  | 0xF4 -> Halt, bits
	| 0xF6 -> 
			let dst, bits, spare = read_rm32_with_spare bits seg_override in
			begin match spare with
			| 0 ->
  			let imm, bits = read_uint32 bits 8 in
  			Test(dst, Imm imm), bits 
			| _ -> raise (Parse (Printf.sprintf "Unknown 0xF6 instruction 0x%x at position 0x%x" spare position))
			end
  | 0xF7 -> 
      let gop, bits, spare = read_rm32_with_spare bits seg_override in
      begin match spare with
			| 6 -> 
				Div (EDX, EAX, gop), bits
      | 2 -> Not gop, bits
			| 3 -> Arith(Neg, gop, Imm 0x00000000L), bits (* Reusing Sub is not possible because Sub treats the first operand as destination and substracts the second operand from it*)
      | 4 (*100*)->  MulLong (EDX, EAX, gop), bits 
      | 5 (*101*)->  ImulLong (EDX, EAX, gop), bits 
      | _ -> raise (Parse (Printf.sprintf "Unknown 0xF7 instruction 0x%x at position 0x%x" spare position))
      end
  (* | 0xF9 -> FlagSet(CF, true), bits *)
  | 0xFF ->
      let gop, bits, spare = read_rm32_with_spare bits seg_override in
      begin match spare with
        0 -> Inc gop, bits
      | 1 -> Dec gop, bits
      | 2 -> Call gop, bits
      | 4 -> Jmp gop, bits
      | 6 -> Push gop, bits
      | _ -> raise (Parse (Printf.sprintf "Unknown 0xFF instruction 0x%x at position 0x%x" spare position))
      end
  | 0x0F ->
      let opc,bits = read_uint bits 8 in
      if opc >= 0x80 && opc < 0x80 + nCcs then
        let loc = get_byte bits + 4 in
        let imm, bits = read_int32 bits 32 in
        Jcc (int_to_cc (opc - 0x80), Int64.add (Int64.of_int (!file_base_offset + loc)) imm), bits
      else if opc >= 0x90 && opc < 0x90 + nCcs then
        let _,_ = read_uint bits 8 in (* throw away first byte *)
        let src,bits,_ = read_rm8_with_spare bits seg_override in
        Set (int_to_cc (opc - 0x90), src),bits
      else begin match opc with
			| 0x48 ->
				let src, bits, spare = read_rm32_with_spare bits seg_override in
					let _,_ = read_uint bits 8 in (* throw away first byte *)	
					Cmov (int_to_cc (opc - 0x40), Reg (int_to_reg32 spare), src), bits
				
			| 0xA4 -> (* reg_mem $v, reg $v$, imm 8 *)
			(* 1st operand: register to be shifted*)
			(* 2nd operand: bit pattern to be shifted in*)
			(* 3rd operand: offset by which to shift (as immediate)*)
				(* assumption: read_rm32_with_spare returns the first operand, the *)
				(* remaining bit string and the second operand*)
				let sregmem, bits, patternreg = read_rm32_with_spare bits seg_override in
				(* assumption: read_uint32 returns the third operand*)
  	      let offset, bits = read_uint32 bits 8 in	
						Shld (sregmem, Reg (int_to_reg32 patternreg), Imm offset), bits			

			| 0xA5 -> (* reg_mem $v, reg $v$, rcx 8 *)
			(* 1st operand: register to be shifted*)
			(* 2nd operand: bit pattern to be shifted in*)
			(* There is no third operand. The offset is read from register CL*)	
				(* assumption: read_rm32_with_spare returns the first operand, the *)
				(* remaining bit string and the second operand*)
				let sregmem, bits, patternreg = read_rm32_with_spare bits seg_override in			
					Shld (sregmem, Reg (int_to_reg32 patternreg), Reg CL), bits
		
			| 0xAC -> (* reg_mem $v, reg $v$, imm 8 *)
				let sregmem, bits, patternreg = read_rm32_with_spare bits seg_override in
  	      let offset, bits = read_uint32 bits 8 in	
						Shrd (sregmem, Reg (int_to_reg32 patternreg), Imm offset), bits				
							
			| 0xAD -> (* reg_mem $v, reg $v$, rcx 8 *)		
				let sregmem, bits, patternreg = read_rm32_with_spare bits seg_override in			
					Shrd (sregmem, Reg (int_to_reg32 patternreg), Reg CL), bits
      | 0xAF -> 
        let src, bits, dst = read_rm32_with_spare bits seg_override in
        Imul ((int_to_reg32 dst), src, None), bits
      | 0xB6 ->
        let _,_ = read_uint bits 8 in (* throw away first byte *)
        let src,bits,spare = read_rm8_with_spare bits seg_override in
          Movzx (Reg (int_to_reg32 spare),src),bits
			| 0xBD ->
				
	   	 let src, bits, spare = read_rm32_with_spare bits seg_override in
    			Bsr ((int_to_reg32 spare), src), bits				
      | _ -> raise (Parse (Printf.sprintf "Unknown 0x0F instruction 0x%x at position 0x%x" opc position))
      end
  | _ -> raise (Parse (Printf.sprintf "Unknown instruction 0x%x at position 0x%x" byte position))

  
let read_instr bits =
  read_instr_body bits None
