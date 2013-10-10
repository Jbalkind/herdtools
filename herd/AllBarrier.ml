(*********************************************************************)
(*                        Memevents                                  *)
(*                                                                   *)
(* Jade Alglave, Luc Maranget, INRIA Paris-Rocquencourt, France.     *)
(* Susmit Sarkar, Peter Sewell, University of Cambridge, UK.         *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

(* Union of relevant PPC,ARM and X86 barriers *)
module type S =
  sig
    type a (* Native arch barrier *)
    type b =
      | SYNC | LWSYNC | ISYNC | EIEIO (* PPC memory model barrier *)
      | DSB | DMB | ISB               (* ARM barrier *)
      | DSBST | DMBST
      | MFENCE | SFENCE | LFENCE
    val a_to_b : a -> b
    val pp_isync : string
  end


module FromPPC(B:PPCBarrier.S) = struct
  type a = B.a

  type b =
      | SYNC | LWSYNC | ISYNC | EIEIO (* PPC memory model barrier *)
      | DSB | DMB | ISB               (* ARM barrier *)
      | DSBST | DMBST
      | MFENCE | SFENCE | LFENCE

  let a_to_b a = match B.a_to_b a with
  | B.LWSYNC -> LWSYNC
  | B.SYNC -> SYNC
  | B.ISYNC -> ISYNC
  | B.EIEIO -> EIEIO

  let pp_isync = "isync"
end

module FromARM(AB:ARMBarrier.S) = struct
  type a = AB.a

  type b =
      | SYNC | LWSYNC | ISYNC | EIEIO (* PPC memory model barrier *)
      | DSB | DMB | ISB               (* ARM barrier *)
      | DSBST | DMBST
      | MFENCE | SFENCE | LFENCE

  let a_to_b a = match AB.a_to_b a with
  | AB.DSB ARMBase.SY -> DSB
  | AB.DMB ARMBase.SY -> DMB
  | AB.DSB ARMBase.ST -> DSBST
  | AB.DMB ARMBase.ST -> DMBST
  | AB.ISB -> ISB
  | _ -> Warn.fatal "Not implemented in AllBarriers"

  let pp_isync = "isb"
end

module FromX86(XB:X86Barrier.S) = struct

  type a = XB.a

  type b =
      | SYNC | LWSYNC | ISYNC | EIEIO (* PPC memory model barrier *)
      | DSB | DMB | ISB               (* ARM barrier *)
      | DSBST | DMBST
      | MFENCE | SFENCE | LFENCE

  let a_to_b a = match XB.a_to_b a with
  | XB.MFENCE -> MFENCE
  | XB.SFENCE -> SFENCE 
  | XB.LFENCE -> LFENCE

  let pp_isync = "???"
end