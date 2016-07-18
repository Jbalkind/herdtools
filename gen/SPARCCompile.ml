(*********************************************************************)
(*                         Diy                                       *)
(*                                                                   *)
(*   Jade Alglave, Luc Maranget INRIA Paris-Rocquencourt, France.    *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique. All rights reserved. This file is distributed    *)
(*  under the terms of the Lesser GNU General Public License.        *)
(*********************************************************************)

open Printf
open Code

module Make(Cfg:CompileCommon.Config) : XXXCompile.S =
  struct

(* Common *)
    module SPARC = SPARCArch
    include CompileCommon.Make(Cfg)(SPARC)

    let ppo _f k = k

    open SPARC
    open C


(* Utilities *)
    let next_reg x = SPARC.alloc_reg x

    let next_init st p init loc =
      let rec find_rec = function
        | (Reg (p0,r0),loc0)::_ when loc0 = loc && p = p0 ->
            r0,init,st
        | _::rem -> find_rec rem
        | [] ->
            let r = Symbolic_reg (sprintf "%s%i" loc p) in
            r,(Reg (p,r),loc)::init,st in
      find_rec init

    let pseudo = List.map (fun i -> Instruction i)

(*********)
(* loads *)
(*********)
    let do_branch cond r i lab k = match i with
    | (K 0) ->
        BRCOND (cond,r,lab)::k
    | _ ->
        OP3 (None,SUB,r,i,tmp1)::
        BRCOND (cond,tmp1,lab)::k

    let branch_neq r i lab k = do_branch RNZ r i lab k

    let _branch_eq r i lab k = do_branch RZ r i lab k


    let emit_load st p init x =
      let rA,st = next_reg st in
      let rB,init,st = next_init st p init x in
      rA,init,pseudo [LD (rB,K 0,rA)],st

    let emit_load_not_zero st p init x =
      let rA,st = next_reg st in
      let rB,init,st = next_init st p init x in
      let lab = Label.next_label "L" in
      rA,init,
      Label (lab,Nop)::
      pseudo
        (LD (rB,K 0,rA)::branch_neq rA (K 0) lab []),
      st

    let emit_load_one st p init x =
      let rA,st = next_reg st in
      let rB,init,st = next_init st p init x in
      let lab = Label.next_label "L" in
      rA,init,
      Label (lab,Nop)::
      pseudo (LD (rB,K 0,rA)::branch_neq rA (K 1) lab []),
      st

    let emit_load_not st p init x bne =
      let rA,st = next_reg st in
      let rC,st = next_reg st in
      let rB,init,st = next_init st p init x in
      let lab = Label.next_label "L" in
      let out = Label.next_label "L" in
      rA,init,
      Instruction (OP3 (None,ADD,Ireg G0,K 200,rC))::
      (* 200 X about 5 ins looks for a typical memory delay *)
      Label (lab,Nop)::
      pseudo
        (LD (rB,K 0,rA)::
         bne rA out
           (OP3 (None,SUB,rC,K 1,rC)::branch_neq rC (K 0) lab []))@
      [Label (out,Nop)],
      st
        
    let emit_load_not_eq st p init x rP =
      emit_load_not st p init x
        (fun r lab k -> branch_neq r (RV rP) lab k)

    let emit_load_not_value st p init x v =
      emit_load_not st p init x
        (fun r lab k -> branch_neq r (K v) lab k)

    let emit_load_idx st p init x idx =
      let rA,st = next_reg st in
      let rB,init,st = next_init st p init x in
      rA,init,pseudo [LD (rB,idx,rA)],st

(**********)
(* Stores *)
(**********)

    let emit_store_reg st p init x rA =
      let rB,init,st = next_init st p init x in
      init,[Instruction (ST (rA,rB,K 0))],st

    let emit_store_idx_reg st p init x idx rA =
      let rB,init,st = next_init st p init x in
      let cs = [ST (rA,rB,idx);] in
      init,pseudo cs,st

    let emit_store st p init x v =
      let rA,st = next_reg st in
      let init,cs,st = emit_store_reg st p init x rA in
      init,Instruction (OP3 (None,ADD,Ireg G0,K v,rA))::cs,st

    let emit_store_idx st p init x idx v =
      let rA,st = next_reg st in
      let init,cs,st = emit_store_idx_reg st p init x idx rA in
      init,Instruction (OP3 (None,ADD,Ireg G0,K v,rA))::cs,st

(*************)
(* Acccesses *)
(*************)

    let emit_access st p init e = match e.dir,e.atom with
    | R,None ->
        let r,init,cs,st = emit_load st p init e.loc in
        Some r,init,cs,st
    | R,Some Reserve | R,Some Atomic ->
        Warn.fatal "No load atomic/reserve on SPARC yet"
    | W,None -> 
        let init,cs,st = emit_store st p init e.loc e.v in
        None,init,cs,st
    | W,Some Reserve | W,Some Atomic ->
        Warn.fatal "No store atomic/reserve on SPARC yet"
    | _, Some (Mixed _) ->
        assert false

(*    let emit_exch st p init er ew = *)
    let emit_exch _ _ _ _ _ =
      Warn.fatal "emit_exch not implemented on SPARC yet"

    let emit_access_dep_addr st p init e r1 =
      let r2,st = next_reg st in
      let c = OP3 (None,XOR,r1,RV r1,r2) in
      match e.dir,e.atom with
      | R,None ->
          let r,init,cs,st = emit_load_idx st p init e.loc (RV r2) in
          Some r,init, Instruction c::cs,st
      | R,Some Reserve ->
          Warn.fatal "Load reserve not implemented on SPARC yet"
      | R,Some Atomic ->
          Warn.fatal "Load atomic not implemented on SPARC yet"
      | W,None ->
          let init,cs,st = emit_store_idx st p init e.loc (RV r2) e.v in
          None,init,Instruction c::cs,st
      | W,Some Reserve ->
          Warn.fatal "Store reserve not implemented on SPARC yet"
      | W,Some Atomic ->
          Warn.fatal "Store atomic not implemented on SPARC yet"
      | _,Some (Mixed _) -> assert false

(*    let emit_exch_dep_addr st p init er ew rd = *)
    let emit_exch_dep_addr _ _ _ _ _ _ =
      Warn.fatal "emit_ach_dep_addr not implemented on SPARC yet"

    let emit_access_dep st p init e dp r1 = match dp with
    | ADDR -> emit_access_dep_addr st p init e r1
    | DATA -> Warn.fatal "emit_access_dep_data not implemented on SPARC yet"
    | CTRL -> Warn.fatal "emit_access_ctrl not implemented on SPARC yet"

    let emit_exch_dep st p init er ew dp r1 = match dp with
    | ADDR -> emit_exch_dep_addr st p init er ew  r1
    | DATA -> Warn.fatal "emit_exch_dep_data not implemented on SPARC yet"
    | CTRL -> Warn.fatal "emit_exch_dep_addr not implemented on SPARC yet"


(* Fences *)

    let emit_fence f =
      Instruction
        (match f with
        | StoreLoad -> MEMBAR StoreLoad)

    let stronger_fence = StoreLoad

(* Check load *)
    let check_load p r e =
      let lab = Label.exit p in
      fun k -> pseudo (branch_neq r (K e.v) lab [])@k

(* Postlude *)
    let does_jump lab cs =
      List.exists
        (fun i -> match i with
        | Instruction (BCOND (_,_,lab0)|BRCOND (_,_,lab0)) ->
            (lab0:string) = lab
        | _ -> false)
        cs

    let does_fail p cs = does_jump (Label.fail p) cs
    let does_exit p cs = does_jump (Label.exit p) cs

    let postlude st p init cs =
      if does_fail p cs then
        let init,okcs,st = emit_store st p init Code.ok 0 in
        init,
        cs@
        Instruction (BCOND (SPARC.A,XCC,Label.exit p))::
        Label (Label.fail p,Nop)::
        okcs@
        [Label (Label.exit p,Nop)],
        st
      else if does_exit p cs then
        init,cs@[Label (Label.exit p,Nop)],st
      else init,cs,st

  end
