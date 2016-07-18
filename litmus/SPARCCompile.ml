(*********************************************************************)
(*                          Litmus                                   *)
(*                                                                   *)
(*        Luc Maranget, INRIA Paris-Rocquencourt, France.            *)
(*                                                                   *)
(*  Copyright 2014 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

module Make(V:Constant.S)(C:Arch.Config) =
  struct
    module A = SPARCArch.Make(C)(V)
    open A
    open A.Out
    open Printf

(* No addresses in code *)
    let extract_addrs _ins = StringSet.empty
    let stable_regs _ins = A.RegSet.empty

(************************)
(* Template compilation *)
(************************)

(* Arithmetic *)
    let op3regs op r1 r2 r3 =
      let memo = A.pp_op3 op in
      { empty_ins with
        memo=memo^ " ^i0,^i1,^o0";
        inputs=[r1; r2];
        outputs=[r3]; }

    let op2regsI op r1 kr r2 =
      let memo = A.pp_op3 op in
      { empty_ins with
        memo= sprintf "%s ^i0,%i,^o0" memo kr;
        inputs=[r1];
        outputs=[r2]; }

    let op3regscc op r1 r2 r3 =
      let memo = A.pp_op3 op in
      { empty_ins with
        memo=memo^ "cc ^i0,^i1,^o0";
        inputs=[r1; r2];
        outputs=[r3]; }

    let op2regsIcc op r1 kr r2 =
      let memo = A.pp_op3 op in
      { empty_ins with
        memo= sprintf "%scc ^i0,%i,^o0" memo kr;
        inputs=[r1];
        outputs=[r2]; }

(* Memory *)
    let ldx r1 r2 r3 =
      { empty_ins with
        memo = sprintf "ldx [^i0+^i1],^o0";
        inputs = [r1;r2] ;
        outputs = [r3] ; }

    let ldxi r1 kr r3 =
      { empty_ins with
        memo = sprintf "ldx [^i0+%i],^o0" kr ;
        inputs = [r1] ;
        outputs = [r3] ; }

    let stx r1 r2 r3 =
      { empty_ins with
        memo = sprintf "stx ^i0,[^i1+^i2]";
        inputs = [r1;r2;r3;] ;
        outputs = []; }

    let stxi r1 r2 kr =
      { empty_ins with
        memo = sprintf "stx ^i0,[^i1+%i]" kr ;
        inputs = [r1;r2;] ;
        outputs = []; }

(* Branch *)
    let bc tr_lab bcond condreg lbl =
      { empty_ins with
        memo = sprintf "b%s ^i0,%s"
          (A.pp_bcond bcond) (A.Out.dump_label (tr_lab lbl)) ;
        inputs=[condreg;];
        branch=[Next; Branch lbl] ; }

    let br tr_lab rcond reg lbl =
      { empty_ins with
        memo = sprintf "b%s ^i0,%s"
          (A.pp_rcond rcond) (A.Out.dump_label (tr_lab lbl)) ;
        inputs=[reg;];
        branch=[Next; Branch lbl] ; }

    let emit_lbl lbl =
      { empty_ins with
        memo=sprintf "%s:" (A.Out.dump_label lbl) ;
        label = Some lbl ; branch=[Next] ; }

    let decr r i = assert false

    let no_tr lbl = lbl

    let emit_loop k = assert false

    let compile_ins tr_lab ins k = match ins with
    | BCOND (bcond,condreg,lbl) -> bc tr_lab bcond (A.Creg condreg) lbl::k
    | BRCOND (bcond,reg,lbl) -> br tr_lab bcond reg lbl::k
    | LDX (r1,A.RV r2,r3) -> ldx r1 r2 r3::k
    | LDX (r1,A.K kr,r3) -> ldxi r1 kr r3::k
    | STX (r1,r2,A.RV r3) -> stx r1 r2 r3::k
    | STX (r1,r2,A.K kr) -> stxi r1 r2 kr::k
    | OP3 (None,op,r1,A.RV r2,r3) -> op3regs op r1 r2 r3::k
    | OP3 (None,op,r1,A.K kr, r2) -> op2regsI op r1 kr r2::k
    | OP3 (Some cc,op,r1,A.RV r2,r3) -> op3regscc op r1 r2 r3::k
    | OP3 (Some cc,op,r1,A.K kr, r2) -> op2regsIcc op r1 kr r2::k
    | MEMBAR barrier -> {empty_ins with memo="membar #StoreLoad"; }::k

    let branch_neq r i lab k = op2regsI A.SUB r i (A.Ireg A.G0)::bc no_tr A.NE (A.Creg A.XCC) lab::k

    let branch_eq r i lab k = op2regsI A.SUB r i (A.Ireg A.G0)::bc no_tr A.E (A.Creg A.XCC) lab::k
    let signaling_write _i _k = Warn.fatal "no signaling write for SPARC"

    let emit_tb_wait _ = Warn.fatal "no time base for SPARC"
  end
