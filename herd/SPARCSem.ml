(*********************************************************************)
(*                        Memevents                                  *)
(*                                                                   *)
(*               Luc Maranget, INRIA Paris-Rocquencourt, France.     *)
(*                                                                   *)
(*  Copyright 2014 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

(** Semantics of SPARC instructions *)

module Make (C:Sem.Config)(V:Value.S)
=
  struct
    module SPARC = SPARCArch.Make(C.PC)(V)
    module Act = MachAction.Make(SPARC)
    include SemExtra.Make(C)(SPARC)(Act)

(* Barrier pretty print *)
    let storeload = {barrier=SPARC.StoreLoad; pp="membar #StoreLoad";}
        
    let barriers = [storeload;]
    let isync = None

 
(* Semantics proper *)
    let (>>=) = M.(>>=)
    let (>>*=) = M.(>>*=)
    let (>>|) = M.(>>|)
    let (>>!) = M.(>>!)
    let (>>::) = M.(>>::)

    let tr_op = function
      | SPARC.ADD | SPARC.ADDC -> Op.Add
      | SPARC.SUB | SPARC.SUBC -> Op.Sub
      | SPARC.AND | SPARC.ANDN -> Op.And
      | SPARC.OR -> Op.Or
      | SPARC.XOR | SPARC.XNOR -> Op.Xor
      | SPARC.ORN -> Op.Nor
      | SPARC.SLLX -> Op.ShiftLeft
      | SPARC.SRAX -> Op.ShiftRightArith
      | SPARC.SRLX -> Op.ShiftRightLog

    let mk_read ato loc v = Act.Access (Dir.R, loc, v, ato)
					      
    let read_loc = 
      M.read_loc (mk_read false)
    let read_reg r ii = match r with
    | SPARC.Ireg SPARC.G0 -> M.unitT V.zero
    | _ -> 
        M.read_loc (mk_read false) (A.Location_reg (ii.A.proc,r)) ii

    let read_mem a ii  = 
      M.read_loc (mk_read false) (A.Location_global a) ii
    let read_mem_atomic a ii = 
      M.read_loc (mk_read true) (A.Location_global a) ii

    let write_loc loc v ii = 
      M.mk_singleton_es (Act.Access (Dir.W, loc, v, false)) ii

    let write_reg r v ii = match r with
    | SPARC.Ireg SPARC.G0 -> M.unitT ()
    | _ ->
        M.mk_singleton_es
          (Act.Access (Dir.W, (A.Location_reg (ii.A.proc,r)), v, false)) ii

    let write_mem a v ii  = 
      M.mk_singleton_es (Act.Access (Dir.W, A.Location_global a, v, false)) ii

    let write_mem_atomic a v resa ii =
      let eq = [M.VC.Assign (a,M.VC.Atom resa)] in
      M.mk_singleton_es_eq (Act.Access (Dir.W, A.Location_global a, v, true)) eq ii

    let create_barrier b ii = 
      M.mk_singleton_es (Act.Barrier b) ii

    let commit ii = 
      M.mk_singleton_es (Act.Commit) ii

    let flip_flag v = M.op Op.Xor v V.one

    let checkc creg ii = read_reg creg ii >>=
         fun v -> M.op Op.And v V.one

    let checkv creg ii = read_reg creg ii >>=
         fun v -> M.op Op.ShiftRightLog v V.one >>=
         fun v -> M.op Op.And v V.one

    let checkn creg ii = read_reg creg ii >>=
         fun v -> M.op Op.ShiftRightLog v V.one >>=
         fun v -> M.op Op.ShiftRightLog v V.one >>=
         fun v -> M.op Op.And v V.one

    let checkz creg ii = read_reg creg ii >>=
         fun v -> M.op Op.ShiftRightLog v V.one >>=
         fun v -> M.op Op.ShiftRightLog v V.one >>=
         fun v -> M.op Op.ShiftRightLog v V.one >>=
         fun v -> M.op Op.And v V.one

    let checkcc c condreg lbl ii = match c with
    | SPARC.A  (* Always *)
      -> B.branchT lbl
    | SPARC.N  (* Never *)
      -> B.nextT
    | SPARC.E  (* Z *)
      -> checkz condreg ii >>= 
         fun z  -> commit ii >>= 
         fun () -> B.bccT z lbl
    | SPARC.NE (* not Z *) 
      -> checkz condreg ii >>=
         fun z  -> flip_flag z >>=
         fun nz -> commit ii >>= 
         fun () -> B.bccT nz lbl
    | SPARC.L  (* N xor V *) 
      -> checkn condreg ii >>| checkv condreg ii >>=
         fun (n,v) -> M.op Op.Xor n v >>=
         fun l  -> commit ii >>=
         fun () -> B.bccT l lbl
    | SPARC.LE (* Z or (N xor V) *) 
      -> checkn condreg ii >>| checkv condreg ii >>=
         fun (n,v) -> M.op Op.Xor n v >>=
         fun nxorv -> checkz condreg ii >>=
         fun z     -> M.op Op.Or z nxorv >>=
         fun le    -> commit ii >>=
         fun ()    -> B.bccT le lbl
    | SPARC.G  (* not (Z or (N xor V)) *) 
      -> checkn condreg ii >>| checkv condreg ii >>=
         fun (n,v) -> M.op Op.Xor n v >>=
         fun nxorv -> checkz condreg ii >>=
         fun z     -> M.op Op.Or z nxorv >>=
         fun le    -> flip_flag le >>=
         fun g     -> commit ii >>=
         fun ()    -> B.bccT g lbl
    | SPARC.GE (* not (N xor V) *) 
      -> checkn condreg ii >>| checkv condreg ii >>=
         fun (n,v) -> M.op Op.Xor n v >>=
         fun l     -> flip_flag l >>=
         fun nl    -> commit ii >>=
         fun ()    -> B.bccT nl lbl
    | SPARC.LU | SPARC.CS (* C *) 
      -> checkc condreg ii >>=
         fun c  -> commit ii >>= 
         fun () -> B.bccT c lbl
    | SPARC.LEU (* C or Z *) 
      -> checkc condreg ii >>| checkz condreg ii >>=
         fun (c,z) -> M.op Op.Or c z >>=
         fun leu   -> commit ii >>=
         fun ()    -> B.bccT leu lbl
    | SPARC.GU  (* not (C or Z) *) 
      -> checkc condreg ii >>| checkz condreg ii >>=
         fun (c,z) -> M.op Op.Or c z >>=
         fun leu   -> flip_flag leu >>=
         fun gu    -> commit ii >>=
         fun ()    -> B.bccT gu lbl
    | SPARC.GEU | SPARC.CC (* not C *) 
      -> checkc condreg ii >>=
         fun c  -> flip_flag c >>=
         fun nc -> commit ii >>= 
         fun () -> B.bccT nc lbl
    | SPARC.POS (* not N *) 
      -> checkn condreg ii >>=
         fun n  -> flip_flag n >>=
         fun nn -> commit ii >>= 
         fun () -> B.bccT nn lbl
    | SPARC.NEG (* N *) 
      -> checkn condreg ii >>=
         fun n  -> commit ii >>= 
         fun () -> B.bccT n lbl
    | SPARC.VS  (* not V *) 
      -> checkv condreg ii >>= 
         fun v  -> flip_flag v >>=
         fun nv -> commit ii >>= 
         fun () -> B.bccT nv lbl
    | SPARC.VC  (* V *) 
      -> checkv condreg ii >>=
         fun v  -> commit ii >>= 
         fun () -> B.bccT v lbl



(* Entry point *)
    let build_semantics ii =
      M.addT (A.next_po_index ii.A.program_order_index)
        begin match ii.A.inst with
        | SPARC.OP3 (_,SPARC.ANDN,r1,SPARC.RV r2,r3) ->
            read_reg r1 ii >>|  read_reg r2 ii >>=
            fun (v1,v2) -> M.op (tr_op SPARC.XNOR) v1 v2 >>=
            fun v -> M.op Op.Nor v (V.intToV 0) >>=
            fun v -> write_reg r3 v ii >>! B.Next
        | SPARC.OP3 (_,SPARC.XNOR,r1,SPARC.RV r2,r3) ->
            read_reg r1 ii >>|  read_reg r2 ii >>=
            fun (v1,v2) -> M.op (tr_op SPARC.XNOR) v1 v2 >>=
            fun v -> M.op Op.Nor v (V.intToV 0) >>=
            fun v -> write_reg r3 v ii >>! B.Next
        | SPARC.OP3 (_,op,r1,SPARC.RV r2,r3) ->
            read_reg r1 ii >>|  read_reg r2 ii >>=
            fun (v1,v2) -> M.op (tr_op op) v1 v2 >>=
            fun v -> write_reg r3 v ii >>! B.Next
        | SPARC.OP3 (_,op,r1,SPARC.K k,r2) ->
            read_reg r1 ii >>=
            fun v -> M.op (tr_op op) v (V.intToV k) >>=
            fun v -> write_reg r2 v ii >>! B.Next
        | SPARC.BCOND (c,condreg,lbl) ->
            checkcc c (SPARC.Creg condreg) lbl ii
        | SPARC.BRCOND (c,reg,lbl) ->
	    read_reg reg ii >>=
            fun v -> 
              M.op (match c with
                   | SPARC.RZ   -> Op.Eq
                   | SPARC.RLEZ -> Op.Le
                   | SPARC.RLZ  -> Op.Lt
                   | SPARC.RNZ  -> Op.Ne
                   | SPARC.RGZ  -> Op.Gt
                   | SPARC.RGEZ -> Op.Ge)
                   v V.zero >>=
            fun v -> commit ii >>=
            fun () -> B.bccT v lbl
        | SPARC.LD (r1,SPARC.RV r2,r3) ->
            read_reg r1 ii >>| read_reg r2 ii >>=
            fun (v1,v2) -> M.add v1 v2 >>=
            fun ea      -> read_mem ea ii >>=
            fun v       -> write_reg r3 v ii >>! B.Next
        | SPARC.LD (r1,SPARC.K k,r2) ->
            read_reg r1 ii >>=
            fun a  -> M.add a (V.intToV k) >>=
            fun ea -> read_mem ea ii >>=
            fun v  -> write_reg r2 v ii >>! B.Next
        | SPARC.ST (r1,r2,SPARC.RV r3) ->
            read_reg r2 ii >>| read_reg r3 ii >>=
            fun (v2,v3) -> M.add v2 v3 >>=
            fun ea      -> read_reg r1 ii >>=
            fun v1      -> write_mem ea v1 ii >>! B.Next
        | SPARC.ST (r1,r2,SPARC.K k) ->
            read_reg r1 ii >>| read_reg r2 ii >>=
            fun (v1,v2) -> M.add v2 (V.intToV k) >>=
            fun ea     -> write_mem ea v1 ii >>! B.Next
(*        | SPARC.LDX (r1,SPARC.RV r2,r3) ->
            read_reg r1 ii >>| read_reg r2 ii >>=
            fun (v1,v2) -> M.add v1 v2 >>=
            fun ea      -> read_mem ea ii >>=
            fun v       -> write_reg r3 v ii >>! B.Next
        | SPARC.LDX (r1,SPARC.K k,r2) ->
            read_reg r1 ii >>=
            fun a  -> M.add a (V.intToV k) >>=
            fun ea -> read_mem ea ii >>=
            fun v  -> write_reg r2 v ii >>! B.Next
        | SPARC.STX (r1,r2,SPARC.RV r3) ->
            read_reg r2 ii >>| read_reg r3 ii >>=
            fun (v2,v3) -> M.add v2 v3 >>=
            fun ea      -> read_reg r1 ii >>=
            fun v1      -> write_mem ea v1 ii >>! B.Next
        | SPARC.STX (r1,r2,SPARC.K k) ->
            read_reg r1 ii >>| read_reg r2 ii >>=
            fun (v1,v2) -> M.add v2 (V.intToV k) >>=
            fun ea     -> write_mem ea v1 ii >>! B.Next *)
        | SPARC.MEMBAR mbtype ->
            create_barrier mbtype ii >>! B.Next
        end
end
