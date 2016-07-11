(** Define register, barriers, and instructions for SPARC *)

open Printf

let arch = Archs.sparc

(*************)
(* Registers *)
(*************)

type ireg =
    | G0 | G1 | G2 | G3 
    | G4 | G5 | G6 | G7 
    | O0 | O1 | O2 | O3 
    | O4 | O5 | O6 | O7 
    | L0 | L1 | L2 | L3 
    | L4 | L5 | L6 | L7 
    | I0 | I1 | I2 | I3 
    | I4 | I5 | I6 | I7 

let iregs =
  [
   G0,"g0"; G1,"g1";
   G2,"g2"; G3,"g3";
   G4,"g4"; G5,"g5";
   G6,"g6"; G7,"g7";
   O0,"o0"; O1,"o1";
   O2,"o2"; O3,"o3";
   O4,"o4"; O5,"o5";
   O6,"o6"; O7,"o7";
   L0,"l0"; L1,"l1";
   L2,"l2"; L3,"l3";
   L4,"l4"; L5,"l5";
   L6,"l6"; L7,"l7";
   I0,"i0"; I1,"i1";
   I2,"i2"; I3,"i3";
   I4,"i4"; I5,"i5";
   I6,"i6"; I7,"i7";
 ]

type freg =
  | F0  | F1  | F2  | F3
  | F4  | F5  | F6  | F7
  | F8  | F9  | F10 | F11
  | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19
  | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27
  | F28 | F29 | F30 | F31

let fregs =
  [
   F0  , "f0";   F1  , "f1";
   F2  , "f2";   F3  , "f3";
   F4  , "f4";   F5  , "f5";
   F6  , "f6";   F7  , "f7";
   F8  , "f8";   F9  , "f9";
   F10 , "f10";  F11 , "f11";
   F12 , "f12";  F13 , "f13";
   F14 , "f14";  F15 , "f15";
   F16 , "f16";  F17 , "f17";
   F18 , "f18";  F19 , "f19";
   F20 , "f20";  F21 , "f21";
   F22 , "f22";  F23 , "f23";
   F24 , "f24";  F25 , "f25";
   F26 , "f26";  F27 , "f27";
   F28 , "f28";  F29 , "f29";
   F30 , "f30";  F31 , "f31";
 ]

type condreg = XCC | ICC

type reg =
  | Ireg of ireg
  | Freg of freg
  | Creg of condreg
(*  | PC *)
(*  | NPC *)
  | Symbolic_reg of string
  | Internal of int

let base = Internal 0
and max_idx = Internal 1
and idx = Internal 2
and ephemeral = Internal 3
and loop_idx = Internal 4

let tmp1 = Symbolic_reg "T1"

(* let pc = PC *)

let reg_compare = Pervasives.compare 

let parse_ireg = function
  | "%g0" -> G0
  | "%g1" -> G1
  | "%g2" -> G2
  | "%g3" -> G3
  | "%g4" -> G4
  | "%g5" -> G5
  | "%g6" -> G6
  | "%g7" -> G7
  | "%o0" -> O0
  | "%o1" -> O1
  | "%o2" -> O2
  | "%o3" -> O3
  | "%o4" -> O4
  | "%o5" -> O5
  | "%o6" -> O6
  | "%o7" -> O7
  | "%l0" -> L0
  | "%l1" -> L1
  | "%l2" -> L2
  | "%l3" -> L3
  | "%l4" -> L4
  | "%l5" -> L5
  | "%l6" -> L6
  | "%l7" -> L7
  | "%i0" -> I0
  | "%i1" -> I1
  | "%i2" -> I2
  | "%i3" -> I3
  | "%i4" -> I4
  | "%i5" -> I5
  | "%i6" -> I6
  | "%i7" -> I7
  | _ -> raise Exit

let parse_freg = function
  | "%f0"  -> F0
  | "%f1"  -> F1
  | "%f2"  -> F2
  | "%f3"  -> F3
  | "%f4"  -> F4
  | "%f5"  -> F5
  | "%f6"  -> F6
  | "%f7"  -> F7
  | "%f8"  -> F8
  | "%f9"  -> F9
  | "%f10" -> F10
  | "%f11" -> F11
  | "%f12" -> F12
  | "%f13" -> F13
  | "%f14" -> F14
  | "%f15" -> F15
  | "%f16" -> F16
  | "%f17" -> F17
  | "%f18" -> F18
  | "%f19" -> F19
  | "%f20" -> F20
  | "%f21" -> F21
  | "%f22" -> F22
  | "%f23" -> F23
  | "%f24" -> F24
  | "%f25" -> F25
  | "%f26" -> F26
  | "%f27" -> F27
  | "%f28" -> F28
  | "%f29" -> F29
  | "%f30" -> F30
  | "%f31" -> F31
  | _ -> raise Exit

let parse_reg s =
  try Some (Ireg (parse_ireg s))
  with Exit -> None

let parse_freg s =
  try Some (Freg (parse_freg s))
  with Exit -> None

open PPMode

let add_percent m s = match  m with
| Ascii | Dot -> "%" ^ s
| Latex -> "\\%" ^ s
| DotFig -> "\\\\%" ^ s

let do_pp_ireg m = function
  | G0  -> add_percent m "g0"
  | G1  -> add_percent m "g1"
  | G2  -> add_percent m "g2"
  | G3  -> add_percent m "g3"
  | G4  -> add_percent m "g4"
  | G5  -> add_percent m "g5"
  | G6  -> add_percent m "g6"
  | G7  -> add_percent m "g7"
  | O0  -> add_percent m "o0"
  | O1  -> add_percent m "o1"
  | O2  -> add_percent m "o2"
  | O3  -> add_percent m "o3"
  | O4  -> add_percent m "o4"
  | O5  -> add_percent m "o5"
  | O6  -> add_percent m "o6"
  | O7  -> add_percent m "o7"
  | L0  -> add_percent m "l0"
  | L1  -> add_percent m "l1"
  | L2  -> add_percent m "l2"
  | L3  -> add_percent m "l3"
  | L4  -> add_percent m "l4"
  | L5  -> add_percent m "l5"
  | L6  -> add_percent m "l6"
  | L7  -> add_percent m "l7"
  | I0  -> add_percent m "i0"
  | I1  -> add_percent m "i1"
  | I2  -> add_percent m "i2"
  | I3  -> add_percent m "i3"
  | I4  -> add_percent m "i4"
  | I5  -> add_percent m "i5"
  | I6  -> add_percent m "i6"
  | I7  -> add_percent m "i7"

let do_pp_freg m = function
  | F0  -> add_percent m "f0"
  | F1  -> add_percent m "f1"
  | F2  -> add_percent m "f2"
  | F3  -> add_percent m "f3"
  | F4  -> add_percent m "f4"
  | F5  -> add_percent m "f5"
  | F6  -> add_percent m "f6"
  | F7  -> add_percent m "f7"
  | F8  -> add_percent m "f8"
  | F9  -> add_percent m "f9"
  | F10 -> add_percent m "f10"
  | F11 -> add_percent m "f11"
  | F12 -> add_percent m "f12"
  | F13 -> add_percent m "f13"
  | F14 -> add_percent m "f14"
  | F15 -> add_percent m "f15"
  | F16 -> add_percent m "f16"
  | F17 -> add_percent m "f17"
  | F18 -> add_percent m "f18"
  | F19 -> add_percent m "f19"
  | F20 -> add_percent m "f20"
  | F21 -> add_percent m "f21"
  | F22 -> add_percent m "f22"
  | F23 -> add_percent m "f23"
  | F24 -> add_percent m "f24"
  | F25 -> add_percent m "f25"
  | F26 -> add_percent m "f26"
  | F27 -> add_percent m "f27"
  | F28 -> add_percent m "f28"
  | F29 -> add_percent m "f29"
  | F30 -> add_percent m "f30"
  | F31 -> add_percent m "f31"

let do_pp_condreg m = function
  | XCC -> add_percent m "xcc"
  | ICC -> add_percent m "icc"

let do_pp_reg m = function
  | Ireg r -> do_pp_ireg m r
  | Freg r -> do_pp_freg m r
  | Creg r -> do_pp_condreg m r
(*  | PC -> add_percent m "pc" *)
(*  | NPC -> add_percent m "npc" *)
  | Symbolic_reg r -> "%" ^ r
  | Internal i -> sprintf "i%i" i

let r0 = Ireg G0

let pp_reg = do_pp_reg Ascii

let reg_compare = Pervasives.compare

(************)
(* Barriers *)
(************)

type barrier =
(*  | LoadLoad *)
  | StoreLoad
(*  | LoadStore
  | StoreStore
  | Lookaside
  | MemIssue
  | Sync *)

let all_kinds_of_barriers = 
  [ (* LoadLoad ; *) StoreLoad (* ; LoadStore ; StoreStore ; Lookaside ; MemIssue ; Sync ; *) ]

let pp_barrier b = match b with
(*  | LoadLoad   -> "LoadLoad" *)
  | StoreLoad  -> "membar #StoreLoad"
(*  | LoadStore  -> "LoadStore"
  | StoreStore -> "StoreStore"
  | Lookaside  -> "Lookaside"
  | MemIssue   -> "MemIssue"
  | Sync       -> "Sync" *)

let barrier_compare = Pervasives.compare

(****************)
(* Instructions *)
(****************)

type k = int
type lbl = Label.t

type ccond = int (* Z | N | V | C (LSB) *)
type bcond = A | N | E | NE | L | LE | G | GE | LU | LEU | GU | GEU | POS | NEG | CS | CC | VS | VC
type brcond = RZ | RLEZ | RLZ | RNZ | RGZ | RGEZ
type op3 = ADD | ADDC | AND | ANDN | XOR | XNOR | SUB | SUBC | OR | ORN | SLLX | SRAX | SRLX
type kr = K of k | RV of reg

type instruction =
(* Branches *)
  | BCOND of bcond * condreg * lbl
  | BRCOND of brcond * reg * lbl
(* Load and Store *)
  | LDX of reg * kr * reg
  | STX of reg * reg * kr
(* Compare - This is actually a synthetic instruction?!
  | CMP of reg * kr *)
(* Operations *)
  | OP3 of condreg option * op3 * reg * kr * reg
(* Barrier *)
  | MEMBAR of barrier

let pp_label i = i

let pp_cond = function
  | A  -> "a"
  | N  -> "n"
  | E  -> "e"
  | NE -> "ne"
  | L  -> "l"
  | LE -> "le"
  | G  -> "g"
  | GE -> "ge"
  | LU -> "lu"
  | LEU-> "leu" 
  | GU -> "gu"
  | GEU-> "geu" 
  | POS-> "pos" 
  | NEG-> "neg" 
  | CS -> "cs"
  | CC -> "cc"
  | VS -> "vs"
  | VC -> "vc"

let pp_rcond = function
  | RZ   -> "rz"
  | RLEZ -> "rlez"
  | RLZ  -> "rlz"
  | RNZ  -> "rnz"
  | RGZ  -> "rgz"
  | RGEZ -> "rgez"

let pp_op3 = function
  | ADD  -> "add"
  | ADDC -> "addc" 
  | AND  -> "and"
  | ANDN -> "andn" 
  | XOR  -> "xor"
  | XNOR -> "xnor" 
  | SUB  -> "sub"
  | SUBC -> "subc" 
  | OR   -> "or"
  | ORN  -> "orn"
  | SLLX -> "sllx" 
  | SRAX -> "srax" 
  | SRLX -> "srlx"

let pp_instruction m =
  let pp_reg = do_pp_reg m in

  let pp_kr kr = match kr with
  | K k -> string_of_int k
  | RV r -> pp_reg r in
  
  fun i -> match i with
(* Branches *)
  | BCOND (cond,condreg,lbl) ->
      sprintf "b%s %s, %s"
        (pp_cond cond)
	(pp_reg (Creg condreg))
        (pp_label lbl)
  | BRCOND (rcond,reg,lbl) ->
      sprintf "b%s %s, %s"
        (pp_rcond rcond)
	(pp_reg reg)
        (pp_label lbl)
(* Load and Store *)
  | LDX (r1,kr,r2) ->
      sprintf "ldx [%s + %s], %s"
        (pp_reg r1)
        (pp_kr kr)
        (pp_reg r2)
  | STX (r1,r2,kr) ->
      sprintf "stx %s, [%s + %s]"
        (pp_reg r1)
        (pp_reg r2)
        (pp_kr kr)
(* Compare 
  | CMP (r,kr) ->
      sprintf "cmp %s, %s"
	(pp_reg r)
	(pp_kr kr) *)
(* Operations *)
  | OP3 (Some _,op,r1,kr,r2)->
      sprintf "%scc %s, %s, %s"
        (pp_op3 op)
        (pp_reg r1)
        (pp_kr kr)
        (pp_reg r2)
  | OP3 (None,op,r1,kr,r2)->
      sprintf "%s %s, %s, %s"
        (pp_op3 op)
        (pp_reg r1)
        (pp_kr kr)
        (pp_reg r2)
(* Barrier *)
  | MEMBAR barrier ->
      pp_barrier barrier

let dump_instruction = pp_instruction Ascii

(****************************)
(* Symbolic registers stuff *)
(****************************)

let allowed_for_symb =
  List.map
    (fun r -> Ireg r)
    [G1; G2; G3; G4; G5; G6; G7; 
     O0; O1; O2; O3; O4; O5; O6; O7; 
     L0; L1; L2; L3; L4; L5; L6; L7; 
     I0; I1; I2; I3; I4; I5; I6; I7;]

let fold_regs (f_regs,f_sregs) =

  let fold_reg reg (y_reg,y_sreg) = match reg with
  | Ireg _ | Freg _ | Creg _ 
    -> f_regs reg y_reg,y_sreg
  | Symbolic_reg reg -> y_reg,f_sregs reg y_sreg
  | Internal _ -> y_reg, y_sreg in

  let fold_kr kr y = match kr with
  | K _ -> y
  | RV r -> fold_reg r y in

  fun c ins -> match ins with
  | BCOND _ | MEMBAR _
    -> c
  | BRCOND (_,r,_)
    -> fold_reg r c
  | LDX (r1,kr,r2)
    -> fold_reg r1 (fold_kr kr (fold_reg r2 c))
  | STX (r1,r2,kr)
    -> fold_reg r1 (fold_reg r2 (fold_kr kr c))
(*  | CMP (r,kr)
    -> fold_reg r (fold_kr kr c) *)
  | OP3 (_,_,r1,kr,r2)
    -> fold_reg r1 (fold_kr kr (fold_reg r2 c))

let map_regs f_reg f_symb =

  let map_reg reg = match reg with
  | Ireg _ | Freg _ | Creg _ -> f_reg reg
  | Symbolic_reg reg -> f_symb reg
  | Internal _ -> reg in

  let map_kr kr = match kr with
  | K _ -> kr
  | RV r -> RV (map_reg r) in

  fun ins -> match ins with
  | BCOND _ | MEMBAR _
    -> ins
  | BRCOND (rcond,r,lbl)
    -> BRCOND (rcond,map_reg r,lbl)
  | LDX (r1,kr,r2)
    -> LDX (map_reg r1,map_kr kr,map_reg r2)
  | STX (r1,r2,kr)
    -> STX (map_reg r1,map_reg r2,map_kr kr)
(*  | CMP (r,kr)
    -> CMP (map_reg r,map_kr kr) *)
  | OP3 (c,op,r1,kr,r2)
    -> OP3 (c,op,map_reg r1,map_kr kr,map_reg r2)

(* No addresses buried in SPARC code *)
let fold_addrs _f c _ins = c

let map_addrs _f ins = ins

(* No normalisation (basing this on MIPS/AArch64) *)
let norm_ins ins = ins

(* Instruction continuation *)
let get_next = function
  | BCOND (_,_,lbl)
    -> [Label.Next; Label.To lbl;]
  | BRCOND (_,_,lbl)
    -> [Label.Next; Label.To lbl;]
  | LDX _ | STX _ | (*CMP _ |*) OP3 _ | MEMBAR _
    -> [Label.Next;]

include Pseudo.Make
    (struct
      type ins = instruction
      type reg_arg = reg

      let get_naccesses = function
	| LDX _ | STX _
	  -> 1
	| BCOND _ | BRCOND _
(*	| CMP _ *)
	| OP3 _
	| MEMBAR _
	  -> 0

      let fold_labels k f = function
	| BCOND (_,_,lbl) | BRCOND (_,_,lbl)
	  -> f k lbl
	| _ -> k

      let map_labels f = function
	| BCOND (c,cr,lbl) -> BCOND (c,cr,f lbl)
	| BRCOND (c,r,lbl) -> BRCOND (c,r,f lbl)
	| ins -> ins

    end)

let get_macro _name = raise Not_found
