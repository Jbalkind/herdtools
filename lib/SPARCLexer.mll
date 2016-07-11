(*********************************************************************)
(*                        DIY                                        *)
(*                                                                   *)
(*               Luc Maranget, INRIA Paris-Rocquencourt, France.     *)
(*                                                                   *)
(*  Copyright 2014 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

{
module Make(O:LexUtils.Config) = struct
open Lexing
open LexMisc
open SPARCParser
module A = SPARCBase
module LU = LexUtils.Make(O)

let check_name = function
(* Branch *)
  | "be"    -> BE  
  | "bne"   -> BNE 
  | "bleu"  -> BLEU
  | "blu"   -> BLU 
  | "ble"   -> BLE 
  | "bl"    -> BL  
  | "bgeu"  -> BGEU
  | "bge"   -> BGE 
  | "bgu"   -> BGU 
  | "bg"    -> BG  
  | "bpos"  -> BPOS
  | "bneg"  -> BNEG
  | "bcs"   -> BCS 
  | "bcc"   -> BCC 
  | "bvs"   -> BVS 
  | "bvc"   -> BVC 
(* Branch Reg *)
  | "brz"   -> BRZ
  | "brlez" -> BRLEZ
  | "brlz"  -> BRLZ
  | "brnz"  -> BRNZ
  | "brgz"  -> BRGZ
  | "brgez" -> BRGEZ
(* Load and Store *)
  | "ldx"   -> LDX
  | "stx"   -> STX
(* Operations *)
  | "addc"  -> ADDC 
  | "add"   -> ADD 
  | "xor"   -> XOR 
  | "xnor"  -> XNOR 
  | "subc"  -> SUBC 
  | "sub"   -> SUB 
  | "orn"   -> ORN 
  | "or"    -> OR  
  | "sllx"  -> SLLX 
  | "srax"  -> SRAX 
  | "srlx"  -> SRLX
(* Barrier *)
  | "membar" -> MEMBAR
  | name -> NAME name

}
let digit = [ '0'-'9' ]
let alpha = [ 'a'-'z' 'A'-'Z']
let name  = alpha (alpha|digit|'_' | '/' | '.' | '-')*
let num = digit+

rule token = parse
| [' ''\t'] { token lexbuf }
| '\n'      { incr_lineno lexbuf; token lexbuf }
| "(*"      { LU.skip_comment lexbuf ; token lexbuf }
| '-' ? num as x { NUM (int_of_string x) }
| 'P' (num as x)
    { PROC (int_of_string x) }
| '%' (name as name) (* { SYMB_REG name } *)
      { match A.parse_reg ("%" ^ name) with
      | Some r -> ARCH_REG r
      | None -> SYMB_REG ("%" ^ name) }
| ';' { SEMI }
| ',' { COMMA }
| '+' { PLUS }
| '|' { PIPE }
| '(' { LPAR }
| ')' { RPAR }
| '[' { LBRK }
| ']' { RBRK }
| ':' { COLON }
| num as x
  { NUM (int_of_string x) }
| name as x
  { check_name x }
| eof { EOF }
| ""  { error "SPARC lexer" lexbuf }

{
let token lexbuf =
   let tok = token lexbuf in
   if O.debug then begin
     Printf.eprintf
       "%a: Lexed '%s'\n"
       Pos.pp_pos2
       (lexeme_start_p lexbuf,lexeme_end_p lexbuf)
       (lexeme lexbuf)
   end ;
   tok
end
}

