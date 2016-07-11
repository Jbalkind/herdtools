(*********************************************************************)
(*                        Herd                                       *)
(*                                                                   *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                   *)
(* Jade Alglave, University College London, UK.                      *)
(*                                                                   *)
(*  Copyright 2013 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

(*********)
(* Archs *)
(*********)

type t =
  | X86
  | PPC
  | SPARC
  | ARM
  | MIPS
  | AArch64
  | C
  | CPP

let tags = ["X86";"PPC";"SPARC";"ARM";"MIPS";"C";"AArch64"]

let parse s = match s with
| "X86" -> Some X86
| "PPC" -> Some PPC
| "SPARC" -> Some SPARC
| "ARM" -> Some ARM
| "MIPS" -> Some MIPS
| "C"   -> Some C
| "CPP"|"C++"   -> Some CPP
| "AArch64" -> Some AArch64
| _ -> None

let lex s = match parse s with
| Some a -> a
| None -> assert false


let pp a = match a with
| X86 -> "X86"
| PPC -> "PPC"
| SPARC -> "SPARC"
| ARM -> "ARM"
| MIPS -> "MIPS"
| AArch64 -> "AArch64"
| C -> "C"
| CPP -> "C++"

let arm = ARM
let ppc = PPC
let x86 = X86
let sparc = SPARC
let mips = MIPS
let aarch64 = AArch64

