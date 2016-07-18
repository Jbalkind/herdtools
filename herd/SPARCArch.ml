(*********************************************************************)
(*                        herd                                      *)
(*                                                                   *)
(*               Luc Maranget, INRIA Paris-Rocquencourt, France.     *)
(*                                                                   *)
(*  Copyright 2014 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

(** Define SPARC architecture *)

module Make (C:Arch.Config) (V:Value.S) =
  struct
    include SPARCBase

    let arch_sets = ["MEMBAR",(function StoreLoad -> true);]

    let is_isync _ = false
    let pp_isync = "???"

    module V = V

    include ArchExtra.Make(C)
	(struct
	  module V = V 

	  type arch_reg = reg
	  let pp_reg = pp_reg
	  let fmt_pp_reg = fmt_pp_reg
	  let reg_compare = reg_compare

	  type arch_instruction = instruction
	end)
	  
  end
