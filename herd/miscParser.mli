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

(* The basic types of architectures and semantics, just parsed *)

type maybev = SymbConstant.v

type reg = string (* Registers not yet parsed *)

type location =
  | Location_reg of int * reg
  | Location_sreg of string
  | Location_global of maybev
  | Location_reg_type of int * reg * string
  | Location_shared of int * maybev (*for GPU shared memory initializations*)

val location_compare : location -> location -> int
val dump_location : location -> string
val dump_rval : location -> string
val is_global : location -> bool
val as_local_proc : int -> location -> reg option

module LocSet : MySet.S with type elt = location


type prop = (location, maybev) ConstrGen.prop
type constr = prop ConstrGen.constr
type quantifier = ConstrGen.kind

type atom = location * maybev
type state = atom list
type outcome = atom list

val pp_atom : atom -> string
val pp_outcome : outcome -> string

type run_type = Ty of string | Pointer of string

(*********************************)
(* GPU memory map and scope tree *)
(*********************************)

type gpu_memory_space = 
| Global
| Shared

type thread      = int
type warp        = thread list
type cta         = warp list
type kernel      = cta list
type device      = kernel list

type scope_tree = 
| Scope_tree of device list
| No_scope_tree

type mem_space_map = 
| Mem_space_map of (string * gpu_memory_space) list
| No_mem_space_map

val pp_scope_tree : scope_tree -> string
val pp_memory_space_map : mem_space_map -> string
val cpu_scope_tree : int -> scope_tree

(* Packed result *)
type info = (string * string) list
type ('i, 'p, 'c, 'loc) result =
    { info : info ;
      init : 'i ;
      prog : 'p ;
      condition : 'c ;
      locations : ('loc * run_type) list ;
      scope_tree : scope_tree ;
      mem_space_map : mem_space_map ;
}

(* Easier to handle *)
type ('loc,'v,'ins) r3 =
      (('loc * 'v) list,
       (int * 'ins list) list,
       ('loc, 'v) ConstrGen.prop ConstrGen.constr,
       'loc) result

type ('loc,'v,'code) r4 =
      (('loc * 'v) list,
       'code list,
       ('loc, 'v) ConstrGen.prop ConstrGen.constr,
       'loc) result

(* Result of generic parsing *)
type 'pseudo t =
    (state, (int * 'pseudo list) list, constr, location) result


(* Extract hash *)
val get_hash :  ('i, 'p, 'c, 'loc) result -> string