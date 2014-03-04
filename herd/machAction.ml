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


open Printf

module Make (A : Arch.S) : (Action.S with module A = A) = struct

  module A = A
  module V = A.V
  open Dir

  type action = 
    | Access of dirn * A.location * V.v * bool 
          (* atomicity flag *)
    | Barrier of A.barrier
    | Commit
  
  let mk_Access (d,l,v,ato) = Access (d,l,v,ato)
  let mk_Barrier b = Barrier b
  let mk_Commit = Commit

(* Local pp_location that adds [..] around global locations *)        
    let pp_location withparen loc =
      if withparen then sprintf "[%s]" (A.pp_location loc)
      else A.pp_location loc

  let pp_action withparen a = match a with
    | Access (W,l,v,ato) ->
	Printf.sprintf "%s%s%s=%s"
          (pp_dirn W)
          (pp_location withparen l)
	  (if ato then "*" else "")
	  (V.pp_v v)
    | Access (R,l,v,ato) ->
	Printf.sprintf "%s%s%s=%s"
          (pp_dirn R)
          (pp_location withparen l) 
          (if ato then "*" else "")
	  (V.pp_v v)
    | Barrier b      -> A.pp_barrier b
    | Commit -> "Commit"

(* Utility functions to pick out components *)
    let value_of a = match a with
    | Access (_,_ , v,_) -> Some v
    | _ -> None

    let location_of a = match a with
    | Access (_, l, _,_) -> Some l
    | _ -> None

    let location_reg_of a = match a with
    | Access (_,A.Location_reg (_,r),_,_) -> Some r
    | _ -> None

    let global_loc_of a = match a with
    | Access (_,A.Location_global loc,_,_) -> Some loc
    | _ -> None

    let location_compare a1 a2 = match location_of a1,location_of a2 with
    | Some loc1,Some loc2 -> 
	A.location_compare loc1 loc2
    | _,_ -> assert false

(* relative to memory *)
    let is_mem_store a = match a with
    | Access (W,A.Location_global _,_,_) -> true
    | _ -> false

    let is_mem_load a = match a with
    | Access (R,A.Location_global _,_,_) -> true
    | _ -> false

    let is_mem a = match a with
    | Access (_,A.Location_global _,_,_) -> true
    | _ -> false

    let is_atomic a = match a with
      | Access (_,_,_,true) -> 
	 assert (is_mem a); true
      | _ -> false

    let get_mem_dir a = match a with
    | Access (d,A.Location_global _,_,_) -> d
    | _ -> assert false

(* relative to the registers of the given proc *)
    let is_reg_store a (p:int) = match a with
    | Access (W,A.Location_reg (q,_),_,_) -> p = q
    | _ -> false

    let is_reg_load a (p:int) = match a with
    | Access (R,A.Location_reg (q,_),_,_) -> p = q
    | _ -> false

    let is_reg a (p:int) = match a with
    | Access (_,A.Location_reg (q,_),_,_) -> p = q
    | _ -> false


(* Store/Load anywhere *)
    let is_store a = match a with
    | Access (W,_,_,_) -> true
    | _ -> false

    let is_load a = match a with
    | Access (R,_,_,_) -> true
    | _ -> false

    let is_reg_any a = match a with
    | Access (_,A.Location_reg _,_,_) -> true
    | _ -> false

    let is_reg_store_any a = match a with
    | Access (W,A.Location_reg _,_,_) -> true
    | _ -> false

    let is_reg_load_any a = match a with
    | Access (R,A.Location_reg _,_,_) -> true
    | _ -> false

(* Barriers *)
    let is_barrier a = match a with
    | Barrier _ -> true
    | _ -> false

    let barrier_of a = match a with
    | Barrier b -> Some b
    | _ -> None

(* Commits *)
   let is_commit a = match a with
   | Commit -> true
   | _ -> false

(* Equations *)

    let undetermined_vars_in_action a =
      match a with
      | Access (_,l,v,_) -> 
	  let undet_loc = match A.undetermined_vars_in_loc l with
	  | None -> V.ValueSet.empty
	  | Some v -> V.ValueSet.singleton v in
	  if V.is_var_determined v then undet_loc
	  else V.ValueSet.add v undet_loc
      | Barrier _|Commit -> V.ValueSet.empty

    let simplify_vars_in_action soln a =
      match a with
      | Access (d,l,v,ato) -> 
	 let l' = A.simplify_vars_in_loc soln l in
	 let v' = V.simplify_var soln v in
	 Access (d,l',v',ato)
      | Barrier _ | Commit -> a

(*************************************************************)	      
(* Add together event structures from different instructions *)
(*************************************************************)	 

    let make_action_atomic a = match a with
      | Access (d,l,v,_) -> Access (d,l,v,true)
      | _ -> a

end
