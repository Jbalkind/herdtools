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

module Make(S : SemExtra.S) = struct

  module S = S
  module E = S.E
  module A = S.A
  module V = A.V
  module C = S.C
  module PC = S.O.PC

(*************)	    
(* Utilities *)
(*************)	    

  let iico es =
    E.EventRel.union
      es.E.intra_causality_data
      es.E.intra_causality_control

  let po_strict es =
    E.EventRel.of_pred
      es.E.events es.E.events E.po_strict

  let po_iico_data es =
    E.EventRel.union
      es.E.intra_causality_data
      (po_strict es)

  let po_iico es =  E.EventRel.union (iico es) (po_strict es)

(* slight extension of prog order *)
  let is_before_strict es e1 e2 =
    E.EventRel.mem (e1,e2) es.E.intra_causality_data  ||
    E.EventRel.mem (e1,e2) es.E.intra_causality_control ||
    E.po_strict e1 e2

  let get_loc e =  match E.location_of e with
  | Some loc -> loc
  | None -> assert false

(* Lift dependance relation to memory *)
  let restrict p = E.EventRel.filter (fun (e1,e2) -> p e1 && p e2)

  let trans_close_mem r = restrict E.is_mem (S.tr r)
  let trans_close_mems r_p = List.map trans_close_mem r_p

(******************)
(* View of a proc *)
(******************)

  let proc_view_event p e =
    E.proc_of e = p || E.is_mem_store e

  let proc_view_event2 p (e1,e2) =
    proc_view_event p e1 && proc_view_event p e2

  let proc_view p vb = E.EventRel.filter (proc_view_event2 p) vb

(* Perform difference, columnwise, ie difference of projected relations *)
  let diff_p = List.map2 E.EventRel.diff

(* Perform union, columnwise, ie union of projected relations *)
  let union_p = List.map2 E.EventRel.union

  let unions_p rows =
    let cols =
      try Misc.transpose rows
      with Misc.TransposeFailure -> assert false in
    List.map E.EventRel.unions cols

  let transitive_closure_p = List.map E.EventRel.transitive_closure

(* Convert the ordered list representation of a total order to a relation *)
  let rec order_to_pairs k evts = match evts with
  | [] -> k
  | e1 :: tl ->      
      let k = List.fold_left (fun k e2 -> (e1,e2)::k) k tl in
      order_to_pairs k tl
	
  let order_to_rel evts = E.EventRel.of_list (order_to_pairs []  evts)

(* The same, for successor relation,
   which is enough for feeding topological orders generators *)

  let rec order_to_succ_rel evts = match evts with
  | []|[_] -> E.EventRel.empty
  | e1::(e2::_ as evts) ->
      E.EventRel.add (e1,e2) (order_to_succ_rel evts)


(********)
(* Misc *)
(********)

  let get_dir e = match e.E.action with
  | E.Access (d,_,_) -> d
  | _ -> assert false


  let find_source rfmap r =
    try S.RFMap.find  (S.Load r) rfmap
    with Not_found -> assert false

(*******************)
(* RF/FR relations *)
(*******************)

  let make_rf_from_rfmap rfmap =
    S.RFMap.fold
      (fun wt rf k -> match wt,rf with
      | S.Load er,S.Store ew when E.is_mem er ->
          E.EventRel.add (ew,er) k
      | _ -> k)
     rfmap 
      E.EventRel.empty

  let make_rf conc = make_rf_from_rfmap conc.S.rfmap 


  let find_rf er rfm =
    try S.RFMap.find (S.Load er) rfm
    with Not_found -> assert false

  let make_fr conc ws =
    let loads = E.mem_loads_of conc.S.str.E.events
    and stores = E.mem_stores_of conc.S.str.E.events in
    E.EventSet.fold
      (fun er k ->
        let erf = find_rf er conc.S.rfmap in
        E.EventSet.fold
          (fun ew k ->
            if E.same_location ew er then match erf with
            | S.Init ->
                E.EventRel.add (er,ew) k
            | S.Store erf ->
                if E.EventRel.mem (erf,ew) ws then
                  E.EventRel.add (er,ew) k
                else k
            else k)
          stores k)
      loads E.EventRel.empty

   let make_rf_regs conc =
      S.RFMap.fold
      (fun wt rf k -> match wt,rf with
      | S.Load er,S.Store ew when E.is_reg_any er ->
          E.EventRel.add (ew,er) k
      | _ -> k)
      conc.S.rfmap 
      E.EventRel.empty

  let rext conc e =
    E.is_mem_load e &&
    (match find_rf e conc.S.rfmap with
    | S.Init -> true
    | S.Store ew -> E.proc_of ew <> E.proc_of e)


  let same_source conc e1 e2 = 
   match find_rf e1 conc.S.rfmap,find_rf e2 conc.S.rfmap with
    | S.Init,S.Init -> true
    | S.Store w1,S.Store w2 -> E.event_compare w1 w2 = 0
    | S.Init,S.Store _
    | S.Store _,S.Init -> false

  let ext r = E.EventRel.filter (fun (e1,e2) -> not (E.same_proc e1 e2)) r
  let internal r = E.EventRel.filter (fun (e1,e2) -> E.same_proc e1 e2) r
      

(* po-separation *)
  let sep is_sep is_applicable evts =
  let is_applicable e1 e2 = is_applicable (e1,e2) in
  let rels =
  E.EventSet.fold
    (fun e k ->
      if is_sep e then
        let before =
          E.EventSet.filter
            (fun ea -> E.po_strict ea e)
            evts
        and after =
          E.EventSet.filter
            (fun eb ->  E.po_strict e eb)
            evts in
	E.EventRel.of_pred before after is_applicable::k
      else k)
    evts [] in
  E.EventRel.unions rels

(* Extract external sub-relation *)

let extract_external r =
  E.EventRel.filter (fun (e1,e2) -> E.proc_of e1 <> E.proc_of e2) r

(**************************************)
(* Place loads in write_serialization *)
(**************************************)
(* Use rfmap to order loads and stores as much as possible *)

(* ws is write serialization *)
  let find_rf er rfm =
    try S.RFMap.find (S.Load er) rfm
    with Not_found -> assert false

  let first_ws ws ew = E.EventSet.is_empty (E.EventRel.preds ew ws)

  let make_load_stores conc ws =
    let loads = E.mem_loads_of conc.S.str.E.events
    and stores = E.mem_stores_of conc.S.str.E.events in
    E.EventSet.fold
      (fun er k ->
        let erf = find_rf er conc.S.rfmap in
        E.EventSet.fold
          (fun ew k ->
            if E.same_location ew er then match erf with
            | S.Init ->
                if first_ws  ew ws then
                  E.EventRel.add (er,ew) k
                else k                
            | S.Store erf ->
                if E.EventRel.mem (erf,ew) ws then
                  E.EventRel.add (er,ew) k
(*              else if E.EventRel.mem (ew,erf) ws then
                E.EventRel.add (ew,er) k
 *)
                else k
            else k)
          stores k)
      loads E.EventRel.empty


(******************************)
(* Sets and Maps on locations *)
(******************************)

  module LocSet =
    MySet.Make
      (struct
	type t = A.global_loc
	let compare = A.V.compare
      end)


  module LocEnv =
    Map.Make
      (struct
	type t = A.location
	let compare = A.location_compare
      end)

(* Collect various events by their location *)

  let map_loc_find loc m =
    try LocEnv.find loc m
    with Not_found -> []

  let collect_by_loc es pred =
    E.EventSet.fold
      (fun e k ->
        if pred e then
          let loc = get_loc e in
          let evts = map_loc_find loc k in
          LocEnv.add loc (e::evts) k
        else k)
      es.E.events LocEnv.empty

  let collect_reg_loads es = collect_by_loc es E.is_reg_load_any
  and collect_reg_stores es = collect_by_loc es E.is_reg_store_any
  and collect_mem_loads es = collect_by_loc es E.is_mem_load
  and collect_mem_stores es = collect_by_loc es E.is_mem_store
  and collect_loads es = collect_by_loc es E.is_load
  and collect_stores es = collect_by_loc es E.is_store
  and collect_atomics es = collect_by_loc es E.is_atomic
      
(*************)
(* Atomicity *)
(*************)


(* Event atomicity class are canonized as
   a mapping from one representant to the class *)
  module Canon = Map.Make(E.OrderedEvent)

  let find_class e map =
    try Canon.find e map with Not_found -> assert false

  let canonical_locked_events_of es =
    E.Atomicity.fold
      (fun evts k ->
	let canon =
	  (* An atomicity class is not empty *)
	  try E.EventSet.choose evts with Not_found -> assert false in
	Canon.add canon evts k)
      es.E.atomicity Canon.empty
      

  let get_canonical_locked_events_of es =
    let lockeds = canonical_locked_events_of es in
    Canon.fold
      (fun e _ k -> E.EventSet.add e k)
      lockeds E.EventSet.empty 

  let get_atomicity_candidates vb es =
(* Canonize *)
    let lockeds = canonical_locked_events_of es in
    let reprs =
      Canon.fold
        (fun e _ k -> E.EventSet.add e k)
        lockeds E.EventSet.empty in
    let filtered_vb =
      E.EventRel.filter
        (fun (e1,e2) -> E.EventSet.mem e1 reprs && E.EventSet.mem e2 reprs)
        vb in
(* Generate orderings, over representants *)
    let perms = E.EventRel.all_topos (PC.verbose > 0) reprs filtered_vb in
    let cands =
(* For every candidate ordering *)
      List.rev_map (* why not be tail-recursive ? *)
        (fun perm ->
	  (* Change into relation *)
	  let canon_cand = order_to_rel perm in
	  (* And lift relation to atomicity classes,
             maybe not the most efficient way... *)
	  let cand =
	    E.EventRel.fold
	      (fun (c1,c2) k ->
	        let atom1 = find_class c1 lockeds
	        and atom2 = find_class c2 lockeds in
	        E.EventRel.union (E.EventRel.cartesian atom1 atom2) k)
	      canon_cand E.EventRel.empty in
	  canon_cand,cand)
        perms in
    reprs,cands

(********************************************)
(* Write serialization candidate generator. *)
(********************************************)


  let restrict_to_mem_stores rel =
    E.EventRel.filter
      (fun (e1,e2) -> E.is_mem_store e1 && E.is_mem_store e2)
      rel

  let fold_write_serialization_candidates conc vb kont res =
    let vb =
      E.EventRel.union vb
        (restrict_to_mem_stores conc.S.last_store_vbf) in
(* Because final state is fixed *)
    let stores_by_loc = collect_mem_stores conc.S.str in
    let orders =
      LocEnv.fold
	(fun _loc stores k ->
          let orders =
	    E.EventRel.all_topos (PC.verbose > 0)
              (E.EventSet.of_list stores) vb in
          List.map order_to_succ_rel orders::k)
        stores_by_loc [] in
    Misc.fold_cross_gen E.EventRel.union E.EventRel.empty
      orders kont res

(* With check *)
  let apply_process_co test conc process_co res =
     try
       fold_write_serialization_candidates
         conc conc.S.pco process_co res
     with E.EventRel.Cyclic ->
       if S.O.debug.Debug.barrier && S.O.PC.verbose > 2 then begin
         let module PP = Pretty.Make(S) in
           let legend =
             sprintf "%s cyclic co precursor"
               test.Test.name.Name.name in
           let pos = conc.S.pos in
           prerr_endline legend ;
           PP.show_legend test  legend conc
             [ ("pos",S.rt pos); ("pco",S.rt conc.S.pco)]
        end ;
        res
(*******************************************************)
(* Saturate all memory accesses wrt atomicity classes  *)
(*******************************************************)
  exception FailFast

  let fold_saturated_mem_order es mem_order kont res =

    (* Inputs : es : E.event_structure
       mem_order : possibly unsaturated memory order
       Action: fold over all possibilities of saturating edges 
     *)
    let accesses = E.mem_of es.E.events in
    let is_before e atom = 
      E.EventSet.exists 
	(fun elock -> E.EventRel.mem (e, elock) mem_order)
	atom in
    let is_after e atom = 
      E.EventSet.exists 
	(fun elock -> E.EventRel.mem (elock, e) mem_order)
	atom in
    let add_before e atom =
      E.EventSet.fold
	(fun elock k -> if E.is_mem elock then E.EventRel.add (e, elock) k else k)
	atom E.EventRel.empty in
    let add_after e atom =
      E.EventSet.fold
	(fun elock k -> if E.is_mem elock then E.EventRel.add (elock, e) k else k)
	atom E.EventRel.empty in
    try 
      let (new_order,unresolved) = 
	E.EventSet.fold
	  (fun e (new_ord,unresolved) ->
	    E.Atomicity.fold
	      (fun atom (new_ord,unresolved) ->
		if E.EventSet.mem e atom 
		then (new_ord,unresolved)
		else 
		  let should_add_before = is_before e atom in
		  let should_add_after = is_after e atom in
		  match (should_add_before, should_add_after) with
		  | true,true -> raise FailFast
		  | true, false -> (E.EventRel.union new_ord (add_before e atom),
				    unresolved)
		  | false, true -> (E.EventRel.union new_ord (add_after e atom),
				    unresolved)
		  | false, false -> (new_ord,
				     (e,atom)::unresolved)
	      )
	      es.E.atomicity (new_ord,unresolved)
	  )
	  accesses (E.EventRel.empty, [])
      in
      let resolved : E.EventRel.t list list = 
	List.map 
	  (fun (e,atom) -> 
	    [
	     add_before e atom;
	     add_after e atom]
	  )
	  unresolved in
      Misc.fold_cross_gen E.EventRel.union new_order resolved kont res
    with
      FailFast -> res
          

(*****************************************)
(* Compute write serialization precursor *)
(*****************************************)

  let compute_pco rfmap ppoloc =
    try
      let pco = 
        if S.O.optace then
          E.EventRel.fold
            (fun (e1,e2 as p) k -> match get_dir e1, get_dir e2 with
            | E.W,E.W -> E.EventRel.add p k
            | E.R,E.R ->
                begin match
                  find_source rfmap e1,
                  find_source rfmap e2
                with
                | S.Store w1,S.Store w2 ->
                    if E.event_equal w1 w2 then k
                    else E.EventRel.add (w1,w2) k
                | S.Init,_ -> k
                | _,S.Init -> raise Exit
                end
            | E.R,E.W ->
                begin match
                  find_source rfmap e1
                with
                | S.Store w1 -> E.EventRel.add (w1,e2) k
                | S.Init -> k
                end
            | E.W,E.R ->
                begin match
                  find_source rfmap e2
                with
                | S.Store w2 ->
                    if E.event_equal e1 w2 then k
                    else E.EventRel.add (e1,w2) k
                | S.Init -> raise Exit
                end)
            ppoloc
            E.EventRel.empty
        else
          E.EventRel.filter
            (fun (e1,e2) -> E.is_store e1 && E.is_store e2)
            ppoloc in
      Some pco
    with Exit -> None

(*************************************)
(* Final condition invalidation mode *)
(*************************************)

(*
  A little optimisation: we check whether the existence/non-existence
  of some vo would help in validation/invalidating the constraint
  of the test.

  If no, not need to go on
 *)

  module T = Test.Make(S.A)
      
  let final_is_relevant test fsc =
    let open ConstrGen in
    let cnstr = T.find_our_constraint test in
    match cnstr with
    (* Looking for 'Allow' witness *)
    | ExistsState p ->  C.check_prop p fsc
    (* Looking for witness that invalidates 'Require' *)
    | ForallStates p -> not (C.check_prop p fsc)
    (* Looking for witness that invalidates 'Forbid' *)
    | NotExistsState p -> C.check_prop p fsc


end
