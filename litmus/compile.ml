(*********************************************************************)
(*                          Litmus                                   *)
(*                                                                   *)
(*        Luc Maranget, INRIA Paris-Rocquencourt, France.            *)
(*        Susmit Sarkar, University of Cambridge, UK.                *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

module type Config = sig
  val numeric_labels : bool
  val signaling : bool
  val timeloop : int
  val barrier : Barrier.t
end

let get_fmt hexa = function
  | "int" ->  if hexa then "x" else "i"
  | t -> Warn.fatal "No format for type '%s'" t

let base =  CType.Base "int"

module Generic (A : Arch.Base) = struct
  open CType

  let base =  base
  let pointer = Pointer base

  let typeof = function
    | Constant.Concrete _ -> base
    | Constant.Symbolic _ -> pointer

  let type_in_final p reg final flocs =
    Misc.proj_opt
      base
      (ConstrGen.fold_constr
         (fun a t ->
            let open ConstrGen in
            match a with
            | LV (A.Location_reg (q,r),v) when p=q && A.reg_compare reg r = 0 ->
                begin match typeof v,t with
                | (Base s1, Some (Base s2))
                | (Pointer (Base s1), Some (Pointer (Base s2)))
                  when Misc.string_eq s1 s2 ->
                    t
                | (ty, None) -> Some ty
                | (loc_ty, Some cond_ty) ->
                    Warn.fatal
                      "Type missmatch between the locations \
                       (type: %s) and the final condition (type: %s)"
                      (CType.dump loc_ty)
                      (CType.dump cond_ty)
                end
            | _ -> t)
         final
         (List.fold_right
            (fun (loc,t) k -> match loc with
               | A.Location_reg (q,r) when p=q && A.reg_compare reg r = 0 ->
                   begin match t with
                   | MiscParser.Ty s -> Some (Base s)
                   | MiscParser.Pointer s -> Some (Pointer (Base s))
                   end
               | _ -> k)
            flocs
            None)
      )

    let add_addr_type a ty env =
(*      Printf.eprintf "Type %s : %s\n"  a (CType.dump ty) ;  *)
      try
        let tz = StringMap.find a env in
        match ty,tz with
        | (Pointer (Base s1), Pointer (Base s2))
        | (Base s1, Base s2) when Misc.string_eq s1 s2 -> env
(* All default cases expressed,
   will produce a warning if t is extended *)
        | _,_ (* (Pointer _|Base _),(Pointer _|Base _) *) ->
            Warn.fatal
              "Type missmatch detected on location %s, required %s vs. found %s"
              a (dump ty) (dump tz)
      with
        Not_found -> StringMap.add a ty env

    let add_value v env = match v with
    | Constant.Concrete _ -> env
    | Constant.Symbolic a -> add_addr_type a base env
end

module Make
    (O:Config)
    (A:Arch.S)
    (T:Test.S with
     type A.reg = A.reg and
     type A.location = A.location and
     module A.LocSet = A.LocSet and
     type A.Out.t = A.Out.t and
     type P.code = int * A.pseudo list)
    (C:XXXCompile.S with module A = A) =
  struct
    open Printf
    open Constant

    module A = A
    module V = A.V
    module Constr = T.C
    module Generic = Generic(A)
    open A.Out

    let rec extract_pseudo ins = match ins with
    | A.Nop -> StringSet.empty
    | A.Label (_,ins) -> extract_pseudo ins
    | A.Instruction ins -> C.extract_addrs ins
    | A.Macro (_,_) -> assert false


    let extract_addrs code =
      List.fold_right
        (fun ins env ->
          StringSet.union (extract_pseudo ins) env)
        code
        StringSet.empty


(*******************************)
(* Assoc label -> small number *)
(*******************************)



let rec lblmap_pseudo c m i = match i with
| A.Nop|A.Instruction _ -> c,m
| A.Label(lbl,i) ->
    let m = StringMap.add lbl c m in
    lblmap_pseudo (c+1) m i
| A.Macro _ -> assert false

let lblmap_code =
  let rec do_rec c m = function
    | [] -> m
    | i::code ->
        let c,m = lblmap_pseudo c m i in
        do_rec c m code in
  do_rec 0 StringMap.empty



(****************)
(* Compile code *)
(****************)

    open ConstrGen
    exception CannotIntern

    let tr_label_fail m lbl =  sprintf "%i" (StringMap.find lbl m)

    let tr_label m lbl =
      try
        tr_label_fail m lbl
      with
      | Not_found -> lbl

    let emit_label m lbl =
      { empty_ins with
        memo=sprintf "%s:" (A.Out.dump_label (tr_label m lbl)) ;
        label = Some lbl ; branch=[Next] ; }

    let as_int = function
      | Concrete i -> i
      | Symbolic _ -> raise CannotIntern

    let rec tr_cond p = function
      | Atom (LV (A.Location_reg (q,r),v)) when p = q ->
          let i = as_int v in
          Atom (LV (r,i))
      | Atom _ -> raise CannotIntern
      | And cs -> And (List.map (tr_cond p) cs)
      | Or _ | Implies _ | Not _ -> raise CannotIntern

    let rec compile_cond c labf kt = match c with
      | Atom (LV (r,i)) -> C.branch_neq r i labf kt
      | Atom _ -> assert false
      | And [] -> kt
      | And (c::cs) ->
          compile_cond c labf (compile_cond (And cs) labf kt)
      | _ -> raise CannotIntern

    let compile_pseudo_code code k =
      let m =
        if O.numeric_labels then lblmap_code code
        else StringMap.empty in

      let tr_lab seen lbl =
        try
          let x = tr_label_fail m lbl in
          (if StringSet.mem lbl seen then sprintf "%sb" else sprintf "%sf") x
        with Not_found -> lbl in

      let rec compile_pseudo seen ins = match ins with
      | A.Nop -> seen,[]
      | A.Label (lbl,ins) ->
          let seen = StringSet.add lbl seen in
          let ilab = emit_label m lbl in
          let seen,k = compile_pseudo seen ins  in
          seen,ilab::k
      | A.Instruction ins ->
          seen,C.compile_ins (tr_lab seen) ins []
      | A.Macro (_,_) -> assert false in

      let rec do_rec seen = function
        | [] -> k
        | ins::code ->
            let seen,ins = compile_pseudo seen ins in
            let k = do_rec seen code in
            ins @ k in
      do_rec StringSet.empty code



    let compile_cond p final =
      try
        let c = tr_cond p (ConstrGen.prop_of final) in
        let lab = Label.next_label "C" in
        let k = C.signaling_write 1 [emit_label StringMap.empty lab] in
        compile_cond c lab k,true
      with
      CannotIntern -> [],false

    let compile_code proc code final =
      let k,cond =
        if O.signaling then
          compile_cond proc final
        else [],false in

      let code = compile_pseudo_code code k in

      let code =
        if O.timeloop > 0 then C.emit_loop code
        else code in

      let code = match O.barrier with
      | Barrier.TimeBase -> (* C.emit_tb_wait *) code
      | _ -> code  in

      code,cond


    module RegSet =
      MySet.Make
        (struct
          type t = A.reg
          let compare = A.reg_compare
        end)

    let pp_reg_set chan rs =
      RegSet.pp chan ","
        (fun chan r -> fprintf chan "%s" (A.pp_reg r))
        rs

    module LabEnv =
      Map.Make
        (struct
          type t = string
          let compare = String.compare
        end)

(* Compute the set of registers that are to be inititialized
   by real code. This is standard live-in calculation *)

(* One instruction *)
    let live_in_ins ins (env,live_in_next) =
      let live_out =
        List.fold_left
          (fun k flow ->
            let rs =  match flow with
            | Next -> live_in_next
            | Branch lbl ->
                try LabEnv.find lbl env
                with Not_found -> RegSet.empty in
            RegSet.union rs k)
          RegSet.empty ins.branch in
      let live_in =
        RegSet.union
          (RegSet.of_list ins.inputs)
          (RegSet.diff live_out
(* Conditional instruction, a la ARM *)
             (if ins.cond then RegSet.empty
               else RegSet.of_list ins.outputs)) in
      (match ins.label with
      | None -> env
      | Some lbl -> LabEnv.add lbl live_in env),
      live_in

(* One sequence of instruction *)
    let live_in_code code env live_in_final =
      List.fold_right live_in_ins code (env,live_in_final)

(* Fixpoint *)
    let comp_fix code live_in_final =
(*
      eprintf "FINAL: {%a}\n" pp_reg_set live_in_final ;
*)
      let rec do_rec env0 =
        let env,r = live_in_code code env0 live_in_final in
(*
        eprintf "FIX: {%a}\n" pp_reg_set r ;
*)
        let c =
          LabEnv.compare RegSet.compare env env0 in
        if c = 0 then r
        else do_rec env in
      do_rec LabEnv.empty

    let comp_initset code inputs_final =
      RegSet.elements (comp_fix code inputs_final)

    let compile_init proc init code flocs final =
      let locs1 = Constr.locations final
      and locs2 = A.LocSet.of_list flocs in
      let locs = A.LocSet.union locs1 locs2 in
      let inputs_final =
        A.LocSet.fold
          (fun loc k -> match loc with
          | A.Location_reg (p,reg) when p = proc -> RegSet.add reg k
          | _ -> k)
          locs RegSet.empty in
      let inputs = comp_initset code inputs_final in
      List.map
        (fun reg ->
          let v = A.find_in_state (A.Location_reg (proc,reg)) init in
          reg,v)
        inputs

    let load_addrs env =
      let lst =
        StringMap.fold
          (fun addr i k -> (i,addr)::k)
          env [] in
      List.sort
        (fun (x,_) (y,_) -> Misc.int_compare x y)
        lst

    let uniq xs ys = A.LocSet.elements (A.LocSet.of_list (xs@ys))

    let compile_final proc final flocs =
      let locs =
        A.LocSet.union
          (Constr.locations final)
          (A.LocSet.of_list flocs) in
      A.LocSet.fold
        (fun loc k -> match loc with
        | A.Location_reg (p,reg) when p=proc -> reg::k
        | _ -> k)
        locs []

    let mk_templates init code final flocs =
      let outs =
        List.map
          (fun (proc,code) ->
            let addrs = extract_addrs code in
            let code,cond = compile_code proc code final in
            proc,addrs,code,cond)
          code in
      let flocs = List.map fst flocs in
      let pecs = List.map (fun (p,e,c,_) -> p,e,c) outs
      and conds =
        List.fold_left (fun r (_,_,_,b) -> r || b)
          false outs in
      if O.signaling && not conds then
        Warn.fatal "could not signal write" ;
      List.map
        (fun (proc,addrs,code) ->
          proc,
          { init = compile_init proc init code flocs final ;
            addrs = StringSet.elements addrs ;
            final = compile_final proc final flocs;
            code = code; })
        pecs

    let comp_globals init code =
      let env =
        List.fold_right
          (fun (loc,v) env ->
            match loc with
            | A.Location_global a ->
(*                let env = Generic.add_value v env in *)
                Generic.add_addr_type a (Generic.typeof v) env
            | _ -> env)
          init StringMap.empty in
      let env =
        List.fold_right
          (fun (_,t) ->
            List.fold_right
              (fun a -> Generic.add_addr_type a base)
              t.addrs)
          code env in
(* Add uninitialised globals referenced as values in init,
   Those may be accessed by code *)
      let env =
         List.fold_right
          (fun (_,v) env ->
            match v with
            | Constant.Symbolic a ->
                begin try
                  let _ = StringMap.find a env in
                  env
                with Not_found  ->
                  StringMap.add a Generic.base env
                end
            | _ -> env)
          init env in
      StringMap.fold
        (fun a ty k -> (a,ty)::k)
        env []

    let type_out p t final flocs =
      List.map
        (fun reg -> reg,Generic.type_in_final p reg final flocs)
        t.final

    let type_outs code final flocs =
      List.map
        (fun (p,t) -> p,(t, (type_out p t final flocs, [])))
        code

    let compile t =
      let
          { MiscParser.init = init ;
            info = info;
            prog = code;
            condition = final;
            locations = locs ; _
          } = t in
      let code = mk_templates init code final locs in
      let code_typed = type_outs code final locs in
      { T.init = init;
        info = info;
        code = code_typed;
        condition = final;
        globals = comp_globals init code;
        flocs = List.map fst locs ;
        global_code = [];
        src = t;
      }

  end
