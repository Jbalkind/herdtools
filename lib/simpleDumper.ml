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

(*****************)
(* Parsable dump *)
(*****************)
module type I = sig
  module A : ArchBase.S

  type state
  val dump_state :state -> string

  type constr
  val dump_constr : constr -> string

  type location
  val dump_location : location -> string
end

module Make(I:I) : sig
  val dump : out_channel ->
    Name.t ->
    (I.state, (int * I.A.pseudo list) list, I.constr, I.location)
        MiscParser.result
      -> unit
  val dump_info : out_channel ->
    Name.t ->
    (I.state, (int * I.A.pseudo list) list, I.constr, I.location)
        MiscParser.result
      -> unit
  val lines :
      Name.t ->
        (I.state, (int * I.A.pseudo list) list, I.constr, I.location)
          MiscParser.result
      -> string list
end = struct    
  open Printf
  open I

  let rec fmt_io io = match io with
  | A.Nop -> ""
  | A.Instruction ins -> A.dump_instruction ins
  | A.Label (lbl,io) -> lbl ^ ": " ^ fmt_io io
  | A.Macro (f,regs) ->
      sprintf
        "%s(%s)"
        f
        (String.concat "," (List.map A.pp_reg regs))

  let fmt_col (p,is) = sprintf "P%i" p::List.map fmt_io is

  let prog chan prog =
    let pp = List.map fmt_col prog in
    Misc.pp_prog chan pp
(*
    dump_procs chan prog ;
    iter_prog (dump_ios chan)
      (List.map snd prog)
*)
  open MiscParser

  let do_dump withinfo chan doc t =
    fprintf chan "%s %s\n" (Archs.pp A.arch) doc.Name.name ;
    if withinfo then begin
      List.iter
        (fun (k,i) -> fprintf chan "%s=%s\n" k i)
        t.info
    end ;
    begin match doc.Name.doc with
    | "" -> ()
    | doc -> fprintf chan "\"%s\"\n" doc
    end ;
    fprintf chan "\n{%s}\n\n" (dump_state  t.init) ;
    prog chan t.prog ;
    fprintf chan "\n" ;
    begin match t.locations with
    | [] -> ()
    | locs ->
        fprintf chan "locations [" ;
        List.iter
          (fun (loc,t) -> match t with
          | MiscParser.I -> fprintf chan "%s; " (I.dump_location loc)
          | MiscParser.P -> fprintf chan "%s*; "(I.dump_location loc))
          locs ;
        fprintf chan "]\n"
    end ;
    fprintf chan "%s\n" (I.dump_constr t.condition) ;
    ()

  let dump = do_dump false
  let dump_info = do_dump true

  let (@@) f k = f k

  let lines doc t =
    begin fun k -> sprintf "%s %s" (Archs.pp A.arch) doc.Name.name :: k
    end @@
    begin fun k -> match doc.Name.doc with
    | "" -> k
    | doc -> sprintf "\"%s\"" doc :: k
    end @@
    begin fun k ->  sprintf "{%s}" (dump_state  t.init) :: k
    end @@
    begin
      fun k -> 
      let pp = List.map fmt_col t.prog in
      let pp = Misc.lines_of_prog pp in
      let pp = List.map (sprintf "%s;") pp in
      pp @ ""::k
    end @@
    begin fun k ->
      match t.locations with
      | [] -> k
      | locs ->
        sprintf "locations [%s]"
            (String.concat " "
               (List.map
                  (fun (loc,t) -> match t with
                  | MiscParser.I -> sprintf "%s; " (I.dump_location loc)
                  | MiscParser.P -> sprintf "%s*; "(I.dump_location loc))
                  locs))::k
    end @@
    [I.dump_constr t.condition]    
end