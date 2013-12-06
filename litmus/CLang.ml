(*********************************************************************)
(*                          Litmus                                   *)
(*                                                                   *)
(*     Jacques-Pascal Deplaix, INRIA Paris-Rocquencourt, France.     *)
(*                                                                   *)
(*  Copyright 2010 Institut National de Recherche en Informatique et *)
(*  en Automatique and the authors. All rights reserved.             *)
(*  This file is distributed  under the terms of the Lesser GNU      *)
(*  General Public License.                                          *)
(*********************************************************************)

module Make(Tmpl:Template.S) = struct

  let dump chan indent env proc t =
    let out x = Printf.fprintf chan x in
    out "%s{\n" indent;
    begin
      let indent = "  " ^ indent in
      let dump_input x =
        let ty = Tmpl.Reexport.dump_type env x in
        let x = Tmpl.fmt_reg x in
        out "%s%s* %s = _a->%s;\n" indent ty x x
      in
      let dump_output x =
        let outname = Tmpl.Reexport.compile_out_reg proc x in
        out "%s%s = %s;\n" indent outname (Tmpl.fmt_reg x)
      in
      let dump_ins x =
        List.iter dump_input x.Tmpl.inputs;
        out "%s" (Tmpl.Reexport.to_string x);
        List.iter dump_output x.Tmpl.outputs
      in
      let trashed = Tmpl.Reexport.trashed_regs t in
      Tmpl.Reexport.before_dump chan indent env proc t trashed;
      List.iter dump_ins t.Tmpl.code;
      Tmpl.after_dump chan indent proc t
    end;
    out "%s}\n" indent

end
