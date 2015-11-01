(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  callgraph.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@gs3102.sp.cs.cmu.edu>
*
*  Started on  Tue Apr 24 13:42:26 2007 David Brumley
*  Last update Wed Jun 20 18:35:59 2007 David Brumley
*)
open Vine;;
open Vine_util;;
open ExtList;;

let usage = "Generate a callgraph for a program"
and infile = ref ""
and irfile = ref ""
and cgdotfile = ref ""
and indirect_label = ref None


let speclist =
  ("-dot", Arg.Set_string(cgdotfile), 
   "<file> cg dot output file.")
  ::("-ir", Arg.Set_string(irfile),
     "<file> IR output file")
  ::("-indirect", Arg.String(fun s -> indirect_label := Some s),
     "<label> optional label to use for indirect calls")
  ::Vine_tovine.speclist
;;

let arg_name _ = 
    raise(Arg.Bad "No anonymous arguments are supported.")
in
let () = Arg.parse speclist arg_name usage in 
let (prog,funinfos) = Vine_tovine.to_program false in 
let prog = Vine_tovine.replace_calls_and_returns prog funinfos in
  if !irfile <> "" then
	Vine.pp_program (output_string (open_out !irfile)) prog;
  if !cgdotfile <> "" then
    let g = Vine_callgraph.mk_cg ?indirect_label: !indirect_label prog in 
      Vine_callgraph.output_dot (open_out !cgdotfile ) g



