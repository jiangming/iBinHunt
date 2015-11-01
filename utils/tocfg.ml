(*
 Owned and copyright BinAnalyse, 2009. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  tocfg.ml
*
*  Made by (Ming Jiang)
*  Login   <jiangming@smu.edu.sg>
*
*  Started on  Sun Man 10 13:42:26 2009 Ming Jiang
*)
open Vine;;
open Vine_util;;
open ExtList;;

let usage = "Generate a control flow graph for a elf file or ida db file with file id"
and infile = ref ""
and irfile = ref ""
and cfgdotfile = ref ""

let write_cfg cfg os =
  Vine_graphviz.VineStmtsDot.output_graph os cfg
	
let speclist =
  ("-dot", Arg.Set_string(cfgdotfile), 
   "<file> cfg dot output file.")
  ::("-ir", Arg.Set_string(irfile),
     "<file> IR output file")
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
  if !cfgdotfile <> "" then
    let cfg = Vine_cfg.prog_to_cfg prog in
       write_cfg cfg (open_out !cfgdotfile ) 



