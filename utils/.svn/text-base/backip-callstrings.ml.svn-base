(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  callstrings.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@gs3102.sp.cs.cmu.edu>
*
*  Started on  Tue Apr 24 13:42:26 2007 David Brumley
*  Last update Wed Jun 20 18:36:09 2007 David Brumley
*)
open Vine;;
open Vine_util;;
module List = ExtList.List;;

let usage = "callstrings [options]* outfile\n" in
let infile = ref "" in 
let csdotfile = ref "" in 
let chopdotfile = ref "" in 
let irchopfile = ref "" in 
let irfile = ref "" in
let start_chop_name = ref [] in 
let end_chop_addrs = ref [] in 
let root = ref "main" in 
let infile_set = ref false in 
let arg_name s = 
  infile := s; 
  infile_set := true 
in
let prepend reference arg =
  reference := arg :: !reference
in
let main argc argv = 
  (
    let speclist = Vine_tovine.speclist in 
    let myspeclist = [
    ("-chopstart", Arg.String(prepend start_chop_name),
    " <name> Add start chop function name (not address) for chop.");
    ("-chopend", Arg.String(prepend end_chop_addrs 
			    <@ Int64.of_string),
    " <addr> Add end address for chop.");
    ("-dot", Arg.Set_string(csdotfile), 
    " <file> cs dot output file.");
    ("-chopdot", Arg.Set_string(chopdotfile), 
    " <file> chop cs dot output file");
    ("-chopir", Arg.Set_string(irchopfile),
     " <file> chop ir output file");
    ("-ir", Arg.Set_string(irfile),
     " <file> IR output file");
    ("-root", Arg.Set_string(root),
     " <name> Set root of callstring (default is main)");
    ] in 
    let speclist = speclist @ myspeclist in 
    let () = Arg.parse speclist arg_name usage in 
    let flag_do_chop = 
      if List.length !end_chop_addrs > 0 then 
	true
      else 
	false 
    in 
    let (prog,funinfos) = Vine_tovine.to_program false  in 
    let prog = Vine_tovine.replace_calls_and_returns prog funinfos in
    let () = 
      if !irfile <> "" then
	Vine.pp_program (output_string (open_out !irfile)) prog
      else () 
    in 
    let () = 
      if (!csdotfile = "") then () else  (
	let g = Vine_callstring.mk_csg prog !root in 
	  Vine_callstring.output_dot  g (open_out !csdotfile )
      )
    in
      if flag_do_chop then (
	assert (List.length !start_chop_name = 1);
	
	let ()=Printf.printf "pm: before standard_multichop\n" in
	
	let chop = Vine_callstring.standard_multichop prog !root
	  (List.hd !start_chop_name) !end_chop_addrs 
	in
	
	let ()=Printf.printf "pm: after standard_multichop\n" in
	
	  if !chopdotfile <> "" then 
	    Vine_callstring.output_dot  chop (open_out !chopdotfile);
	  if !irchopfile <> "" then (
	    let prog = Vine_callstring.csg_to_program chop in 
	      Vine.pp_program (output_string (open_out !irchopfile)) prog;
	  ) else ()
      ) else ()
  )
in
main (Array.length Sys.argv) Sys.argv;;
