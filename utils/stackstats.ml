(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(* 
 Author: Prateek Saxena
*)

open Vine;;
open Vine_util;;
open Vine_dataflow;;

module List = ExtList.List;;

let func_to_analyze = ref [] in

let print_stack_analysis_stats = function
    Function(a,b,c,d, Some(_)) as f ->
      let to_do = ref false in
      let () = if (List.length !func_to_analyze == 0) then (to_do := true) else () in

      let () = if (!to_do == false) then (
	if (String.compare a (List.hd !func_to_analyze) == 0)
	then (to_do := true) else ()
      ) else () in
	
	if (!to_do) then (
	  let () = Printf.printf "Func name %s\n Getting Cfg ...\n" a in
	  let fcfg = (Vine_cfg.func_to_cfg f) in
	  let () = Printf.printf " Doing Stack analysis ....\n Max depth in %s is %s\n" a 
	    (Int64.to_string (Vine_dataflow.get_max_stack_depth fcfg)) in
	  let () = Printf.printf " Formal parameters and local variable offsets in %s are ::\n" a in
	  let lvarset = (Vine_dataflow.get_local_vars (fcfg)) in
	  let () =SetOfInt64.iter (fun x -> Printf.printf " %s " (Int64.to_string x)) lvarset in
	  let () = Printf.printf "\n" in
	    ()
	)
	else (
	  ()
	)
  | _ -> ()
      
in
  
let usage = "stackstats [options]* infile\n" in
let infile = ref "" in 
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
      ("-funcname", Arg.String(prepend func_to_analyze),
       " <name> Name of the function to perform stack analysis on.");    
    ] in 
    let speclist = speclist @ myspeclist in 
    let () = Arg.parse speclist arg_name usage in 
    let (prog,funinfos) = Vine_tovine.to_program true in 
    let (dl,sl) = Vine_tovine.replace_calls_and_returns prog funinfos in
    let () = List.iter (fun x -> print_stack_analysis_stats x) sl 
    in  ()
  )
in
  main (Array.length Sys.argv) Sys.argv;;

