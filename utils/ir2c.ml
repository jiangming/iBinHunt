(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
Author: Zhenkai Liang
$Id: ir2c.ml 2313 2007-10-12 20:50:10Z zliang $
*)
      
(*   let () = print_string ("#include \"irtest.h\"\n") in *)
(*   let () = print_string ("int ir_tester" ^  *)
(* 			    "(struct regs_struct *regs, char *INPUT)\n" ^  *)
(* 			    "{\n" ^ "    u_int8_t post;\n") *)
(*   in  *)
(*   let p dlist slist = *)
(*     Block(dlist, slist)  *)
(*   in *)
(*   let () = p2c_stmt (p dl sl) in *)
(*   let () = print_string "    return post;\n}\n" *)
(*   in *)
(*     p2c_func (p dl sl)  *)
(* ;;       *)

type cmdlineargs_t = {
    mutable infile : string; 
    mutable regular : bool;  (* generate regular C file or signature *)
  } ;;

let usage = "ir2c [options]* file" in 
let cmdargs = {
    infile = "";
    regular = false; 
  } in
let arg_spec = [
    ("-regular", Arg.Unit (fun s -> cmdargs.regular <- true), 
    "Generating regular C files. Default is to generate signatures.");
  ] in 
let main argc argv = 
  let () = Arg.parse arg_spec (fun s -> cmdargs.infile <- s) usage in
    if (cmdargs.infile <> "") then (
(*       Vine_absyn.strip_nums := true; *)
      let prog = Vine_parser.parse_file cmdargs.infile in 
	Vine_ir2c.program_to_c (print_string) prog cmdargs.regular;
    )
    else
      let () = Printf.printf "%s\n" usage in
	exit(1);
in
  main (Array.length Sys.argv) Sys.argv;;



(* ;; *)

(* if true then Gc.set { (Gc.get()) with Gc.verbose = 0x00c; Gc.max_overhead = 10000000 };; *)

(* let _ = Sys.signal Sys.sigusr1 (Sys.Signal_handle (fun _ -> Gc.compact())) ;; *)

(* if Array.length Sys.argv < 3 *)
(* then  (print_string "Usage: ir2c <tracefile> <c_output>\n"; exit 0);; *)

(* ir2c Sys.argv.(1) Sys.argv.(2) *)
