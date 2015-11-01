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
*  Last update Wed Jun 20 18:36:17 2007 David Brumley
*)
open Vine;;
open Vine_util;;
module List = ExtList.List;;

let print_it do_dot = function
    Function(a,b,c,d,Some(_)) as f ->
      let oc = open_out (a^".ir") in 
      let () = Vine.pp_program (output_string oc) ([],[f]) in
      let () = close_out oc in
	if do_dot then (
	  let oc = open_out (a^".dot") in 
	  let () = 
	    Vine_cfg.print_dot_cfg (Vine_cfg.func_to_cfg f) a
				      Vine_cfg.stmt_printer oc in
	    close_out oc
	) else ()
	
  | _ -> ()
;;

let write_prog_ir s name = 
  let x = name^".ir" in 
  let oc = open_out x in 
  let () = Vine.pp_program (output_string oc) s in
    close_out oc
;;


let usage = "elfutil [options]* outfile\n" in
let flag_do_dot = ref false in 
let infile = ref "" in 
let infile_set = ref false in 
let irfile = ref "" in
let start_address = ref 0L in 
let end_address = ref 0L in 
let inst_address = ref 0L in 
let arg_name s = 
  infile := s; 
  infile_set := true 
in

let main argc argv = 
  let speclist = Vine_tovine.speclist in 
  let myspeclist = [
    ("-dot", Arg.Set(flag_do_dot), " Enable dot output");
    ("-ir", Arg.Set_string(irfile), " <file> IR output file");
    ("-saddr", Arg.String (fun s -> start_address := Int64.of_string s), 
    "Starting address");
    ("-eaddr", Arg.String (fun s -> end_address := Int64.of_string s), 
    "End address");
    ("-iaddr", Arg.String (fun s -> inst_address := Int64.of_string s), 
    "Instruction address in a functions");
  ] in 
  let speclist = speclist @ myspeclist in 
  let () = Arg.parse speclist arg_name usage in 
  let addr_range_to_file addrstart addrend output =
    let prog = 
      if !Vine_tovine.flag_is_elf then
	Vine_tovine.elf_address_range_to_ir !Vine_tovine.flag_elf_file
	  addrstart addrend 
      else 
	Vine_tovine.ida_address_range_to_ir !Vine_tovine.flag_idadb_file 
	  !Vine_tovine.flag_idadb_fileid addrstart addrend 
    in
    let prog = Vine_memory2array.coerce_prog prog in
      write_prog_ir prog output 
  in
  let range_of_function instaddr =
    let db = Sqlite3.db_open !Vine_tovine.flag_idadb_file in
    let condstr = Printf.sprintf "%Lu >= start_address and %Lu < end_address" 
      instaddr instaddr in
    let finfos = Vine_idadb.get_idafuncs_where db condstr in
    let (_, _, _, _, _, sa, ea) = List.hd finfos in
    let () = Printf.fprintf stderr "0x%Lx 0x%Lx\n" sa ea in
      (sa, ea)
  in
    if (!irfile <> "") then (
      if !start_address = 0L && !inst_address <> 0L
      then (
	let (sa, ea) = range_of_function !inst_address in
	  start_address := sa; 
	  end_address := ea; 
      );
      addr_range_to_file !start_address !end_address !irfile;
    )
    else (
(*       let testprog = Vine_tovine.elf_address_range_to_ir "libc-2.2.5.so" 0x420825B0L 0x420825D2L in *)
(*       let testprog = Vine_memory2array.coerce_prog testprog in *)
(* 	Vine.pp_program (fun s -> Printf.printf "%s" s) testprog *)

    )
in
  main (Array.length Sys.argv) Sys.argv;;


(*    

(*     let testprog = Vine_tovine.ida_address_range_to_ir "libc-2.2.5.so.db" 1 0x420825B0L 0x420825D2L in *)
    (*     let () = Vine.pp_program (fun s -> Printf.printf "%s" s) testprog in *)
  let testprog = Vine_tovine.elf_address_range_to_ir "libc-2.2.5.so" 0x420825B0L 0x420825D2L in
  let testprog = Vine_memory2array.coerce_prog testprog in
  let () = Vine.pp_program (fun s -> Printf.printf "%s" s) testprog in 

    (*     let (prog,funinfos) = Vine_tovine.to_program true in  *)
    (*     let (dl,sl) = Vine_tovine.replace_calls_and_returns prog funinfos in *)
    (*     let t2 = Unix.gettimeofday () in *)
    (*     let () = Printf.printf "Total time to translate: %f\n%!"  *)
    (*       (t2 -. t1) in  *)
    (*     let () = if !flag_do_dot then  *)
    (*       List.iter (fun x -> print_it !flag_do_dot x ) sl else ()  *)
    (*     in  *)
    (*     let () =  *)
    (*       if !irfile <> "" then *)
    (* 	write_prog_ir prog !irfile *)
    (*       else ()  *)
    (*     in  *)
    ()



*)
