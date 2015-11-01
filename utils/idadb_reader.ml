(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  idadb_reader.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Tue Jun  5 12:27:51 2007 David Brumley
*  Last update Thu Jun 21 15:37:20 2007 David Brumley
*)

open Vine;;
open Vine_util;;
module List = ExtList.List;;
open Vine_idadb;;

let print_funcs lst = 
  Printf.printf ("---- functions ---\n%!");
  List.iter (fun f -> pr_idafunc (print_string) f;
	       Printf.printf "\n%!") lst

let print_disasm lst = 
  Printf.printf ("---- disassembly ---\n%!");
  List.iter (fun a -> pr_idainstr (print_string) a;
	       Printf.printf "\n%!") lst


let print_imports lst = 
  Printf.printf ("---- imports ---\n%!");
  List.iter (fun a -> pr_idaimport (print_string) a;
	       Printf.printf "\n%!") lst

let print_exports lst = 
  Printf.printf ("---- exports ---\n%!");
  List.iter (fun a -> pr_idaexport (print_string) a;
	       Printf.printf "\n%!") lst

let print_idastr lst = 
  Printf.printf ("---- strings ---\n%!");
  List.iter (fun a -> pr_idastring (print_string) a;
	       Printf.printf "\n%!") lst
;;

let usage = "idadb_reader [options]* <idadb_file>\n" in
let infile = ref "" in 
let infile_set = ref false in 
let arg_name s = 
  infile := s; 
  infile_set := true 
in
let main argc argv = 
  (
    let speclist = Vine_tovine.speclist in 
    let () = Arg.parse speclist arg_name usage in 
    let () = if not !infile_set then
      failwith usage in
    let db = Sqlite3.db_open !infile in 
    let infos = get_idainfos db in 
    let () = List.iter (fun i  -> 
			  let (file_id,_,_,_,_,_,_,_,_,_,_,_) = i in 
			  Printf.printf "--- info ---\n%!";
			  pr_idainfo (print_string) i;
			  Printf.printf "\n%!";
			  print_disasm (get_idainstr_by_id db file_id);
			  print_funcs (get_idafuncs_by_id db file_id);
			  print_imports (get_idaimports_by_id db
					   file_id);
			  print_exports (get_idaexports_by_id db
					   file_id);
			  print_idastr (get_idastrings_by_id db file_id);
			  Printf.printf "\n\n%!"
		       ) infos in
      ()
  )
in
main (Array.length Sys.argv) Sys.argv;;
