(*createed by pan meng*)
(*translate the ida db to IR *)

open Vine
open Vine_tovine
open Vine_cfg
open Vine_util
open Exectrace 
open Sqlite3;;

module List = ExtList.List ;;
module String = ExtString.String ;;
(*match table*)

let fix_name n =
	let n2 = 
	if ( String.contains n '@')
	then (
		let left_index = String.index n '@' in
		String.sub n 1 (left_index-1)
	)
	else n
	in
	if ( (String.contains n2 '(') && (String.contains n2 ')') )
	then (
		let left_index = String.rindex n2 '(' in
		String.sub n2 0 left_index
	)
	else n2
;;

let main argc argv = 
(
			let ida_file = argv.(1) in
	
			let ((dl,sl),finfo_l) = Vine_tovine.from_ida_flat true ida_file 1 in
			let (dl,sl) = Vine_tovine.replace_calls_and_returns (dl,sl) finfo_l in
			let finfo_l = List.map (fun f -> 
				{f with name= (fix_name f.name) }
			) finfo_l in
	
			let fl = List.filter (fun f ->
	    match f with
	     |   Function(n,_,_,false,Some(s)) when n <> Vine_tovine.unknown_addrs_function.name-> true 
	     |   Function(n,_,_,true,_) when n <> Vine_tovine.unknown_addrs_function.name-> true 
	     |   _ -> false
  		) sl in
	
	let out_ir = open_out ("./middle/" ^ ida_file^".ir") in
	let () = Marshal.to_channel out_ir (sl) [] in
	let () = flush out_ir in
	let () = close_out out_ir in
()
)
in
main (Array.length Sys.argv) Sys.argv;;