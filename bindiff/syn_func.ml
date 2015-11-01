open Sqlite3;;


module List = ExtList.List ;;
module String = ExtString.String ;;
(*match table*)

let header_update = ref(true);;
let int_tbl_header = ref([]);;
let int_tbl_rows = ref([]);;


let mt_fix_name n =
	let n2 = 
	if ( String.contains n '@')
	then (
		let left_index = String.index n '@' in
		String.sub n 1 (left_index-1)
	)
	else n
	in
	if ( (String.length n2) >= 3 && (String.sub n2 0 3) = "loc" ) 
	then (
		let () = String.blit "sub" 0 n2 0 3 in
		n2
	)
	else n2
;;


let store_tbl  = fun r h ->
   let () = if !header_update then ( 
	let () = int_tbl_header := [] in
	let col_list = (Array.to_list h) in
	let () = List.iter (fun c -> 
		int_tbl_header := !int_tbl_header @ [c]
	) col_list in
        header_update := false
	)
   in

   let row_list = (Array.to_list r) in
   let num_rows = (List.length row_list) in
   let row_list2 = List.map (fun row_opt -> match row_opt with
	| Some(s) -> (mt_fix_name s)
	| None -> "EMPTY FIELD"
   ) row_list in
   if (List.length !int_tbl_rows) = 0 then int_tbl_rows := [row_list2]
   else int_tbl_rows := !int_tbl_rows @ [row_list2]
;;


let gen_func_match_tbl dgf_file =
	let tbl_func_match = Hashtbl.create 0 in
	let sqlite_db_handle = db_open dgf_file in
	let query4 = "select TheSourceFunctionName, MatchRate from FunctionMatchInfo" in
	let ret = exec  sqlite_db_handle ~cb:store_tbl  query4 in
	let () = Printf.printf "return = %s~\n" (Sqlite3.Rc.to_string ret) in
	let query_tbl_header4 = !int_tbl_header in
	let query_tbl_rows4 = !int_tbl_rows in
	let () = header_update := true in
	let () = int_tbl_rows := [] in
	
	
	let () = List.iter (fun r ->  
	let n = (List.hd r) in
	let match_rate = float_of_string (List.hd (List.tl r)) in
	
	let () = Printf.printf "%s %f\n" n match_rate in
	
	if (match_rate >= 100.00) then
		Hashtbl.add tbl_func_match  n (n, match_rate)
) query_tbl_rows4 in
	
	let func_match_file_ch = open_out (dgf_file^"_func_match.syn") in
	let () = Marshal.to_channel func_match_file_ch (tbl_func_match) [] in
	let () = flush func_match_file_ch in
()
in


let main argc argv = 
(
	let dgf_file = argv.(1) in

	let () = gen_func_match_tbl dgf_file in
	
()
)
in
main (Array.length Sys.argv) Sys.argv;;