open Sqlite3;;


let out_debug = open_out "debug.txt";;
let debug_flag = ref(true);;

let source_postfix = ref([]);;
let dest_postfix = ref([]);;
let result_postfix = ref([]);;

let header_update = ref(true);;
let int_tbl_header = ref([]);;
let int_tbl_rows = ref([]);;

let print_tbl_local hlist rlist = 
   let () = Printf.printf "\n\nHeader:\t" in
   let () = List.iter (fun c -> 
	Printf.printf "\t%s" c
   ) hlist
   in
   let () = Printf.printf "\n\n" in

   List.iter (fun r ->
	Printf.printf "Row:\t";
	List.iter (fun f ->
		Printf.printf "%s\t" f
        ) r ;
	Printf.printf "\n"
   ) rlist
;;

(*
let fix_name n =
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
;;*)

let fix_name n =
	let n2 = 
	if ( String.contains n '@')
	then (
		let left_index = String.index n '@' in
		if(left_index=0) then n
		else
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
	| Some(s) -> (fix_name s)
	| None -> "EMPTY FIELD"
   ) row_list in
   if (List.length !int_tbl_rows) = 0 then int_tbl_rows := [row_list2]
   else int_tbl_rows := !int_tbl_rows @ [row_list2]
;;



let print_tbl_from_sql  = fun r h ->
   let () = Printf.printf "\n\nPrinting header:\n" in
   let col_list = (Array.to_list h) in
   let () = List.iter (fun c -> 
	Printf.printf "\t%s\n" c
   ) col_list
   in

   let () = Printf.printf "\n\nPrinting row:\n" in
   let row_list = (Array.to_list r) in
   (*let num_rows = (List.length row_list) in*)
   List.iter (fun row_opt -> match row_opt with
	|Some(s) -> 	Printf.printf "\t%s\n" s
	| None -> Printf.printf "\tEMPTY FIELD\n"
   ) row_list
;;


let set_spostfix = fun r h ->
   let row_list = (Array.to_list r) in
   List.iter (fun row_opt -> match row_opt with
	|Some(s) -> source_postfix := s :: !source_postfix
	| None -> ()
   ) row_list
;;

let set_dpostfix = fun r h ->
   let row_list = (Array.to_list r) in
   List.iter (fun row_opt -> match row_opt with
	|Some(s) -> dest_postfix := s :: !dest_postfix
	| None -> ()
   ) row_list
;;

let set_rpostfix = fun r h ->
   let row_list = (Array.to_list r) in
   List.iter (fun row_opt -> match row_opt with
	|Some(s) -> result_postfix := s :: !result_postfix
	| None -> ()
   ) row_list
;;




let main argc argv = 
(

let sqlite_db_handle = db_open argv.(1) in



(*let ret = exec  sqlite_db_handle ~cb:print_tbl_from_sql  "SELECT * FROM DiffResultsInfo" in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
*)

let ret = exec sqlite_db_handle ~cb:set_spostfix  "SELECT src_table_postfix FROM DiffResultsInfo " in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in

let ret = exec sqlite_db_handle ~cb:set_dpostfix  "SELECT dst_table_postfix FROM DiffResultsInfo " in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in

let ret = exec sqlite_db_handle ~cb:set_rpostfix  "SELECT results_postfix FROM DiffResultsInfo " in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in

let () = Printf.printf "source_postfix = %s\n" (List.hd !source_postfix) in
let () = Printf.printf "dest_postfix = %s\n" (List.hd !dest_postfix) in
let () = Printf.printf "result_postfix = %s\n" (List.hd !result_postfix) in

let srcNames = "Names_" ^ (List.hd !source_postfix) in
let dstNames = "Names_" ^ (List.hd !dest_postfix) in
let funMatchTbl = "SubroutineMatchTable_" ^ (List.hd !result_postfix) in
let blockMatchTbl = "FunctionMatchTable_" ^ (List.hd !result_postfix) in

(*
let ret = exec  sqlite_db_handle ~cb:print_tbl_from_sql  ("SELECT * FROM Names_" ^ (List.hd !source_postfix)) in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
*)

(*
let ret = exec  sqlite_db_handle ~cb:print_tbl_from_sql  ("SELECT address , name FROM " ^ dstNames) in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
*)

(*
let match_query = "select " ^ srcNames ^ ".name , " ^ dstNames ^ ".name , " ^ funMatchTbl ^ ".MatchRate FROM " ^ srcNames ^ " , " ^ dstNames ^ " , " ^ funMatchTbl ^ " WHERE " ^ srcNames ^ ".address = " ^ funMatchTbl ^ ".Address01 AND " ^ dstNames ^ ".address = " ^ funMatchTbl ^ ".Address02" in

let match_query2 = "select " ^ srcNames ^ ".name , " ^ dstNames ^ ".name , " ^ blockMatchTbl ^ ".MatchRate FROM " ^ srcNames ^ " , " ^ dstNames ^ " , " ^ blockMatchTbl ^ " WHERE " ^ srcNames ^ ".address = " ^ blockMatchTbl ^ ".Address01 AND " ^ dstNames ^ ".address = " ^ blockMatchTbl ^ ".Address02" in
*)

(* let () = Printf.printf "match_query = %s\n" match_query in *)



(** get function matchings *)

let query1 = "SELECT address , name FROM " ^ srcNames in
let query2 =  "SELECT address , name FROM " ^ dstNames in
let query3 = "SELECT Address01, Address02, MatchRate FROM " ^ funMatchTbl in

let ret = exec  sqlite_db_handle ~cb:store_tbl  query1 in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
let query_tbl_header1 = !int_tbl_header in
let query_tbl_rows1 = !int_tbl_rows in
let () = header_update := true in
let () = int_tbl_rows := [] in

let ret = exec  sqlite_db_handle ~cb:store_tbl  query2 in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
let query_tbl_header2 = !int_tbl_header in
let query_tbl_rows2 = !int_tbl_rows in
let () = header_update := true in
let () = int_tbl_rows := [] in

let ret = exec  sqlite_db_handle ~cb:store_tbl  query3 in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
let query_tbl_header3 = !int_tbl_header in
let query_tbl_rows3 = !int_tbl_rows in
let () = header_update := true in
let () = int_tbl_rows := [] in

let addr_to_name1 = Hashtbl.create (List.length query_tbl_rows1) in

let addr_to_name2 = Hashtbl.create (List.length query_tbl_rows2) in

let () = List.iter (fun r ->
	Hashtbl.add addr_to_name1 (List.hd r) (List.hd (List.tl r))
) query_tbl_rows1 in

let () = List.iter (fun r ->
	Hashtbl.add addr_to_name2 (List.hd r) (List.hd (List.tl r))
) query_tbl_rows2 in

let fun_matching_table = Hashtbl.create (List.length query_tbl_rows3) in

let () = List.iter (fun r ->  
	let a1 = (List.hd r) in
	let a2 = (List.hd (List.tl r)) in
	let match_rate = float_of_string (List.hd (List.tl (List.tl r))) in
	try 	Hashtbl.add fun_matching_table (Hashtbl.find addr_to_name1 a1) ((Hashtbl.find addr_to_name2 a2), match_rate)
	with Not_found -> Printf.printf "Error in fun_matching_table!\n"
) query_tbl_rows3 in

(*
let () = Hashtbl.iter (fun a (b,c) ->
	Printf.printf "%s matched with %s, score = %f\n" a b c
) fun_matching_table in
*)

let () = Printf.printf "Size of fun_matching_table = %d..." (Hashtbl.length fun_matching_table) in
let () = flush stdout in

let out_ir = open_out ("fun_matchings__" ^ argv.(1)) in
let () = Marshal.to_channel out_ir (fun_matching_table) [] in
let () = flush out_ir in
let () = close_out out_ir in

let () = Printf.printf "finished marshalling out function matches.\n" in
let () = flush stdout in



(** get block matchings *)

let query4 = "SELECT Address01, Address02, MatchRate FROM " ^ blockMatchTbl in

let ret = exec  sqlite_db_handle ~cb:store_tbl  query4 in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
let query_tbl_header4 = !int_tbl_header in
let query_tbl_rows4 = !int_tbl_rows in
let () = header_update := true in
let () = int_tbl_rows := [] in

let block_matching_table = Hashtbl.create (List.length query_tbl_rows4) in

let () = List.iter (fun r ->  
	let a1 = Int64.of_string (List.hd r) in
	let a2 = Int64.of_string (List.hd (List.tl r)) in
	let match_rate = float_of_string (List.hd (List.tl (List.tl r))) in
	Hashtbl.add block_matching_table a1 (a2, match_rate)
) query_tbl_rows4 in

(*
let () = Printf.printf "\n\n**********Printing block matching table, num entries = %d:\n" 
	(Hashtbl.length block_matching_table) in
let () = flush stdout in
*)

(*
let () = Hashtbl.iter (fun a (b,c) ->
	Printf.printf "%s matched with %s, score = %f\n" (Int64.to_string a) (Int64.to_string b) c
) block_matching_table in
*)


let () = Printf.printf "Size of block_matching_table = %d\n" (Hashtbl.length block_matching_table) in
let () = flush stdout in

let out_ir = open_out ("block_matchings__" ^ argv.(1)) in
let () = Marshal.to_channel out_ir (block_matching_table) [] in
let () = flush out_ir in
let () = close_out out_ir in



(*
let match_tbl_header = !int_tbl_header in
let match_tbl_rows = !int_tbl_rows in
let () = header_update := true in
let () = int_tbl_rows := [] in
let () = Printf.printf "# cols in match tbl = %d\n" (List.length match_tbl_header) in
let () = Printf.printf "# rows in match tbl = %d\n" (List.length match_tbl_rows) in
let () = flush stdout in

let () = print_tbl_local match_tbl_header match_tbl_rows in
*)

(*
let ret = exec  sqlite_db_handle ~cb:store_tbl  match_query2 in
let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in

let block_match_tbl_header = !int_tbl_header in
let block_match_tbl_rows = !int_tbl_rows in
let () = header_update := true in
let () = int_tbl_rows := [] in
let () = Printf.printf "# cols in block match tbl = %d\n" (List.length block_match_tbl_header) in
let () = Printf.printf "# rows in block match tbl = %d\n" (List.length block_match_tbl_rows) in

let () = print_tbl_local block_match_tbl_header block_match_tbl_rows in
*)


db_close sqlite_db_handle


)

in

main (Array.length Sys.argv) Sys.argv;;


close_out out_debug;;







