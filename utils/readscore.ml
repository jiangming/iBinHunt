open Vine
open Vine_tovine
open Vine_cfg

let read_score_ch = (open_out ("debug/readscore_debug")) ;;

let main argc argv = 
(
		let score_db = argv.(1) in
		let db_type = argv.(2) in
		
		let score_in_ch = open_in score_db in
		let block_matchings_l = (Marshal.from_channel score_in_ch: (bbid*bbid*float) list) in
		
		
		Printf.fprintf read_score_ch "%s\n" score_db;
		let () = List.iter(fun (id1,id2,score) -> 
			Printf.fprintf read_score_ch "%s %s %f\n" (bbid_to_string(id1))  (bbid_to_string(id2)) score;
			)block_matchings_l 
		in
			
		let () = close_in score_in_ch in
()
)
in
main (Array.length Sys.argv) Sys.argv;;
close_out read_score_ch;;