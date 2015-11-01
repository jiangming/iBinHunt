open Vine
open Vine_tovine
open Vine_cfg
open Vine_util
open Exectrace 
open Sqlite3;;

module List = ExtList.List ;;
module String = ExtString.String ;;
(*match table*)

let thread_wait_tbl = (Hashtbl.create 1024) ;;

let before_match_num = ref 0 ;;

let header_update = ref(true);;
let int_tbl_header = ref([]);;
let int_tbl_rows = ref([]);;
let fun_matchings_l = ref [] ;;
(*let block_matchings = ref (Hashtbl.create 0) ;;*)
let block_matchings_l = ref [] ;;
let ref_pre_and_suc_match_l = ref [];;
let ref_pre_or_suc_match_l = ref [];;
let ref_tested_id_pair = ref [] ;;
(*let ref_*)

(*bb_range*)
type bb_range = 
{
	id: Vine_cfg.bbid;
	start_addr: int64;
	end_addr: int64;
};;

(**thread*)
let number_of_threads1 = 2;;
let number_of_threads2 = 1;;

let threads_wait1 = 0.01;;
let threads_wait2 = 5.0;;

(*let threads_wait1 = 0.1;;
let threads_wait2 = 6.0;;*)

let m_threads = Mutex.create ();;
(*let m_score = Mutex.create ();;*)
let m_score= m_threads;;


let threads_count = ref 0;;
let threads = ref [];;


(*blk_stp*)
let trace_diff_debug_ch = (open_out ("debug/trace_diff.debug")) ;;

let score_same_inst = 1.00;;	(* debin previously has 0.9 *)
let score_same_type = 0.9;;
let score_same_stp = 0.85;;
let score_color_slight = 0.8;;
let score_same_pre_and_suc = 0.7;;
let score_same_pre_or_suc = 0.5;;
(*let score_same_type = 0.7;;*)
let score_timeout = 0.5;;
let score_same_name = 0.0;;	(* debin previously had 0.0 *)
(*let score_same_size = 0.05;;*)
let score_empty = 1.00;;	(*debin previously had 0.4*)
let score_diff = 0.0;;
let score_empty_and_same_name = 1.00;;
(*cfg.iso end*)

let blk_length_similar_abs = 2;;
let blk_length_similar_rel = 0.1;;

let init_max_size_ratio_cfg1 = 0.99;;
let init_max_size_ratio_cfg2 = 0.45;;
let init_max_score_ratio_cfg = 0.2;;
let final_score_ratio = 0.5;;
let final_size_ratio1 = 0.5;;
let final_size_ratio2 = 0.1;;

let timeout_length_cfg = 3.0;;
let timeout_count_cfg = 1000;;(*peng1000->100*)

let stp_timeout = 100;;

let cfg_debug_flag_level1 = true;;(*peng*)
let cfg_debug_flag_level2 = true;;(*peng*)

(*let blk_stp_path = "/home/raistlin/work/vine/bindiff/blk_stp";;*)
let blk_stp_path = "../bindiff/blk_stp";;


let cfg_stp_queries = ref 0;;
let cfg_testv_calls = ref 0;;
let cfg_stp_true = ref 0;;
let cfg_quick_true = ref 0;;
(***********************************************************************************************************)
let bb_to_saddr sl = List.fold_left ( fun acc s ->
	if acc = Int64.zero 
	then (
     		 match s with
        		| Comment str -> (
                   		try (
					let lindex = String.index str ':' in
					(*let () = Printf.printf "str = %s \n lindex = %d!\n" str lindex in*)
					(*Int64.of_string ("0x" ^ (String.uppercase (String.sub str 0 lindex)))*)
					  if lindex = 7
					  then (Int64.of_string ("0x" ^ (String.uppercase (String.sub str 0 lindex))))
					  else acc (*peng*)

				)
              			with Not_found -> acc
            		)
			| _ -> acc
	)
	else acc
   ) Int64.zero sl
;;

(************************************blk_diff****************************************************************************)
(*let blk_diff sl1 sl2 block_matchings test_type test_stp cfgdiff_debug_ch debug_str =*)
let blk_diff (id1, id2, sl1, sl2, block_matchings, test_type, test_stp, cfgdiff_debug_ch, debug_str) =
(** @return true when control can flow here from somewhere other than the
    preceding stmt *)
  let rec is_ignored s =
    match s with
    	Comment _ | ExpStmt _ -> true
	| Function _ -> ( Printf.fprintf cfgdiff_debug_ch "WARNING: found Function in preprocess_blk!!\n"; true  )
  	| Attr(s',_) -> is_ignored s'
  	| _ -> false
  in

  (** start preprocess_blk subroutine *)
  let preprocess_blk sl =
    let rec filter_blk sl =
      match sl with
        | s1 :: tail -> (
            if (is_ignored s1)
            then filter_blk tail
            else
              (
              match s1 with
                | Block (dl, sl) -> filter_blk (sl @ tail)
                | Attr (s2, _) -> filter_blk (s2 :: tail)
                | _ -> s1 :: (filter_blk tail)
              )
            )
        | [] -> []
    in

   
    (* returns a String list *)
    let blk_asm = List.fold_left (fun acc s ->
      match s with
        | Comment str -> (
            let col_pos = (
              try String.index str ':'
              with
                Not_found -> -1
              ) + 1
            in
            (String.sub str col_pos (String.length str - col_pos)) :: acc
            )
        | _ -> acc
      ) [] sl
    in

    let blk_rev = List.rev (filter_blk sl) in
		
    match blk_rev with
      | s :: tail -> (
          match s with
            | Jmp _
            | CJmp _
            | Call _ 
            | Return _ -> (Some s, List.rev tail, blk_asm, bb_to_saddr sl)
            | _ -> (None, List.rev blk_rev, blk_asm, bb_to_saddr sl)
          )
      | [] -> (None, [], blk_asm, bb_to_saddr sl)
  in
  (** end preprocess_blk subroutine *)

  let asm_same_content asm1 asm2 =
    asm1 = asm2
  in


  let rec stmt_same_type s1 s2 =
    match s1 with
      | None -> (
          match s2 with
            | None -> true
            | _ -> false
          )
      | Some Jmp _ -> (
          match s2 with
            | Some Jmp _ -> true
            | _ -> false
          )
      | Some CJmp _ -> (
          match s2 with
            | Some CJmp _ -> true
            | _ -> false
          )
      | Some Move _ -> (
          match s2 with
            | Some Move _ -> true
            | _ -> false
          )
      | Some Special _ -> (
          match s2 with
            | Some Special _ -> true
            | _ -> false
          )
      | Some Label _ -> (
          match s2 with
            | Some Label _ -> true
            | _ -> false
          )
      | Some ExpStmt _ -> (
          match s2 with
            | Some ExpStmt _ -> true
            | _ -> false
          )
      | Some Comment _ -> (
          match s2 with
            | Some Comment _ -> true
            | _ -> false
          )
      | Some Block (dl1, sl1) -> (
          match s2 with
            | Some Block (dl2, sl2) -> true
            | _ -> false
          )
      | Some Function _ -> (
          match s2 with
            | Some Function _ -> true
            | _ -> false
          )
      | Some Return _ -> (
          match s2 with
            | Some Return _ -> true
            | _ -> false
          )
      | Some Call _ -> (
          match s2 with
            | Some Call _ -> true
            | _ -> false
          )
      | Some Attr (ss1,_) -> (
          match s2 with
            | Some Attr (ss2,_) -> stmt_same_type (Some ss1) (Some ss2)
            | _ -> false
          )
      | _ -> false
  in

  
  let blk_same_type b1 b2 =
    try (List.fold_left2 (fun acc s1 s2 -> 
      acc && (stmt_same_type (Some s1) (Some s2))
      ) true b1 b2)
    with
      (*Invalid_argument _ -> false*)(*pm*)
			_ -> false
  in

(**blk_stp*)
  let blk_stp b1 b2 = 
    let rec is_straightline blk =
      match blk with
        | (Jmp _) :: tail -> false
        | (CJmp _) :: tail -> false
        | Block (dl, sl) :: tail -> is_straightline (List.rev_append sl tail)
        | Attr (s, _) :: tail -> is_straightline (s :: tail)
        | s :: tail -> is_straightline tail
        | [] -> true
    in

   
    let get_posts blk =
      List.fold_left (fun (reg, mem) s ->
        match s with
          | Move (l, e) -> (
              match l with
                | Temp _ -> (l :: reg, mem)
                | Mem _ -> (reg, l :: mem)
              )
          | _ -> (reg, mem)
        ) ([], []) blk
    in


    if (is_straightline b1) && (is_straightline b2)
    then
      (
      let (post_reg1, post_mem1) = get_posts b1 in
      let (post_reg2, post_mem2) = get_posts b2 in
      let reg_length = List.length post_reg1 in
      let mem_length = List.length post_mem1 in
  (*    let () = if cfg_debug_flag_level1
	then Printf.fprintf cfgdiff_debug_ch "reg_length1=%d, mem_length1=%d, reg_length2=%d, mem_length2=%d\n" reg_length mem_length (List.length post_reg2) (List.length post_mem2) in*)
      if reg_length = (List.length post_reg2) && 
        mem_length = (List.length post_mem2)
      then
        (
        let reg_ret = if reg_length > 0
          then 
            (
            let (in_fd1, in_fd2) = Unix.pipe () in
            let (out_fd1, out_fd2) = Unix.pipe () in
            let (err_fd1, err_fd2) = Unix.pipe () in
            let () = if cfg_debug_flag_level1
              then Printf.fprintf cfgdiff_debug_ch "start stp, calling blk_stp executable\n%!"
            in
            let pid = 
              Unix.create_process blk_stp_path [||] out_fd1 in_fd2 err_fd2 
            in
            let () = if cfg_debug_flag_level1
              then Printf.fprintf cfgdiff_debug_ch "process created: %d\n%!" pid
            in
            let buf = String.create 6 in
            let buf_read = Unix.read in_fd1 buf 0 6 in
            let () = if cfg_debug_flag_level1
              then Printf.fprintf cfgdiff_debug_ch "%d: %s%!" buf_read buf
            in
            let out_ch = Unix.out_channel_of_descr out_fd2 in
            let () = Marshal.to_channel out_ch (post_reg1, post_reg2, 
              reg_length, b1, b2, "debug/blk_stp_reg." ^ debug_str) [] in
            let () = flush out_ch in
            let () = if cfg_debug_flag_level1
              then Printf.fprintf cfgdiff_debug_ch "request sent\n%!"
            in
            let in_ch = Unix.in_channel_of_descr in_fd1 in
	    let (stp_queries_read,testv_calls_read,reg_ret_read,quick_ret_read) = 
	      (Marshal.from_channel in_ch : int * int * bool * bool ) 
	    in
	    let () = if cfg_debug_flag_level1
		then Printf.printf "stp_queries=%d, testv_calls=%d, stp_true=%b, quick_true=%b, str=%s\n" stp_queries_read testv_calls_read reg_ret_read quick_ret_read debug_str 
	   in
            let _ = Unix.write out_fd2 "done\n" 0 5 in
            let () = Unix.close in_fd1 in
            let () = Unix.close out_fd1 in
            let () = Unix.close err_fd1 in
            let () = Unix.close in_fd2 in
            let () = Unix.close out_fd2 in
            let () = Unix.close err_fd2 in
	    let () = cfg_stp_queries := !cfg_stp_queries + stp_queries_read in
	    let () = cfg_testv_calls := !cfg_testv_calls + testv_calls_read in
	    let () = if reg_ret_read then cfg_stp_true := !cfg_stp_true + 1 in
	    let ()=  if quick_ret_read then cfg_quick_true := !cfg_quick_true + 1 in
	    reg_ret_read
            )
          else (
	 	let () = if cfg_debug_flag_level1 then Printf.fprintf cfgdiff_debug_ch "reg_length = 0\n!" in
		 true
		)
        in                 
        let () = if cfg_debug_flag_level1
          then 
            (
            if reg_ret 
            then Printf.fprintf cfgdiff_debug_ch "reg stp result: true\n"
            else Printf.fprintf cfgdiff_debug_ch "reg stp result: false\n"
            )
        in

        if reg_ret 
        then
          (
          let (mem_ret) = if mem_length > 0
            then 
              (
              let (in_fd1, in_fd2) = Unix.pipe () in
              let (out_fd1, out_fd2) = Unix.pipe () in
              let (err_fd1, err_fd2) = Unix.pipe () in
              let () = if cfg_debug_flag_level1
                then Printf.fprintf cfgdiff_debug_ch "start stp mem!\n"
              in
              let pid = 
                Unix.create_process blk_stp_path [||] out_fd1 in_fd2 err_fd2 
              in
              let () = if cfg_debug_flag_level1
                then Printf.fprintf cfgdiff_debug_ch "process created: %d\n%!" pid
              in
              let buf = String.create 6 in
              let buf_read = Unix.read in_fd1 buf 0 6 in
              let () = if cfg_debug_flag_level1
                then Printf.fprintf cfgdiff_debug_ch "%d: %s%!" buf_read buf
              in
              let out_ch = Unix.out_channel_of_descr out_fd2 in
              let () = Marshal.to_channel out_ch (post_mem1, post_mem2, 
                mem_length, b1, b2, "debug/blk_stp_mem." ^ debug_str) [] in
              let () = flush out_ch in
              let () = if cfg_debug_flag_level1
                then Printf.fprintf cfgdiff_debug_ch "mem request sent\n%!"
              in
               let () = if cfg_debug_flag_level1
              then Printf.fprintf cfgdiff_debug_ch "request sent\n%!"
           	 in
           	 let in_ch = Unix.in_channel_of_descr in_fd1 in
	   	 let (stp_queries_read,testv_calls_read,mem_ret_read,quick_ret_read) = 
	   	  (Marshal.from_channel in_ch  : int * int * bool * bool ) 
	   	 in
	         let () = if cfg_debug_flag_level1 then Printf.printf "stp_queries=%d, testv_calls=%d, stp_true=%b, quick_true=%b, str=%s\n" stp_queries_read testv_calls_read mem_ret_read quick_ret_read debug_str in
           	 let _ = Unix.write out_fd2 "done\n" 0 5 in
          	  let () = Unix.close in_fd1 in
          	  let () = Unix.close out_fd1 in
          	  let () = Unix.close err_fd1 in
           	 let () = Unix.close in_fd2 in
           	 let () = Unix.close out_fd2 in
            	let () = Unix.close err_fd2 in
	       let () = cfg_stp_queries := !cfg_stp_queries + stp_queries_read in
	    let () = cfg_testv_calls := !cfg_testv_calls + testv_calls_read in
	    let () = if mem_ret_read then cfg_stp_true := !cfg_stp_true + 1 in
	    let ()=  if quick_ret_read then cfg_quick_true := !cfg_quick_true + 1 in
	    mem_ret_read
              )
            else true
          in
          let () = if cfg_debug_flag_level1
            then 
              (
              if mem_ret
              then Printf.fprintf cfgdiff_debug_ch "mem stp result: true\n"
              else Printf.fprintf cfgdiff_debug_ch "mem stp result: false\n"
              )
	in
          mem_ret
          )
        else false
        )
      else false
      )
    else false
  in
(**blk_stp end*)

  let perform_test_content asm1 asm2 =
    let () = if cfg_debug_flag_level1
      then Printf.fprintf cfgdiff_debug_ch "start test_content\n"
    in
    if (asm_same_content asm1 asm2)
    then
      (
      let () = if cfg_debug_flag_level1
        then Printf.fprintf cfgdiff_debug_ch "--same_content\n"
        else ()
      in
      score_same_inst
      )
    else score_diff
  in

  let perform_test_type b1 b2 =
    let () = if cfg_debug_flag_level1
      then Printf.fprintf cfgdiff_debug_ch "start test type\n"
    in
    if (blk_same_type b1 b2)
    then
      (
      let () = if cfg_debug_flag_level1
        then Printf.fprintf cfgdiff_debug_ch "--same_type\n"
        else ()
      in
      (*score_sam_inst*)
			score_same_type
      )
    else score_diff
  in


  let perform_test_stp b1 b2 =
    let () = if cfg_debug_flag_level1
      then Printf.fprintf cfgdiff_debug_ch "start test stp\n"
    in
    let blk_length_similar b1 b2 =
      let l1 = List.length b1 in
      let l2 = List.length b2 in
      if l1 > l2
      then
        (
        let l_diff = l1 - l2 in
        l_diff < blk_length_similar_abs || 
          float_of_int(l_diff) /. float_of_int(l1) < blk_length_similar_rel
        )
      else 
        (
        let l_diff = l2 - l1 in
        l_diff < blk_length_similar_abs || 
          float_of_int(l_diff) /. float_of_int(l2) < blk_length_similar_rel
        )
    in


    if (blk_length_similar b1 b2)
    then 
      (
      let () = if cfg_debug_flag_level1
        then Printf.fprintf cfgdiff_debug_ch "starting stp test, block lengths = %d and %d\n\n" (List.length b1) (List.length b2)
      in
      if (blk_stp b1 b2)
      then
				( 
					let () = Printf.printf "blk_stp true,score_same_stp=%f\n" score_same_stp in
					score_same_stp
				)
      else score_diff
      )
    else 
      (
      let () = if cfg_debug_flag_level1
        then Printf.fprintf cfgdiff_debug_ch "skipping stp test, block length too dissimilar, block lengths = %d and %d\n\n" (List.length b1) (List.length b2)
      in
      score_diff
      )
  in


  (***** "entry" point for blk_diff routine *)
  (*let () = if cfg_debug_flag_level2
    then print_blk "Printing original blocks\n" sl1 sl2
    else ()
  in*)
  
  let (last_s1, blk1, asm1, saddr1) = preprocess_blk sl1 in
  let (last_s2, blk2, asm2, saddr2) = preprocess_blk sl2 in
  (*let () = if cfg_debug_flag_level2
    then 
      print_blk "Printing preprocessed blocks\n" blk1 blk2 
    else (
	if cfg_debug_flag_level1 then print_asm "Printing preprocessed asms\n" asm1 asm2
	)
  in*)
  let () = if cfg_debug_flag_level1
    then Printf.fprintf cfgdiff_debug_ch "start blk_diff\n"
  in
  
  if (stmt_same_type last_s1 last_s2) (* tests if last jump,call,return statement is same type *)
  then
    (
    if perform_test_content asm1 asm2 = score_same_inst	(* tests if identical assembly instructions *)
    then score_same_inst
    else
      (
      if test_stp 
      then
        (
        if perform_test_stp blk1 blk2 = score_same_stp  (* tests if semantically equivalent *)
        then score_same_stp
        else
          (
          if test_type 
          then perform_test_type blk1 blk2	(* tests if num and types of instructions are equivalent *)
          else score_diff
          )
        )
      else
        (
        if test_type 
        then perform_test_type blk1 blk2
        else score_diff
        )
      )
    )
  else score_diff
;;
(************************************************************************************************************)
let thread_blk_diff (id1, id2, sl1, sl2,  test_type, test_stp, cfgdiff_debug_ch, debug_str) =
	let t_self = Thread.self () in
	
	(*let () = Printf.printf "Thread %d: enter Mutex.lock m_threads \n" (Thread.id t_self)  in
	flush stdout;*)
  let () = Mutex.lock m_threads in
  let () = threads := t_self :: !threads in
  let () = threads_count := !threads_count + 1 in
  let () = Mutex.unlock m_threads in
	(*let () = Printf.printf "Thread %d: leave Mutex.lock m_threads \n" (Thread.id t_self)  in
	flush stdout;*)
			
	let ret = try (
		let (f_id1, f_id2, fast_score) = List.find (fun (m_id1,m_id2,m_rate) -> (m_id1=id1)) !block_matchings_l in
			
		true
	)
	with Not_found -> 
		(	
			let _ = if (true    
			) then
				(
						let () = Printf.printf "Thread %d: enter blk_diff, id1=%s, id2=%s \n" (Thread.id t_self) (bbid_to_string(id1)) (bbid_to_string(id2))  in
						flush stdout;
						let test_score = blk_diff 
														(id1, id2, sl1, sl2, !block_matchings_l, true, true, trace_diff_debug_ch,  "log") 
						in
						let () = Printf.printf "Thread %d: leave blk_diff \n" (Thread.id t_self)  in
						flush stdout;
						
						let () = if (test_score >= 0.85) then
							(
								(*let () = Printf.printf "Thread %d: enter Mutex.lock m_score \n" (Thread.id t_self)  in
								flush stdout;*)
								Mutex.lock m_score;
								(*Hashtbl.add !block_matchings id1 (id2, test_score);*)
								block_matchings_l := (id1, id2, test_score)::!block_matchings_l;
								Mutex.unlock m_score;		
								(*let () = Printf.printf "Thread %d: leave Mutex.lock m_score \n" (Thread.id t_self)  in
								flush stdout;*)
								()
							)
						in
					()
				)
			in
				
			false;
		)
	in	
	
	(*let () = Printf.printf "Thread %d: enter Mutex.lock m_threads 2222\n" (Thread.id t_self)  in
	flush stdout;*)
	Mutex.lock m_threads;

  threads := List.filter (fun x -> 
    x <> t_self
    ) !threads;
  threads_count := !threads_count - 1;
  Mutex.unlock m_threads;
	(*let () = Printf.printf "Thread %d: leave Mutex.lock m_threads 2222\n" (Thread.id t_self)  in
	flush stdout;*)
	()
;;
(************************************************************************************************************)
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

(*
let get_blk_match_tbl dgf_file range_tbl1 range_tbl2 ida_file2 =
	(**function dfg*)
	let dfg_list = ref [] in
	let fun_addr_l = ref [] in
	let sqlite_db_handle = db_open dgf_file in
	let query4 = "select TheSourceAddress, EndAddress, TheTargetAddress,MatchRate from FunctionMatchInfo" in
	let ret = exec  sqlite_db_handle ~cb:store_tbl  query4 in
	let () = Printf.printf "return = %s~\n" (Sqlite3.Rc.to_string ret) in
	let query_tbl_header4 = !int_tbl_header in
	let query_tbl_rows4 = !int_tbl_rows in
	let () = header_update := true in
	let () = int_tbl_rows := [] in
	
	let () = List.iter (fun r ->  
		let s1 = Int64.of_string (List.hd r) in
		let e1 = Int64.of_string (List.hd (List.tl r)) in
		let s2 = Int64.of_string (List.hd (List.tl (List.tl r))) in
		let match_rate = float_of_string (List.hd (List.tl (List.tl (List.tl r)))) /. 100. in
		
		if (match_rate >= 1.0) then
			dfg_list := (s1,e1,s2,match_rate)::!dfg_list;
	) query_tbl_rows4 in
	
	let ret = db_close sqlite_db_handle in
	
	(**function db2*)
	let db2_list = ref [] in
	let sqlite_db_handle = db_open ida_file2 in
	let query4 = "select start_address, end_address from functions" in
	let ret = exec  sqlite_db_handle ~cb:store_tbl  query4 in
	let () = Printf.printf "return = %s~\n" (Sqlite3.Rc.to_string ret) in
	let query_tbl_header4 = !int_tbl_header in
	let query_tbl_rows4 = !int_tbl_rows in
	let () = header_update := true in
	let () = int_tbl_rows := [] in
	
	let () = Printf.printf "before list.iter query_tbl_rows4\n" in
	let () = List.iter (fun r ->  
	let s = Int64.of_string (List.hd r) in
	let e = Int64.of_string (List.hd (List.tl r)) in
	db2_list := (s, e)::!db2_list;
) query_tbl_rows4 in

let () = Printf.printf "After list.iter query_tbl_rows4\n" in
	
	let ret = db_close sqlite_db_handle in
	
	(**map dfg to db2 end of fuc*)
	let () = List.iter(fun (s1,e1,s2,match_rate) -> 
		let _ = try(
		let (s,e2) = List.find (fun (x_s, x_e) -> (s2 = x_s)) !db2_list in
		fun_matchings_l := (s1,e1,s2, e2)::!fun_matchings_l;
		)
		with _ -> ()
		in
		()
		)!dfg_list 
	in
	
	let () = Printf.printf "After list.iter dfg_list\n" in
	
	(**block dfg*)
	let sqlite_db_handle = db_open dgf_file in
	let query4 = "select TheSourceAddress,TheTargetAddress,MatchRate from MatchMap " in
	let ret = exec  sqlite_db_handle ~cb:store_tbl  query4 in
	let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
	let query_tbl_header4 = !int_tbl_header in
	let query_tbl_rows4 = !int_tbl_rows in
	let () = header_update := true in
	let () = int_tbl_rows := [] in
	
	let () = Printf.printf "Before block_matching_table create\n" in
	(*let block_matching_table = Hashtbl.create (List.length query_tbl_rows4) in*)
	let block_matching_list = ref [] in
	
	let () = Printf.printf "After block_matching_table create\n" in
	
	let () = List.iter (fun r ->  
		let a1 = Int64.of_string (List.hd r) in
		let a2 = Int64.of_string (List.hd (List.tl r)) in
		let match_rate = float_of_string (List.hd (List.tl (List.tl r))) /. 100. in
		try(
			
			let id1 = Hashtbl.find range_tbl1 a1 in
			let id2 = Hashtbl.find range_tbl2 a2 in
			
			if (match_rate >= 1.0) then
				(*Hashtbl.add block_matching_table id1 (id2, match_rate)*)
				block_matching_list := (id1, id2, match_rate)::!block_matching_list;
			)
		with Not_found ->
			Printf.printf "get_blk_match_tbl: not found: a1=%Lx, a2=%Lx\n" a1 a2;
	) query_tbl_rows4 in
	
	let ret = db_close sqlite_db_handle in
	
!block_matching_list
;;
*)
let get_blk_match_tbl dgf_file range_tbl1 range_tbl2 ida_file1 ida_file2 =
	
	let () = Printf.printf "After list.iter query_tbl_rows4\n" in
	let syntac_ch = open_in ("./middle/"^ida_file1^"_"^ida_file2^".syn") in
	let block_matching_list = (Marshal.from_channel syntac_ch: (bbid*bbid*float) list) in
	let () = close_in syntac_ch in

	
block_matching_list
;;
(**************************************************************************************)
let self_label_to_addr_notail (l_t:label) =
	(*let l = del_label_tail l_t in*)
  try
    Scanf.sscanf l_t "pc_0x%Lx" (fun x-> x)
  with
      _ -> 
	raise (VineError "label_to_addr given non address-like label")
;;

let label_is_addr l = 
 try
    let _ = label_to_addr l in
    true
 with
    VineError _ -> 
      false
;;	
	
let make_BB_range cfg = 
	let range_tbl = Hashtbl.create cfg#length in
	let bbid_list = Vine_cfg.cfg_nodes cfg in
	
	let () = List.iter(fun id->
		let stmts = Vine_cfg.bb_stmts cfg id in
		let () = List.iter(fun stmt->
			let () = match stmt with
				| Label l->
					let is_addr = label_is_addr l in
					let () = match is_addr with
						| true->
							let addr =  self_label_to_addr_notail l in
							Hashtbl.add range_tbl addr id 
						| false->() 
					in	  
					()
				|_->()
		in
		()	
		)stmts in
	()
	)bbid_list in
range_tbl
;;
(******************************cmp *****************************************************************************)
let print_cfg current_cfg str_file_append=
    let counter = ref 0 in
    let cfgprint_ch = ref(open_out ("debug/"^str_file_append^"_cfgprint")) in
      
    let bbid_list = Vine_cfg.cfg_nodes current_cfg in
    
    let () = Printf.fprintf !cfgprint_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
    let () = Printf.fprintf !cfgprint_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
   
    let () = List.iter (fun bblock_id ->
    	let () = Printf.fprintf !cfgprint_ch "\t Looking at basic block id %s\n" (Vine_cfg.bbid_to_string bblock_id) in
	    let block_pred_list = Vine_cfg.bb_pred current_cfg bblock_id in
	    let block_succ_list = Vine_cfg.bb_succ current_cfg bblock_id in
	    let () = Printf.fprintf !cfgprint_ch "\t\t Predecessors: " in
	    let () = List.iter (fun b_id ->
	    Printf.fprintf !cfgprint_ch "%s " (Vine_cfg.bbid_to_string b_id)
    ) block_pred_list 
    in
      
		let () = Printf.fprintf !cfgprint_ch "\n\t\t Successors: " in
      
		let () = List.iter (fun b_id ->
	        Printf.fprintf !cfgprint_ch "%s " (Vine_cfg.bbid_to_string b_id)
    ) block_succ_list in
      
		let sl = current_cfg#get_info (current_cfg#find bblock_id) in
		let asm = List.fold_left (fun acc s ->
     		 match s with
     		   | Comment str -> (
         	  	 let col_pos = 0(*(
          	   		try String.index str ':'
           	   		with
               	 			Not_found -> -1
           	   		) + 1*)
           	 	in
            		acc ^ "\n" ^ (String.sub str col_pos (String.length str - col_pos)) 
            		)
        	| _ -> acc
      	) "" sl in
		let stmts = Vine_cfg.bb_stmts current_cfg bblock_id in
		let () = Printf.fprintf !cfgprint_ch "\n\t\t IR:\n" in
		let () = List.iter(fun stmt->
			Printf.fprintf !cfgprint_ch "%s\n" (stmt_to_string stmt)
			)stmts in
		Printf.fprintf !cfgprint_ch "\n\t\t Assembly:\n%s\n" asm
	
	
    ) bbid_list in

	let () = close_out !cfgprint_ch in 
  (*let () Printf.printf "print_cfg %s done!\n" str_file_append in*)
	()
;;

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
let make_cfgs function_l =
  
	let cfgs = List.fold_left (fun acc f ->
    match f with 
  	    | Function(n,_,_, true, _) -> (   (* external function *)
	  		let g = (prog_to_cfg ([], f::[])) in (* func_to_cfg requires a function DEFINITION *)
        (f,g) :: acc
	  		)
      	| Function(_,_,_,false, None) -> acc  (*remove this check? already ensured internal fun declarations were removed *)
      	| _ -> ( 	(*internal function definition *)
          let g = func_to_cfg f in
					(*let () = print_cfg g "cfg_before_coalesce" in*)
          let () = coalesce_bb g in 
          (* let () = Printf.printf "size of cfg = %d\n" (cfg_numnodes g) in *)
	  			(f,g) :: acc
        )
    ) [] function_l
  in
	cfgs;
;;


let static_analyze_db ida_file=
(*pm start flat*)
		let in_ir = open_in ("./middle/" ^ ida_file^".ir") in
		let fl = (Marshal.from_channel in_ir: Vine.stmt list) in
		let () = close_in in_ir in
		
 		let cfgs_f = make_cfgs fl in
 	
		let (flat_f,flat_cfg)= List.hd cfgs_f in
		
		let range_tbl = make_BB_range flat_cfg in

(range_tbl, flat_cfg)
;;

let slight_diff s_cfg id seq=
	let suc_matched = ref false in
	let pred_matched = ref false in
	let pre_id = ref (BB(0)) in
	let suc_id = ref (BB(0)) in
	
	let pred_l = bb_pred s_cfg id in
	let () = List.iter(fun bid -> 
		let () = match seq with
				| 1 ->
					let _ = try (
						
						let _ = List.find (fun (x_id1, x_id2, x_score) -> 
							if (x_id1 = bid) then true
							else false
							) !block_matchings_l 
						in
						
						pred_matched := true;
						pre_id := bid;
						) with Not_found -> ()
					in 
					()
				| 2 ->
					let _ = try (
						
						let _ = List.find (fun (x_id1, x_id2, x_score) -> 
							if (x_id2 = bid) then true
							else false
							) !block_matchings_l 
						in
						
						pred_matched := true;
						pre_id := bid;
						) with Not_found -> ()
					in 
					() 
			in
			()
		) pred_l
	in

	(**succ*)
	let succ_l = bb_succ s_cfg id in
	let () = List.iter(fun bid ->
		let () = match seq with
				| 1 ->
					let _ = try (
						
						let _ = List.find (fun (x_id1, x_id2, x_score) -> 
							if (x_id1 = bid) then true
							else false
							) !block_matchings_l 
						in
						
						suc_matched := true;
						suc_id := bid;
						) with Not_found -> ()
					in 
					()
				| 2 ->
					let _ = try (
						
						let _ = List.find (fun (x_id1, x_id2, x_score) -> 
							if (x_id2 = bid) then true
							else false
							) !block_matchings_l 
						in
						
						suc_matched := true;
						suc_id := bid;
						) with Not_found -> ()
					in 
					() 
			in
			()
		)succ_l in 
	
	let _ = if ((!pred_matched = true) && (!suc_matched = true)	) 
					then (
						ref_pre_and_suc_match_l := (id, !pre_id, !suc_id, score_same_pre_and_suc)::!ref_pre_and_suc_match_l; 
						)
					 else if ((!pred_matched = true) || (!suc_matched = true)	) then
						(
						ref_pre_or_suc_match_l := (id, !pre_id, !suc_id, score_same_pre_or_suc)::!ref_pre_or_suc_match_l;
						)
					else ()
	in
()
;;

let find_unmatch t_l1 t_l2 s_cfg1 s_cfg2 =
		 (**first program*)
	
	let () = List.iter(fun (id1,_) -> 
		let ret = try (
			let _ = List.find (fun (m_id1, m_id2, m_rate) -> 
				(id1 = m_id1) 
			) !block_matchings_l 
		  in
				
			true
			)
		with Not_found -> 
			(
				let () = slight_diff s_cfg1 id1  1 in
				(*Printf.printf "cover1 unmatched block: %s\n" (bbid_to_string(id1));*)
				false
			)
		in
		()
		)t_l1 
	in
	
	let slight_ch1 = open_out "./debug/slight1" in
	
	let () = Printf.fprintf slight_ch1 
	"%d blocks are order2,(unmatched, but both predesessor and successor matched)\n"
	(List.length !ref_pre_and_suc_match_l) 
	in
	let () = List.iter(fun (id, pre_id, suc_id, score_same_pre_and_suc) -> 
		Printf.fprintf slight_ch1 "id=%s\tpred=%s\tsucc=%s\tscore=%f\n" 
		(bbid_to_string(id)) 
		(bbid_to_string(pre_id))
		(bbid_to_string(suc_id))
		score_same_pre_and_suc
		) !ref_pre_and_suc_match_l 
	in
	
			let () = Printf.fprintf slight_ch1 
	"%d blocks are order3,(unmatched, but either predesessor and successor matched)\n"
	(List.length !ref_pre_or_suc_match_l) 
	in
	let () = List.iter(fun (id, pre_id, suc_id, score_same_pre_or_suc) -> 
		Printf.fprintf slight_ch1 "id=%s\tpred=%s\tsucc=%s\tscore=%f\n" 
		(bbid_to_string(id)) 
		(bbid_to_string(pre_id))
		(bbid_to_string(suc_id))
		score_same_pre_or_suc
		) !ref_pre_or_suc_match_l 
	in
	
	
	let () = close_out slight_ch1 in
	
	(**second program*)

		ref_pre_and_suc_match_l := [];
		ref_pre_or_suc_match_l := [];

	let () = List.iter(fun (id2,_) -> 
		let ret = try (
			let _ = List.find (fun (x_id1, x_id2, x_score) -> 
				(id2 = x_id2) 
			) !block_matchings_l	in
				
			true
			)
		with Not_found -> 
			(
				let () = slight_diff s_cfg2 id2 2 in
				(*Printf.printf "cover2 unmatched block: %s\n" (bbid_to_string(id2));*)
				false
			)
		in
		()
		)t_l2 
	in
	
	let slight_ch2 = open_out "./debug/slight2" in
	
		let () = Printf.fprintf slight_ch2 
	"%d blocks are order2,(unmatched, but both predesessor and successor matched)\n"
	(List.length !ref_pre_and_suc_match_l) 
	in
	let () = List.iter(fun (id, pre_id, suc_id, score_same_pre_and_suc) -> 
		Printf.fprintf slight_ch2 "id=%s\tpred=%s\tsucc=%s\tscore=%f\n" 
		(bbid_to_string(id)) 
		(bbid_to_string(pre_id))
		(bbid_to_string(suc_id))
		score_same_pre_and_suc
		) !ref_pre_and_suc_match_l 
	in
	
			let () = Printf.fprintf slight_ch2 
	"%d blocks are order3,(unmatched, but either predesessor and successor matched)\n"
	(List.length !ref_pre_or_suc_match_l) 
	in
	let () = List.iter(fun (id, pre_id, suc_id, score_same_pre_or_suc) -> 
		Printf.fprintf slight_ch2 "id=%s\tpred=%s\tsucc=%s\tscore=%f\n" 
		(bbid_to_string(id)) 
		(bbid_to_string(pre_id))
		(bbid_to_string(suc_id))
		score_same_pre_or_suc
		) !ref_pre_or_suc_match_l 
	in
	let () = close_out slight_ch2 in
	(***)
	
()
;;

let match_exist id1  addr=
		(*let match_fun_exist id1 addr =
				let l_exist = try
						(
								let _ = List.find (fun (x_s1,x_e1,_,_) -> ((addr >= x_s1) && (addr <= x_e1)) ) !fun_matchings_l in
								Mutex.lock m_score;
								Hashtbl.add !block_matchings id1 (BB(0), 1.0);
								Mutex.unlock m_score;
								true
						)
					with Not_found ->find_unmatch
						(
							let l_exist2 = try (
								let _ = List.find  (fun (s1,e1,s2, e2) ->
									if (((addr>=s1) && (addr<e1))) then true
									else false
									) !fun_matchings_l in
								true
								)
							with Not_found -> false
							in
							l_exist2
						)
				in
		l_exist
	 in*)
		
		
	let ret = try (
			(*let (f_id2, fast_score) = Hashtbl.find !block_matchings id1 in*)
			let _ = List.find (fun (m_id1,m_id2,m_rate) ->
				if (id1 = m_id1) then true
				 else false  
				) !block_matchings_l in
			true 
		) 
	with Not_found ->
		(
			(*match_fun_exist id1 addr;*)
			false
		)
	in
ret		
;;

(***********************************************************************)
let is_low_addr addr =
	if (addr < 0xb7000000L)
	then true
	else false

(***********************************************************************)
let del_label_tail l_t = 
	let idx = String.rindex l_t '_' in
	let l = String.sub l_t 0 idx in
	l
(***********************************************************************)
let self_label_to_addr (l_t:label) =
	let l = del_label_tail l_t in
  try
    Scanf.sscanf l "pc_0x%Lx" (fun x-> x)
  with
      _ -> 
	raise (VineError "label_to_addr given non address-like label")

(***********************************************************************************)
			
let get_middle_info ida_file1 ida_file2 =
	(*let trace_l1= (Marshal.from_channel tcl_ch: 
	((bbid*int list)*(bbid*int*int*int list)*(bbid*int list)*(bbid*int*int*int list)) ) in*)
	let tcl_ch = open_in ("./middle/"^ida_file1^"_"^"trace.list") in
	let trace_l1= (Marshal.from_channel tcl_ch: (bbid*int) list) in
	let () = close_in tcl_ch in
	
	let tcl_ch = open_in ("./middle/"^ida_file1^"_"^"color.list") in
	let color_l1= (Marshal.from_channel tcl_ch: ((bbid*int*int*int) list)) in
	let () = close_in tcl_ch in
	
	let tcl_ch = open_in ("./middle/"^ida_file2^"_"^"trace.list") in
	let trace_l2= (Marshal.from_channel tcl_ch: (bbid*int) list) in
	let () = close_in tcl_ch in
	
	let tcl_ch = open_in ("./middle/"^ida_file2^"_"^"color.list") in
	let color_l2= (Marshal.from_channel tcl_ch: (bbid*int*int*int) list) in
	let () = close_in tcl_ch in
	
(trace_l1,color_l1,trace_l2,color_l2)
;;

let  matched_tested_uncolor id1 id2 (color1:int) (color2:int)=	
	let tested = try(
		let _ = List.find (fun (test_id1, test_id2) ->
			 if ((test_id1=id1) && (test_id2=id2)) then true
			else
				false
			) !ref_tested_id_pair 
		in
		true
		)
	with Not_found -> 
		(
			false
		)
	in
	
	let matched  = try(
		let _ = List.find (fun (m_id1, m_id2, m_rate) ->
			 if ((m_id1=id1) && (m_id2=id2)) then true
			else
				false
			) !block_matchings_l 
		in
		true
		)
	with Not_found -> 
		(
			false
		) 
	in
	
	let uncolor =  (color1 <> color2) in
	
	if (tested || matched || uncolor) then true
	else false;
;;

let thread_count tid =
	let count = try(
		let orgin_count = Hashtbl.find thread_wait_tbl tid in
		let _ = Hashtbl.replace thread_wait_tbl tid (orgin_count+1) in
		(orgin_count+1)
		) with Not_found -> 
		(
			Hashtbl.add thread_wait_tbl tid 1;
			1
		)
	in 

count
;;
(**********************************sub cmp*************************************************)
let cmp_color_bbs (color_bb_l1: (Vine_cfg.bbid * int * int * int) list) (color_bb_l2: (Vine_cfg.bbid * int * int * int) list) cfg1 cfg2 ida_file1 ida_file2=
		
	let debug_count = ref 0 in
	let id1_debug_count = ref 0 in	
	let id2_debug_count = ref 0 in		
	let has_matched = ref false in
	let tmp_threads_count = ref 0 in
	
	let () = List.iter(fun (id1,color1,t_indx1,c_indx1) -> 
			let () = Printf.printf "\nid1_debug_count=%d  \n" !id1_debug_count in
			id1_debug_count := !id1_debug_count+1;
			id2_debug_count := 0;
			
			(*let addr1 = bb_to_saddr (bb_stmts cfg1 id1) in *)
			
			let () = List.iter (fun (id2,color2,t_indx2,c_indx2) -> 	
							let ret = matched_tested_uncolor id1 id2 color1 color2 in
							let () = match ret with
							| true -> ()
							| false -> 
								
									ref_tested_id_pair := (id1, id2)::!ref_tested_id_pair;	
									let () = Printf.printf "id2_debug_count=%d \n" !id2_debug_count in
									id2_debug_count := !id2_debug_count+1;
																		
									let t_ret = Thread.create 
													thread_blk_diff 
													(id1, id2, (bb_stmts cfg1 id1), (bb_stmts cfg2 id2), true, true, trace_diff_debug_ch,  "log") 
									in
									Thread.delay threads_wait1;
                  tmp_threads_count := !threads_count;			(** FIXME: rafind_unmatchce condition!!!! *)
								
								  let ref_wait_count = ref 0 in
								
									while !tmp_threads_count >= number_of_threads1
                	do 
                  (
										flush stdout;
										let _ = if (!ref_wait_count = 6) then
											(
												let after_match_num = List.length !block_matchings_l in
												(*let () = Printf.printf "s_cfg_cover_list1 len=%d s_cfg_cover_list2 len=%d\n" (List.length s_cfg_cover_list1) (List.length s_cfg_cover_list2) in*)
												let () = Printf.printf "before_match_num=%d,after_match_num=%d\n" !before_match_num after_match_num in
											
												let score_out_ch = (open_out ("middle/"^ida_file1^"_"^ida_file2^".score")) in
												let () = Marshal.to_channel score_out_ch !block_matchings_l [] in
												let () = flush score_out_ch in
												let () = close_out score_out_ch in
												
												let tested_out_ch = (open_out ("middle/"^ida_file1^"_"^ida_file2^".tested")) in
												let () = Marshal.to_channel tested_out_ch !ref_tested_id_pair [] in
												let () = flush tested_out_ch in
												let () = close_out tested_out_ch in
												
												let () = Printf.printf "Thread intercept, result has been written, restart the process\n" in
												()
											)
										in
										
											ref_wait_count := !ref_wait_count +1 ;				
											Printf.printf "---waiting on thread id's:\n";
		                  List.iter (fun x ->
		                    Printf.printf  "%d " (Thread.id x);
												
												(*pm*)
												let repeat_times = thread_count  (Thread.id x) in
												let _ = if (repeat_times > 10) then
													(
														try(
															
															Thread.kill x;
																																																												
															Printf.printf "1-killed thread %d\n" (Thread.id x);
															flush stdout;
															)
														with _  -> 
															(
																
																Printf.printf "1-killed thread %d and safe caught\n" (Thread.id x);
																flush stdout;
															) ;
														
															  
															  threads := List.filter (fun y -> 
															    y <> x
															    ) !threads;
															  threads_count := !threads_count - 1;
															 
													)
												in
												(*pm end*)
												()
		                    ) !threads;
																
                      Thread.delay threads_wait2;
                      tmp_threads_count := !threads_count;		(** FIXME: race condition!!!! *)
                      
                  )
                done;
								(*end false*)
								()
							in
							
						()
			)color_bb_l2
		in
		()
	)color_bb_l1  
	in
	
	let wait_loop = ref 0 in
  while !threads_count > number_of_threads2
  do
    (
			Mutex.lock m_threads;
    	Printf.printf  "waiting\n";
    	List.iter (fun x ->
      Printf.printf "%d " (Thread.id x)
      ) !threads;
    	Printf.printf  "\n---\n%!";
   	 Mutex.unlock m_threads;
		
    Thread.delay threads_wait2
    )
  done
  ;
		()
;;

(*****************************************************************************************)
let cmp_bbs sub_bb_l1 sub_bb_l2 cfg1 cfg2 ida_file1 ida_file2=
		
	let debug_count = ref 0 in
	let id1_debug_count = ref 0 in	
	let id2_debug_count = ref 0 in		
	let has_matched = ref false in
	let tmp_threads_count = ref 0 in
	
	let () = List.iter(fun id1 -> 
			let () = Printf.printf "\nid1_debug_count=%d  \n" !id1_debug_count in
			id1_debug_count := !id1_debug_count+1;
			id2_debug_count := 0;
			
			(*let addr1 = bb_to_saddr (bb_stmts cfg1 id1) in *)

			let () = List.iter(fun id2 -> 	
							let ret = matched_tested_uncolor id1 id2 0 0 in
							let () = match ret with
							| true -> ()
							| false -> 
								
									ref_tested_id_pair := (id1, id2)::!ref_tested_id_pair;	
									let () = Printf.printf "id2_debug_count=%d \n" !id2_debug_count in
									id2_debug_count := !id2_debug_count+1;
																		
									let t_ret = Thread.create 
													thread_blk_diff 
													(id1, id2, (bb_stmts cfg1 id1), (bb_stmts cfg2 id2), true, true, trace_diff_debug_ch,  "log") 
									in
									Thread.delay threads_wait1;
                  tmp_threads_count := !threads_count;			(** FIXME: rafind_unmatchce condition!!!! *)
								
								  let ref_wait_count = ref 0 in
								
									while !tmp_threads_count >= number_of_threads1
                	do 
                  (
										flush stdout;
										let _ = if (!ref_wait_count = 6) then
											(
												let after_match_num = List.length !block_matchings_l in
												(*let () = Printf.printf "s_cfg_cover_list1 len=%d s_cfg_cover_list2 len=%d\n" (List.length s_cfg_cover_list1) (List.length s_cfg_cover_list2) in*)
												let () = Printf.printf "before_match_num=%d,after_match_num=%d\n" !before_match_num after_match_num in
											
												let score_out_ch = (open_out ("middle/"^ida_file1^"_"^ida_file2^".score")) in
												let () = Marshal.to_channel score_out_ch !block_matchings_l [] in
												let () = flush score_out_ch in
												let () = close_out score_out_ch in
												
												let tested_out_ch = (open_out ("middle/"^ida_file1^"_"^ida_file2^".tested")) in
												let () = Marshal.to_channel tested_out_ch !ref_tested_id_pair [] in
												let () = flush tested_out_ch in
												let () = close_out tested_out_ch in
												
												let () = Printf.printf "Thread intercept, result has been written, restart the process\n" in
												()
											)
										in
										
											ref_wait_count := !ref_wait_count +1 ;				
											Printf.printf "---waiting on thread id's:\n";
		                  List.iter (fun x ->
		                    Printf.printf  "%d " (Thread.id x);
												(*pm*)
												let repeat_times = thread_count  (Thread.id x) in
												let _ = if (repeat_times > 10) then
													(
														try(
															
															Thread.kill x;
																																																												
															Printf.printf "2-killed thread %d\n" (Thread.id x);
															flush stdout;
															)
														with _  -> 
															(
																
																Printf.printf "2-killed thread %d and safe caught\n" (Thread.id x);
																flush stdout;
															) ;
														
															  threads := List.filter (fun y -> 
															    y <> x
															    ) !threads;
															  threads_count := !threads_count - 1;
															 
													)
												in
												(*pm end*)
												()
		                    ) !threads;
																
                      Thread.delay threads_wait2;
                      tmp_threads_count := !threads_count;		(** FIXME: race condition!!!! *)
                      
                  )
                done;
								(*end false*)
								()
							in
							
						()
			)sub_bb_l2
		in
		()
	)sub_bb_l1  
	in
	
	let wait_loop = ref 0 in
  while !threads_count > number_of_threads2
  do
    (
			Mutex.lock m_threads;
    	Printf.printf  "waiting\n";
    	List.iter (fun x ->
      Printf.printf "%d " (Thread.id x)
      ) !threads;
    	Printf.printf  "\n---\n%!";
   	 Mutex.unlock m_threads;
		
    Thread.delay threads_wait2
    )
  done
  ;
		
;;

(*****************************************************************************************)
let get_color_indx id c_l seq=
	
	let (_, color, t_indx, c_indx) = try (
		List.find (fun (c_id, c_color, c_t_indx, c_c_indx) -> (c_id=id)) c_l;
		)
	with _ -> 
		(
			let () = Printf.printf "Error: get_color_indx id=%s, seq=%d" (bbid_to_string(id)) seq in 
		(BB(0),0,0,0)	
		) 
	in
(color, t_indx, c_indx)
;;

(*****************************************************************************************)
let get_trace_indx id t_l seq=
	
	let (_, t_indx) = try (
		List.find (fun (t_id,t_t_indx) -> (t_id=id)) t_l;
		)
	with _ -> 
		(
			let () = Printf.printf "Error: get_trace_indx id=%s, seq=%d" (bbid_to_string(id)) seq in
			(BB(0),0)
			) 
	in
t_indx
;;
(*****************************************************************************************)
let is_matched id seq=

	let (matched, m_id1, m_id2, rate) = match seq with
		| 1 ->
			try (
				let (matched_id1, matched_id2, rate) = List.find (fun (m_id1, m_id2, m_rate) -> (m_id1=id)) !block_matchings_l in
				(true,matched_id1, matched_id2, rate)
				)
			with _ -> (false,BB(0), BB(0), 0.0)
		| _ ->
			try (
				let (matched_id1, matched_id2, rate) = List.find (fun (m_id1, m_id2, m_rate) -> (m_id2=id)) !block_matchings_l in
				(true,matched_id1, matched_id2, rate)
				)
			with _ ->	(false,BB(0), BB(0), 0.0)  
	in

(matched, m_id1, m_id2, rate)
;;

(*****************************************************************************************)
let get_color_neighbor indx c_l=
	let (pre_id,pre_color, pre_t_indx, pre_c_indx) = List.nth c_l (indx-1) in
	let (suc_id,suc_color, suc_t_indx, suc_c_indx) = List.nth c_l (indx+1) in
	
(pre_id,pre_t_indx, pre_c_indx,suc_id,suc_t_indx, suc_c_indx)
;;
(***********************************************************************************)
let cmp_sub_bb color_matched_l cfg1 cfg2 ida1 ida2 trace_l1 trace_l2=  
	let f_found = ref false in
	let f_id1 = ref (BB(0)) in
	let f_id2 = ref (BB(0)) in
	
	let () = List.iter (fun (id1,id2,rate, color) -> 
		let () = match !f_found with
			| false ->
				(
						f_id1 := id1;
						f_id2 := id2;
						f_found := true;
				) 
			| true -> 
				(
					let f_t_indx1 = get_trace_indx !f_id1 trace_l1 1 in
					let f_t_indx2 = get_trace_indx !f_id2 trace_l2 2 in
					let c_t_indx1 = get_trace_indx id1 trace_l1 1 in
					let c_t_indx2 = get_trace_indx id2 trace_l2 2 in
					
					let sub_t_l1 = List.filter (fun (t_id, t_t_indx) -> 
						((t_t_indx > f_t_indx1) && (t_t_indx < c_t_indx1)) ) 
						trace_l1 
					in
					
					let sub_t_l2 = List.filter (fun (t_id, t_t_indx) -> 
						((t_t_indx > f_t_indx2) && (t_t_indx < c_t_indx2)) ) 
						trace_l2 
					in
					
					let (sub_l1,_) = (List.split sub_t_l1) in
					let (sub_l2,_) = (List.split sub_t_l2) in
					let () = cmp_bbs sub_l1 sub_l2 cfg1 cfg2 ida1 ida2 in
					
					f_id1 := id1;
					f_id2 := id2;
					()
				)
		in
		()
		) color_matched_l in
		
		let len = List.length color_matched_l in
		let (last_id1, last_id2, _, _) = List.nth  color_matched_l (len-1) in
		let last_c_t_indx1 = get_trace_indx last_id1 trace_l1 1 in
		let last_c_t_indx2 = get_trace_indx last_id2 trace_l2 2 in
		
		let sub_t_l1 = List.filter (fun (t_id, t_t_indx) -> 
						(t_t_indx > last_c_t_indx1))  
						trace_l1 
		in
		
		let sub_t_l2 = List.filter (fun (t_id, t_t_indx) -> 
						(t_t_indx > last_c_t_indx2) ) 
						trace_l2 
		in
()
;;
(***********************************************************************************)
let profile_score ida1 ida2 =
	let score_ch = open_out ("./debug/"^ida1^ida2^"score.log") in 
	let syn_l = List.filter (fun (m_id1, m_id2, m_rate) -> (m_rate=1.0)) !block_matchings_l in
	let () = List.iter(fun (id1,id2,rate) -> 
		Printf.fprintf score_ch "%s %s %f\n" (bbid_to_string(id1)) (bbid_to_string(id2)) rate; 
		) syn_l 
	in
	
	let sem_l = List.filter (fun (m_id1, m_id2, m_rate) -> (m_rate=score_same_stp)) !block_matchings_l in
	let () = List.iter(fun (id1,id2,rate) -> 
		Printf.fprintf score_ch "%s %s %f\n" (bbid_to_string(id1)) (bbid_to_string(id2)) rate; 
		) sem_l 
	in
	
	let color_slight_l = List.filter (fun (m_id1, m_id2, m_rate) -> (m_rate=score_color_slight)) !block_matchings_l in
	let () = List.iter(fun (id1,id2,rate) -> 
		Printf.fprintf score_ch "%s %s %f\n" (bbid_to_string(id1)) (bbid_to_string(id2)) rate; 
		) color_slight_l 
	in
	
	let pre_and_succ_l = List.filter (fun (m_id1, m_id2, m_rate) -> (m_rate=score_same_pre_and_suc)) !block_matchings_l in
	let () = List.iter(fun (id1,id2,rate) -> 
		Printf.fprintf score_ch "%s %s %f\n" (bbid_to_string(id1)) (bbid_to_string(id2)) rate; 
		) pre_and_succ_l 
	in
	
	let pre_or_succ_l = List.filter (fun (m_id1, m_id2, m_rate) -> (m_rate=score_same_pre_or_suc)) !block_matchings_l in
	let () = List.iter(fun (id1,id2,rate) -> 
		Printf.fprintf score_ch "%s %s %f\n" (bbid_to_string(id1)) (bbid_to_string(id2)) rate; 
		) pre_or_succ_l 
	in
	
	let () = Printf.fprintf score_ch "\n\nTotal:\nSyntactic-1.0: %d\n Sematic-0.85: %d\n Color_slight-0.8: %d\n Pre_and_suc-0.7: %d\nPre_or_suc-0.5: %d\n" 
	(List.length(syn_l)) (List.length(sem_l)) (List.length(color_slight_l)) (List.length(pre_and_succ_l)) (List.length(pre_or_succ_l)) in
() 	
;;


(***********************************************************************************)
let trace_cmp ida_file1 ida_file2  dgf_file= 
(
	let () = Printf.printf "enter trace_cmp\n" in
	let tmp_threads_count = ref 0 in
	let matched_id2_tbl = Hashtbl.create 100 in

(**cfg*)
	let (range_tbl1, cfg1) = static_analyze_db ida_file1 in
	let () = print_cfg cfg1 "trace_diff_cfg1" in
	
	let (range_tbl2, cfg2) = static_analyze_db ida_file2 in
	let () = print_cfg cfg2 "trace_diff_cfg2" in
	
	let () = Printf.printf "after static analysis~~~~~~~\n" in
(**read stored record*)
	let ret = try(	
			let score_in_ch = (open_in ("middle/"^ida_file1^"_"^ida_file2^".score")) in
			block_matchings_l := (Marshal.from_channel score_in_ch: (Vine_cfg.bbid*Vine_cfg.bbid*float) list) ;
			let () = close_in score_in_ch in
			true
	)
	with _ -> 
		(

			block_matchings_l := get_blk_match_tbl dgf_file range_tbl1 range_tbl2 ida_file1 ida_file2;
			false
		)
	in

	let () = Printf.printf "before get_middle_info\n " in
(**preprocess*)
	let (trace_l1,color_l1,trace_l2,color_l2) = get_middle_info ida_file1 ida_file2 in
	before_match_num := List.length !block_matchings_l;

(**tested id pair*)
let () = Printf.printf "before test id pair\n " in
	
	let () = try (
		let tested_in_ch = (open_in ("middle/"^ida_file1^"_"^ida_file2^".tested")) in
		ref_tested_id_pair := (Marshal.from_channel tested_in_ch: ((bbid*bbid) list));
		let () = close_in tested_in_ch in
		()
		)
	with _ -> 
		()
	in
	
(**cmp color bb*)
let () = Printf.printf "before cmp_color_bbs\n " in
let () = cmp_color_bbs color_l1 color_l2 cfg1 cfg2 ida_file1 ida_file2 in
(**color bb slight*)

let () = Printf.printf "before color bb slight\n " in
let pre_c = ref (BB(0)) in
let suc_c = ref (BB(0)) in

let cl_len1 = List.length color_l1 in
let () = List.iter(fun (c_id1, c_color1, c_t_indx1, c_c_indx1) ->
	let _ = if ((c_c_indx1 = 0) || (c_c_indx1 = (cl_len1 - 1))) then ()
	else
		(
			let (matched,_,_,_) = is_matched c_id1 1 in
			let () =  match matched with
				| true -> ()
				| false ->
					
						let (pre_id1,pre_t_indx1, pre_c_indx1,suc_id1,suc_t_indx1, suc_c_indx1) = 
							get_color_neighbor c_c_indx1  color_l1
						in
						let (pre_matched, _, m_pre_id2, _) = is_matched pre_id1 1 in
						let (suc_matched, _cmp_color_bbs, m_suc_id2, _) = is_matched suc_id1 1 in
						let _ = if (pre_matched && suc_matched) then
							(
								let (_,_,pre_c_indx2) = get_color_indx m_pre_id2 color_l2 2 in
								let (_,_,suc_c_indx2) = get_color_indx m_suc_id2 color_l2 2 in
								let _ = if (suc_c_indx2 = (pre_c_indx2+2)) then
									(
										let (c_id2,c_color2,_,_) = List.find (fun (_,_,_,c_c_indx2) -> (c_c_indx2=(pre_c_indx2+1))) color_l2 in
										let _ = if (c_color1 = c_color2) then
											(
												block_matchings_l := (c_id1, c_id2, score_color_slight)::!block_matchings_l ;
												()
											)
										else
											()
										in
										()
									)
								else
									()
								in
								()				
							)
						else
							()
						in
					(*end false*)
					
					() 
			in 	
			()
		)	
	in
	()
	) color_l1 
in
(**color bb matched info*)
let color_matched_l = ref [] in
let () = List.iter(fun (c_id1, c_color, c_t_indx, c_c_indx) -> 
	let _ = try(
		let (bb1, bb2, rate) = List.find (fun (m_id1, _, _)-> (m_id1=c_id1)) !block_matchings_l in
		color_matched_l := (bb1,bb2,rate, c_color)::!color_matched_l;
		)
	with Not_found -> ()
	in
	()
	) color_l1 
in

color_matched_l := List.rev !color_matched_l ;
(**cmp sub bb*)

(*let trace_diff_debug_ch = open_out ("./middle/trace_diff.debug") in*)
let () = Printf.fprintf trace_diff_debug_ch "\ncolor_matched_l length: %d\n" (List.length !color_matched_l) in
let () = List.iter(fun (id1, id2, _, color) -> 
	Printf.fprintf trace_diff_debug_ch "color_matched_l: %s %s %d\n" (bbid_to_string(id1)) (bbid_to_string(id2)) color;
	)!color_matched_l in
let  () = flush trace_diff_debug_ch in
(*let () = close_out trace_diff_debug_ch in*)

let () = cmp_sub_bb !color_matched_l cfg1 cfg2 ida_file1 ida_file2 trace_l1 trace_l2 in

	(**output score table for next use*)
	let after_match_num = List.length !block_matchings_l in
	let score_out_ch = (open_out ("middle/"^ida_file1^"_"^ida_file2^".score")) in
	let () = Marshal.to_channel score_out_ch !block_matchings_l [] in
	let () = flush score_out_ch in
	let () = close_out score_out_ch in
	
	let tested_out_ch = (open_out ("middle/"^ida_file1^"_"^ida_file2^".tested")) in
	let () = Marshal.to_channel tested_out_ch !ref_tested_id_pair [] in
	let () = flush tested_out_ch in
	let () = close_out tested_out_ch in
	
	let () = find_unmatch trace_l1 trace_l2 cfg1 cfg2 in
	let () = profile_score ida_file1 ida_file2 in
	let () = Printf.printf "before_match_num=%d,after_match_num=%d\n" !before_match_num after_match_num in
	
	let () = List.iter (fun (id1, id2,rate) ->
		Printf.fprintf trace_diff_debug_ch "block_matching_l: %s %s %f\n" (bbid_to_string(id1)) (bbid_to_string(id2)) rate; 
		) !block_matchings_l in
	
	(**output log*)
	(*let candidate_ch = open_out "./debug/cadindate.log" in
	let () = Marshal.to_channel candidate_ch (s_cfg_cover_list1, s_cfg_cover_list2) [] in
	let () = close_out candidate_ch in**)
	
	
()	
)
in

let main argc argv = 
(
	let ida_file1 = argv.(1) in
	let ida_file2 = argv.(2) in
	
	let dgf_file = "./middle/diff.dgf" in
	let tmp_threads_count = ref 0 in
		
	let () = trace_cmp ida_file1 ida_file2  dgf_file in
	
()
)
in
main (Array.length Sys.argv) Sys.argv;;
close_out trace_diff_debug_ch;;