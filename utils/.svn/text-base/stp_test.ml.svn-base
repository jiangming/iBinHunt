open Vine
open Vine_tovine
open Vine_cfg
open Vine_util
open Exectrace 
open Sqlite3;;

module List = ExtList.List ;;
module String = ExtString.String ;;
(*match table*)

(*let block_matchings = ref (Hashtbl.create 0) ;;*)
let block_matchings_l = ref [] ;;

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

let m_score = Mutex.create ();;
let m_threads = Mutex.create ();;
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
	

flat_cfg
;;


(*****************************************************************************************)
let cmp_bb id1 id2 cfg1 cfg2 ida_file1 ida_file2=
		
	let debug_count = ref 0 in
	let id1_debug_count = ref 0 in	
	let id2_debug_count = ref 0 in		
	let has_matched = ref false in
	let tmp_threads_count = ref 0 in
	
	(*let () = Printf.printf "input pid:\n" in
	flush stdout;
	let pid = Scanf.scanf  "%d" (fun x -> x) in
	let () = Printf.printf "pid=%d\n" pid in*)
	
	let pid = Unix.getpid () in
	let () = Printf.printf "pid=%d\n" pid in
	
		(*
	let ref_line = ref "" in
	let stat_file = Printf.sprintf "/proc/%d/stat\n" pid in
	let stat_ch = open_in stat_file in
	let stat_line  = input_line stat_ch in
	let () = close_in stat_ch in

	flush stdout;
	let pid = Scanf.scanf  "%d" (fun x -> x) in
	
	let () = Printf.printf "stat_line:\n%s\n" stat_line in
	*)
	flush stdout;
	let pid = Scanf.scanf  "%d" (fun x -> x) in
	
	let rec cmp stp_loop = 
			let () = match stp_loop with
				| 0 -> ()
				| _ ->
					 	
									let t_ret = Thread.create 
													thread_blk_diff 
													(id1, id2, (bb_stmts cfg1 id1), (bb_stmts cfg2 id2), true, true, trace_diff_debug_ch,  "log") 
									in
									Thread.delay threads_wait1;

									let () = cmp (stp_loop-1) in
						
					()
			in (*end match*)
			()
	in

	let () = cmp 50000 in


	()	
;;


(***********************************************************************************)
let trace_cmp ida_file1 ida_file2  dgf_file= 
	let () = Printf.printf "enter trace_cmp\n" in
	let tmp_threads_count = ref 0 in
	let matched_id2_tbl = Hashtbl.create 100 in

(**cfg*)
	let cfg1 = static_analyze_db ida_file1 in
	let () = print_cfg cfg1 "trace_diff_cfg1" in
	
	let cfg2 = static_analyze_db ida_file2 in
(**cmp*)
let () = cmp_bb (BB(4971)) (BB(8978)) cfg1 cfg2 ida_file1 ida_file2 in
()
;;
(**************************************************************************)
let main argc argv = 
(
	let ida_file1 = argv.(1) in
	let ida_file2 = argv.(2) in
	
	let dgf_file = "./middle/diff.dgf" in
	let tmp_threads_count = ref 0 in
		
	let () = trace_cmp ida_file1 ida_file2  dgf_file in
	
()
)
;;
main (Array.length Sys.argv) Sys.argv;;
close_out trace_diff_debug_ch;;