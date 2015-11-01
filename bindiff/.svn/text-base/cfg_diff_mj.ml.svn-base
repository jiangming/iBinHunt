open Vine;;
open Vine_cfg;;
open Cg_iso;;
open Cfg_iso;;


exception EARLY_TERMINATE;;


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

let cfg_debug_flag_level1 = false;;(*peng*)
let cfg_debug_flag_level2 = false;;(*peng*)

(** let blk_stp_path = "/home/raistlin/work/vine/bindiff/blk_stp";;*)
(**let blk_stp_path = "/home/jiangming/workspace/vine/bindiff/blk_stp";;*)
let blk_stp_path = "/home/mengpan/bitblaze/vine/bindiff/blk_stp";;

let cfg_stp_queries = ref 0;;
let cfg_testv_calls = ref 0;;
let cfg_stp_true = ref 0;;
let cfg_quick_true = ref 0;;
let cfgdiff_debug_ch = ref stdout ;;

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

let blk_diff sl1 sl2 block_matchings test_type test_stp cfgdiff_debug_ch debug_str =

(** @return true when control can flow here from somewhere other than the
    preceding stmt *)
  let rec is_ignored s =
    match s with
    	Comment _ | ExpStmt _ -> true
	| Function _ -> ( Printf.fprintf cfgdiff_debug_ch "WARNING: found Function in preprocess_blk!!\n"; true  )
  	| Attr(s',_) -> is_ignored s'
  	| _ -> false
  in

  let print_blk str sl1 sl2 =
    Printf.fprintf cfgdiff_debug_ch str;
    Printf.fprintf cfgdiff_debug_ch "--printing statements in block 1\n";
    List.iter (fun s -> Printf.fprintf cfgdiff_debug_ch "%s\n" (stmt_to_string s)
              ) sl1;
    Printf.fprintf cfgdiff_debug_ch "\n";
    Printf.fprintf cfgdiff_debug_ch "--printing statements in block 2\n";
    List.iter (fun s -> Printf.fprintf cfgdiff_debug_ch "%s\n" (stmt_to_string s)
              ) sl2;
    Printf.fprintf cfgdiff_debug_ch "\n";
  in




  let print_asm str asm1 asm2 =
    Printf.fprintf cfgdiff_debug_ch str;
    Printf.fprintf cfgdiff_debug_ch "--printing asm 1\n";
    List.iter (fun s -> Printf.fprintf cfgdiff_debug_ch "%s\n" s
              ) asm1;
    Printf.fprintf cfgdiff_debug_ch "\n";
    Printf.fprintf cfgdiff_debug_ch "--printing asm 2\n";
    List.iter (fun s -> Printf.fprintf cfgdiff_debug_ch "%s\n" s
              ) asm2;
    Printf.fprintf cfgdiff_debug_ch "\n";
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
      Invalid_argument _ -> false
  in


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
      let () = if cfg_debug_flag_level1
	then Printf.fprintf cfgdiff_debug_ch "reg_length1=%d, mem_length1=%d, reg_length2=%d, mem_length2=%d\n" reg_length mem_length (List.length post_reg2) (List.length post_mem2) in
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
      score_same_inst
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
      then score_same_stp
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
  let () = if cfg_debug_flag_level2
    then print_blk "Printing original blocks\n" sl1 sl2
    else ()
  in
  
  let (last_s1, blk1, asm1, saddr1) = preprocess_blk sl1 in
  let (last_s2, blk2, asm2, saddr2) = preprocess_blk sl2 in
  let () = if cfg_debug_flag_level2
    then 
      print_blk "Printing preprocessed blocks\n" blk1 blk2 
    else (
	if cfg_debug_flag_level1 then print_asm "Printing preprocessed asms\n" asm1 asm2
	)
  in
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


let cal_cfg_diff g1 g2 offset block_matchings test_type test_stp debug_str =
  let get_actual_size blk_tbl = 
    Hashtbl.fold (fun id blk acc ->
      if id <> BB(0)
      then acc + 1
      else acc
      ) blk_tbl 0
  in

  let bb_list1 = cfg_nodes g1 in
  let bb_tbl1 = Hashtbl.create (List.length bb_list1) in
  List.iter (fun id ->
	Hashtbl.add bb_tbl1 id (g1#find id);
  ) bb_list1;

  let bb_list2 = cfg_nodes g2 in
  let bb_tbl2 = Hashtbl.create (List.length bb_list2) in
  List.iter (fun id ->
	Hashtbl.add bb_tbl2 id (g2#find id);
  ) bb_list2;

(* *)
let _ = if (cfg_debug_flag_level1) then
	(
		cfgdiff_debug_ch := open_out ("debug/cfgdiff." ^ debug_str);
		()
	)
	else ()
in
		
(* *)
 (* if (cfg_debug_flag_level1) then
   let cfgdiff_debug_ch = open_out ("debug/cfgdiff." ^ debug_str) *)
  let base_size = get_actual_size bb_tbl1 in
  let g_size1 = base_size in
  let g_size2 = get_actual_size bb_tbl2 in
  let (cfg1, cfg2, g_size1, g_size2) = if g_size1 < g_size2
    then (g1, g2, g_size1, g_size2)
    else (g2, g1, g_size2, g_size1)
  in  

  let id2bb_list_cfg1 = ref [] in
  let id2bb_list_cfg2 = ref [] in
  (*let no_fast_block_matchings1 = ref [] in*)
  (*let no_fast_block_matchings2 = ref [] in*)
  let saddr_to_bbid1 = ref (Hashtbl.create g_size1) in
  let saddr_to_bbid2 = ref (Hashtbl.create g_size2) in
  let rev_block_matchings = ref (Hashtbl.create (Hashtbl.length block_matchings)) in

  let bbid_list_cfg1 = cfg_nodes cfg1 in
  let id2bb_tbl_cfg1 = Hashtbl.create (List.length bbid_list_cfg1) in
  let () = List.iter (fun id ->
	let () = Hashtbl.add id2bb_tbl_cfg1 id (cfg1#find id) in
        let () = Hashtbl.add !saddr_to_bbid1 (bb_to_saddr (bb_stmts cfg1 id)) id in
        id2bb_list_cfg1 := (id,cfg1#find id) :: !id2bb_list_cfg1 
  ) bbid_list_cfg1 in
  
  let bbid_list_cfg2 = cfg_nodes cfg2 in
  let id2bb_tbl_cfg2 = Hashtbl.create (List.length bbid_list_cfg2) in
  let () = List.iter (fun id ->
	let () = Hashtbl.add id2bb_tbl_cfg2 id (cfg2#find id) in
        let () = Hashtbl.add !saddr_to_bbid2 (bb_to_saddr (bb_stmts cfg2 id)) id in
        id2bb_list_cfg2 := (id,cfg2#find id) :: !id2bb_list_cfg2
  ) bbid_list_cfg2 in
  (*let () = List.iter (fun id ->
	let () = 
	  try (Hashtbl.add id2bb_tbl_cfg2 id (cfg2#find id))
	  with Failure(int_of_string) -> (Printf.printf "place A\n"; ()) 
	in
        let () = 
	  try (Hashtbl.add !saddr_to_bbid2 (bb_to_saddr (bb_stmts cfg2 id)) id)
	  with Failure(int_of_string) -> (Printf.printf "place B\n"; ())
	in
        id2bb_list_cfg2 := (id,cfg2#find id) :: !id2bb_list_cfg2
  ) bbid_list_cfg2 in*)(*peng*)
  

  let result = if (g_size1 > 0) && (g_size2 > 0)
    then
      (
      let () = if cfg_debug_flag_level1 then Printf.fprintf !cfgdiff_debug_ch "size of cfg1=%d, size of cfg2=%d\n\n" g_size1 g_size2 in


   (*   let () =  no_fast_block_matchings2 := List.map (fun (id2, bb2) ->
	( (bb_to_saddr (bb_stmts cfg2 id2)),bb2)
      ) !id2bb_list_cfg2 in
   *)

      let () = Hashtbl.iter (fun sa1 (sa2, match_score) ->
		Hashtbl.add !rev_block_matchings sa2 (sa1, match_score) 
     ) block_matchings in
 
 
    (*  let () = List.iter (fun (id1, bb1) ->  
	let sa1 = (bb_to_saddr (bb_stmts cfg1 id1)) in
	try  ( 
		let (sa2, score) = Hashtbl.find block_matchings sa1 in
                if score > 0.9999999 
		then (
			let () = Printf.fprintf cfgdiff_debug_ch "Fast matching %s with %s, score=%f.\n" sa1 sa2 score in
			no_fast_block_matchings2 := List.filter (fun (n1,_) ->
				n1 <> sa2
			) !no_fast_block_matchings2
		)
		else (
			Printf.fprintf cfgdiff_debug_ch "block %s not syntactically matched!\n" sa1;
			no_fast_block_matchings1 := (sa1,bb1) :: !no_fast_block_matchings1
		)
	)
	with Not_found -> (
		Printf.fprintf cfgdiff_debug_ch "block %s not syntactically matched!\n" sa1;
		no_fast_block_matchings1 := (sa1,bb1) :: !no_fast_block_matchings1
	)
      ) !id2bb_list_cfg1  in
*)


      let score = Hashtbl.create (g_size1 * g_size2) in


     let () = List.iter (fun (id1, blk1) ->
	let sa1 = (bb_to_saddr (bb_stmts cfg1 id1)) in
	try  ( 
		let (sa2, fast_score) = Hashtbl.find block_matchings sa1 in
                let id2 = Hashtbl.find !saddr_to_bbid2 sa2 in
		if (fast_score > 0.9999999) then (
			let () = if cfg_debug_flag_level1 then Printf.fprintf !cfgdiff_debug_ch "Cfg_diff_score: fast matching blocks %s with %s, score=%f.\n" (Int64.to_string sa1) (Int64.to_string sa2) score_same_inst in
                	Hashtbl.add score (id1, id2) score_same_inst
		)
		else (
			(** do blk_diff of sa1 and sa2 *)
			let test_score = blk_diff (bb_stmts cfg1 id1) (bb_stmts cfg2 id2) block_matchings test_type 
                      		test_stp !cfgdiff_debug_ch debug_str in
			let () = if cfg_debug_flag_level1
			then Printf.fprintf !cfgdiff_debug_ch 
                     		 "--cfg_diff adding score from blk_diff (stp): %f (%s, %s)\n\n" test_score 					(bbid_to_string id1) (bbid_to_string id2)
                    	in
			Hashtbl.add score (id1, id2) test_score
		)
	)
	with Not_found -> (
		let () = if cfg_debug_flag_level1 then Printf.fprintf !cfgdiff_debug_ch 
			"\tCfg_diff_score: %s not fast matched...starting to compare now\n" (Int64.to_string sa1) in
		List.iter (fun c2 -> 
			match c2 with
			| (id2,bb2) -> (		
			    (** do blk_diff of sa1 and sa2 *)
			    let sa2 = (bb_to_saddr (bb_stmts cfg2 id2)) in
			    try ( Hashtbl.find !rev_block_matchings sa2; ())
			    with Not_found -> (
				(** do blk_diff of sa1 and sa2 *)
                        	(*let id2 = Hashtbl.find !saddr_to_bbid2 sa2 in*)
				let test_score = blk_diff (bb_stmts cfg1 id1) (bb_stmts cfg2 id2) 
					block_matchings test_type test_stp !cfgdiff_debug_ch debug_str in
				let () = if cfg_debug_flag_level1
				then Printf.fprintf !cfgdiff_debug_ch 
                     			 "--cfg_diff adding score from blk_diff (stp): %f (%s, %s)\n\n" test_score 						(bbid_to_string id1) (bbid_to_string id2)
                    		in
				Hashtbl.add score (id1, id2) test_score
			    )
                        )
		) !id2bb_list_cfg2
	     )
   ) !id2bb_list_cfg1 in

(*
  let () = if ( (List.length !no_fast_block_matchings1) > 0 && (List.length !no_fast_block_matchings2) > 0 ) then

  List.iter (fun c1 ->  (*iterating over no_fast_matchings1 *)
    match c1 with
	| (id1,bb1) -> ( 
           if id1 not matched (
	   	List.iter (fun c2 -> 
			match c2 with
			| (id2,bb2) -> (		

			    let sa2 = (bb_to_saddr (bb_stmts cfg2 id2)) in
			    try ( Hashtbl.find !rev_block_matchings sa2; ())
			    with Not_found -> (
				(** do blk_diff of sa1 and sa2 *)
 			        let sa1 = (bb_to_saddr (bb_stmts cfg1 id1)) in
				let test_score = blk_diff (bb_stmts cfg1 id1) (bb_stmts cfg2 id2) 
					block_matchings test_type test_stp !cfgdiff_debug_ch debug_str in
				let () = if cfg_debug_flag_level1
				then Printf.fprintf !cfgdiff_debug_ch 
                     			 "--cfg_diff adding score from blk_diff (stp): %f (%s, %s)\n\n" test_score 						(bbid_to_string id1) (bbid_to_string id2)
                    		in
				Hashtbl.add score (id1, id2) test_score
			    )
			)
		)
	     )
	  )  !id2bb_list_cfg1
	)
    )  !id2bb_list_cfg2
  in
*)

      let () = if cfg_debug_flag_level1 then Printf.fprintf !cfgdiff_debug_ch "starting isomorphism\n\n" in
      let (iso_ret, iso_size, iso_score, iso_result) = if g_size1 > 90000000
        then Cfg_iso.isomorphism_accurate cfg1 cfg2 g_size1 (Hashtbl.create g_size1) 
          score init_max_size_ratio_cg init_max_score_ratio_cg 
          timeout_length_cg1 timeout_length_cg2 timeout_count_cg1
          timeout_count_cg2 !cfgdiff_debug_ch false
        else Cfg_iso.isomorphism cfg1 cfg2 g_size1 (Hashtbl.create g_size1) score 
          init_max_size_ratio_cfg1 init_max_score_ratio_cfg timeout_length_cfg 
          timeout_count_cfg !cfgdiff_debug_ch false
      in
      let (ret_size, ret_score) = (
        let (tmp_size, tmp_score) = 
          ((float_of_int iso_size) /. (float_of_int base_size), 
            iso_score /. (float_of_int base_size))
        in
        if iso_ret
        then (tmp_size, tmp_score)
        else (max tmp_size score_timeout, max tmp_score score_timeout)
        )
      in
      let ret = 
        if ret_size > init_max_size_ratio_cfg2 && 
          ret_score > init_max_score_ratio_cfg 
        then final_size_ratio1 *. ret_size +. final_score_ratio *. ret_score 
          +. offset -. final_size_ratio2 *. float_of_int (g_size2 - g_size1) 
          /. float_of_int base_size
        else 0.0
      in
     let () = if cfg_debug_flag_level1 then
      Printf.fprintf !cfgdiff_debug_ch 
        "***result_size: (%d,%f), result_score: (%f,%f), ret: %f\n\n" 
        iso_size ret_size iso_score ret_score ret
     in
      ret
      )
    else
      (
      Printf.fprintf !cfgdiff_debug_ch "***empty\n\n";
      if g_size1 = g_size2 
      then score_empty +. offset
      else score_diff +. offset
      )
  in

let _ = if (cfg_debug_flag_level1) then
	(
		  close_out !cfgdiff_debug_ch;
		()
	)
	else ()
in

  (result,!cfg_stp_queries, !cfg_testv_calls, !cfg_stp_true, !cfg_quick_true )
;;
