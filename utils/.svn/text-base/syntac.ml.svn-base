open Vine
open Vine_tovine
open Vine_cfg
open Vine_util
open Exectrace 
open Sqlite3;;

module List = ExtList.List ;;
module String = ExtString.String ;;
(*match table*)

let ref_syntac_blk_matching_l = ref [] ;;
let header_update = ref(true);;
let int_tbl_header = ref([]);;
let int_tbl_rows = ref([]);;

(*********************************************************************)
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

(*******************************************************************)
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

(*********************************************************************)
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
		let in_ir = open_in ("./middle/" ^ ida_file^".ir") in
		let fl = (Marshal.from_channel in_ir: Vine.stmt list) in
		let () = close_in in_ir in
		
		let () = Printf.printf "Before make_cfgs\n" in
 		let cfgs_f = make_cfgs fl in
		let () = Printf.printf "After make_cfgs\n" in
		
 	
		let (flat_f,flat_cfg)= List.hd cfgs_f in

(flat_cfg)
;;
(***************************************************************************)
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

let get_fun_info ida_file=
	let fun_info_l = ref [] in
		(**function db*)
	let db_list = ref [] in
	let sqlite_db_handle = db_open ida_file in
	let query4 = "select start_address, end_address, name from functions" in
	let ret = exec  sqlite_db_handle ~cb:store_tbl  query4 in
	let () = Printf.printf "return = %s~\n" (Sqlite3.Rc.to_string ret) in
	let query_tbl_header4 = !int_tbl_header in
	let query_tbl_rows4 = !int_tbl_rows in
	let () = header_update := true in
	let () = int_tbl_rows := [] in
	
	let () = List.iter (fun r ->  
	let s = Int64.of_string (List.hd r) in
	let e = Int64.of_string (List.hd (List.tl r)) in
	let name = (List.hd (List.tl (List.tl r))) in
	fun_info_l := (s, e, name)::!fun_info_l;
) query_tbl_rows4 in

!fun_info_l
;;

(***********************************************************************************************************)
	let label_is_addr l = 
  try
    let _ = label_to_addr l in
    true
  with
    VineError _ -> 
      false
	;;

(** *)
let del_label_tail l_t = 
	let idx = String.rindex l_t '_' in
	let l = String.sub l_t 0 idx in
	l
;;

(** *)
let self_label_to_addr (l:label) =
	(*let l = del_label_tail l_t in*)
  try
    Scanf.sscanf l "pc_0x%Lx" (fun x-> x)
  with
      _ -> 
	raise (VineError "label_to_addr given non address-like label")
;;
(** *)
let bb_to_saddr sl =
	 
	List.fold_left ( fun acc s ->
					if (acc = Int64.zero) then (
				     		 match s with
				        		| Label l -> 
				                  let is_addr = label_is_addr l in
													let addr = match is_addr with
														| true->
																self_label_to_addr l
														| false -> acc
													in
													addr
										| _ -> acc
						)
						else acc

   ) Int64.zero sl
;;


let bbs_to_addrs bbid_list cfg=
	let bb_addr_l = ref [] in
	let () = List.iter(fun id -> 
			let addr = bb_to_saddr (bb_stmts cfg id) in
			bb_addr_l := (id, addr)::!bb_addr_l;	
		)bbid_list 
	in

!bb_addr_l
;;

(***********************************************************************************************************)
let is_matched id seq=

	let (matched, m_id1, m_id2, rate) = match seq with
		| 1 ->
			let ret = try (
				let (matched_id1, matched_id2, rate) = List.find (fun (m_id1, m_id2, m_rate) -> (m_id1=id)) !ref_syntac_blk_matching_l in
				(true,matched_id1, matched_id2, rate)
				)
			with _ -> (false,BB(0), BB(0), 0.0)
			in
			ret
		| 2 ->
			let ret = try (
				let (matched_id1, matched_id2, rate) = List.find (fun (m_id1, m_id2, m_rate) -> (m_id2=id)) !ref_syntac_blk_matching_l in
				(true,matched_id1, matched_id2, rate)
				)
			with _ ->	(false,BB(0), BB(0), 0.0)
			in
			ret  
	in

(matched, m_id1, m_id2, rate)
;;
(***************************************************************************************************)
let cmp_bb id1 id2 sl1 sl2 = 
		(** @return true when control can flow here from somewhere other than the
    preceding stmt *)
  let rec is_ignored s =
    match s with
    	Comment _ | ExpStmt _ -> true
	| Function _ ->true
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

   
    (* *returns a String list *)
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

	(**entry point*)		
		let (last_s1, blk1, asm1, saddr1) = preprocess_blk sl1 in
	  let (last_s2, blk2, asm2, saddr2) = preprocess_blk sl2 in
	
		let _ = if (asm_same_content asm1 asm2) then (
			ref_syntac_blk_matching_l := (id1, id2, 1.0)::!ref_syntac_blk_matching_l;
			) else () in
()
;;
(***************************************************************************************************)
let  cmp_bbs sub_bbl_1 sub_bbl_2 cfg1 cfg2=
		let () = List.iter (fun id1 ->
				let (matched1,_,_,_) = is_matched id1 1 in
				let () = match matched1 with
					| true -> ()
					| false -> (
							let () = List.iter (fun id2 -> 
											let (matched2,_,_,_) = is_matched id2 2 in
											let () = match matched2 with
												| true -> ()
												| false -> (
															let bb_sl1 = (bb_stmts cfg1 id1) in
															let bb_sl2 = (bb_stmts cfg1 id1) in
															let () = cmp_bb id1 id2 bb_sl1 bb_sl2 in
													()		
													)
											in
								()
								)sub_bbl_2 
						 in
						()	 								
					)
			in
		()
		)sub_bbl_1 
	in
						

()
;;


let main argc argv = 
(
			let ida_file1 = argv.(1) in
			let ida_file2 = argv.(2) in
	
			let flat_cfg1 = static_analyze_db ida_file1 in
			let flat_cfg2 = static_analyze_db ida_file2 in
			
			(*let () = print_cfg flat_cfg1 ida_file1 in
			let () = print_cfg flat_cfg2 ida_file2 in*)
			
			let bbid_l1 = Vine_cfg.cfg_nodes flat_cfg1 in
			let bbid_l2 = Vine_cfg.cfg_nodes flat_cfg2 in
			
			let bb_addr_l1 = bbs_to_addrs bbid_l1 flat_cfg1 in
			let bb_addr_l2 = bbs_to_addrs bbid_l2 flat_cfg2 in
			
			let fun_info_l1 = get_fun_info ida_file1 in
			let fun_info_l2 = get_fun_info ida_file2 in
			
			
			let () = List.iter (fun (s1, e1, name1) ->
				let _ = try (
					let (s2, e2, name2) = List.find (fun (f_s2, f_e2, f_name2) ->
						(f_name2=name1) 
						)  fun_info_l2 
					in
					
					let sub_addr_l1 = List.filter (fun (id1, addr1) -> 
						((addr1 >= s1) && (addr1 <= e1))
						) bb_addr_l1 
					in
					
					let (sub_bb_l1, _) = List.split sub_addr_l1 in
					
					let sub_addr_l2 = List.filter (fun (id2, addr2) -> 
						((addr2 >= s2) && (addr2 <= e2))
						) bb_addr_l2 
					in
					
					let (sub_bb_l2, _) = List.split sub_addr_l2 in
					
					let () = cmp_bbs sub_bb_l1 sub_bb_l2 flat_cfg1 flat_cfg2 in
					
					
					()	
				)
				with Not_found -> ()
				in			
				()
				)fun_info_l1 in
	
	let syntac_ch = open_out ("./middle/"^ida_file1^"_"^ida_file2^".syn") in
	let () = Marshal.to_channel syntac_ch !ref_syntac_blk_matching_l [] in
	let () = flush syntac_ch in
	let () = close_out syntac_ch in
	
	let debug_ch = open_out ("./debug/syntac.debug") in
	let () = Printf.fprintf debug_ch "syntac matched number:%d\n" (List.length !ref_syntac_blk_matching_l) in
	let () = List.iter (fun (id1,id2,rate) -> 
		Printf.fprintf debug_ch "%s %s %f" (bbid_to_string(id1)) (bbid_to_string(id2)) rate;
		)!ref_syntac_blk_matching_l
  in
	(*
	let () = Printf.fprintf debug_ch "block addr info!\n" in
	let () = List.iter (fun (id1,addr1) -> 
		Printf.fprintf debug_ch "%s %Ld\n" (bbid_to_string(id1)) addr1;
		)bb_addr_l1
  in
	
	let () = Printf.fprintf debug_ch "function info!\n" in
	let () = List.iter (fun (s1,e1,name) -> 
		Printf.fprintf debug_ch "%Ld %Ld %s\n" s1 e1 name;
		)fun_info_l1
  in
	*)
	
	let () = flush debug_ch in
	let () = close_out debug_ch in
			
()
)
in
main (Array.length Sys.argv) Sys.argv;;