open Vine;;
open Vine_tovine;;
open Vine_cfg;;
open Cg_iso;;
open Cfg_iso;;
open Cfg_diff;;
open Mycg;;

exception EARLY_TERMINATE;;

let thread_wait_tbl = (Hashtbl.create 1024) ;;
let number_of_threads1 = 2;;
let threads_wait1 = 0.01;;
let threads_wait2 = 5.0;;

let use_hybridization = true;;(*peng*)

let score_func_same_inst = 1.0;;


let cfg_diff_test_type = true;;(*peng*)
let cfg_diff_test_stp = true;;


let debug_flag = true;;(*peng*)
let toplevel_debug_ch = ref (open_out "debug/debug.toplevel");;
let initscore_debug_ch = ref (open_out "debug/debug.initscore");;
let cfgprint_debug_ch = ref (open_out "debug/debug.cfgprint");;
let debug_ch = ref (open_out "debug/debug.other");;

let stats_debug_ch = ref (open_out "debug/stats");;

let input_file1 = ref "";;
let input_file2 = ref "";;
let input_file3 = ref "";;
let input_file4 = ref "";;


let sum_stp_queries = ref 0;;
let sum_testv_calls = ref 0;;
let sum_stp_true = ref 0;;
let sum_quick_true = ref 0;;

let no_fast_matchings1 = ref([]);;
let no_fast_matchings2 = ref([]);;

(*let m_score = Mutex.create ();;
let m_threads = Mutex.create ();;
let m_stats = Mutex.create ();;*)(*pm commment*)


let m_threads = Mutex.create ();;
let m_score= m_threads;;
let m_stats= m_threads;;

let threads_count = ref 0;;
let threads = ref [];;



let process_block_name n name2saddr_tbl =
	if ( String.contains n '_')
	then (
		let right_index = String.rindex n '_' in
		String.uppercase (String.sub n (right_index + 1) ((String.length n) - right_index - 1))
	)
	else (
	try String.uppercase (Int64.to_string (Hashtbl.find name2saddr_tbl n))
	with Not_found -> "INVALID"
	)



;;

let get_asm sl = List.fold_left (fun acc s ->
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
;;


(* returns a string to string list Hashtbl
  specifically, function name -> list of assembly instructions
*)
let create_name2asm_tbl fun_list =
	let name2asm_tbl = Hashtbl.create (List.length fun_list) in
	let () = List.iter (fun  f -> match f with
		| Function(n,_,_,_,Some(Block(bdl,bsl))) ->  
			Hashtbl.add name2asm_tbl n (get_asm bsl)

		| _ -> ()
	) fun_list in
	name2asm_tbl
;;

let cfg_to_dot cfg1 file_append =

     let cfgdot_ch = open_out ("debug/cfg." ^ file_append ^ ".dot") in
     let g = ref (G.empty) in
     let vertex_id = ref 0 in 
     let cg_int_tbl = Hashtbl.create cfg1#length in

        let () = cfg1#iter_bb (fun bb ->
        
     	let id = !vertex_id in 
        let name = bbid_to_string (cfg1#get_id bb) in
        let sl = cfg1#get_info bb in
	let s = Block([],sl) in
      	let v = G.V.create (id,name,s) in 
        let () = Hashtbl.add cg_int_tbl name v in
      	let () = g := G.add_vertex !g v in
     	vertex_id := !vertex_id + 1

    ) in

     let () = cfg1#iter_edges (fun u1 v1 ->
	  let u2 = Hashtbl.find cg_int_tbl (bbid_to_string (cfg1#get_id u1)) in
	  let v2 = Hashtbl.find cg_int_tbl (bbid_to_string (cfg1#get_id v1)) in
	  g := G.add_edge !g u2 v2 

     ) in

     Dot.output_graph cfgdot_ch !g
;;


let print_cfgs cfgs_list file_append =
 let counter = ref 0 in
 List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
    if n = "HttpFilterProc" then cfg_to_dot current_cfg file_append;
    
    let bbid_list = cfg_nodes current_cfg in
    let () = Printf.fprintf !cfgprint_debug_ch "\nProcessing cfg # %d corresponding to function %s. " !counter n  in
    let () = Printf.fprintf !cfgprint_debug_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
    let () = Printf.fprintf !cfgprint_debug_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
    let () = List.iter (fun bblock_id ->
    	let () = Printf.fprintf !cfgprint_debug_ch "\t Looking at basic block id %s\n" (bbid_to_string bblock_id) in
	let block_pred_list = bb_pred current_cfg bblock_id in
	let block_succ_list = bb_succ current_cfg bblock_id in
	let () = Printf.fprintf !cfgprint_debug_ch "\t\t Predecessors: " in
	let () = List.iter (fun b_id ->
	        Printf.fprintf !cfgprint_debug_ch "%s " (bbid_to_string b_id)
	) block_pred_list in
	let () = Printf.fprintf !cfgprint_debug_ch "\n\t\t Successors: " in
	let () = List.iter (fun b_id ->
	        Printf.fprintf !cfgprint_debug_ch "%s " (bbid_to_string b_id)
	) block_succ_list in
	let sl = current_cfg#get_info (current_cfg#find bblock_id) in
	let asm = List.fold_left (fun acc s ->
     		 match s with
     		   | Comment str -> (
         	  	 let col_pos = (
          	   		try String.index str ':'
           	   		with
               	 			Not_found -> -1
           	   		) + 1
           	 	in
            		acc ^ "\n" ^ (String.sub str col_pos (String.length str - col_pos)) 
            		)
        	| _ -> acc
      	) "" sl in

	Printf.fprintf !cfgprint_debug_ch "\n\t\t Assembly:\n%s\n" asm 
	
	(*let statement_list = current_cfg#get_info (current_cfg#find bblock_id) in
	List.iter (fun s -> match s with
		| Comment(comment_str) -> Printf.fprintf !cfgprint_debug_ch "\t\t\t%s\n" comment_str
		(*| _ -> () *)
		| _ -> Printf.fprintf !cfgprint_debug_ch "\t\t\t%s\n" (stmt_to_string s)
	) statement_list *)
    ) bbid_list in
    counter := !counter + 1 
 ) cfgs_list
;;


(*
make cfgs from a function list
return List(Function(..) * cfg)
@param function_l: List(Function(...))
*)
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
          let () = coalesce_bb g in 
          (* let () = Printf.printf "size of cfg = %d\n" (cfg_numnodes g) in *)
	  (f,g) :: acc
          )
    ) [] function_l
  in
  List.sort (fun (Function(_, _, _, _, _), g1) (Function(_, _, _, _, _), g2) ->
    let s1 = g1#length in
    let s2 = g2#length in
    if s1 = s2
    then 0
    else
      (
      if s1 > s2   (* sort in decreasing order *)
      then -1
      else 1
      )
    ) cfgs
;;


(*
returns Hashtbl of function pairings to assembly score
@param asmtbl1, asmtbl2: Hashtbl of function name (string) -> assembly instructions (string list)
*)
let create_asm_mappings asmtbl1 asmtbl2 =
  let asm_mapped_tbl = Hashtbl.create ((Hashtbl.length asmtbl1) * (Hashtbl.length asmtbl2)) in
  let () = Hashtbl.iter (fun n1 asm1 ->
      let map_list = Hashtbl.fold (fun n2 asm2 acc ->
          if asm1 = asm2 then n2 :: acc else acc 
	  
      ) asmtbl2 []
      in
      Hashtbl.add asm_mapped_tbl n1 map_list
  ) asmtbl1 in
  asm_mapped_tbl
  
;;  


(*
find mappings by comparing assembly instructions
return Hashtbl(function name1, function name2)
  two functions are added to the table if they have the same assembly 
  instructions
@param asmtbl1, asmtbl2: Hashtbl(function info, assembly instruction list)
*)
let match_inst asmtbl1 asmtbl2 =
  let size = max (Hashtbl.length asmtbl1) (Hashtbl.length asmtbl2) in
  let acc = Hashtbl.create size in
  Hashtbl.iter (fun f1 inst1 ->
    Hashtbl.iter (fun f2 inst2 ->
      if inst1 = inst2 && f1.name <> unknown_addrs_function.name && 
        f2.name <> unknown_addrs_function.name 
      then Hashtbl.add acc f1.name f2.name
      ) asmtbl2
    ) asmtbl1; 
  Printf.printf "%d pairs of functions matched\n" (Hashtbl.length acc);
  acc
;;


(*
obtain node id in the cg from function name
@param name: function name
@param tbl: Hashtbl(function name, node id in cg)
*)
let get_id_from_name name tbl =
  try Hashtbl.find tbl name 
  with
    Not_found -> 0
;;


(*
obtain function name from node id in the cg
@param id: node id in a cg
@param tbl: Hashtbl(function name, node id in cg)
*)
let get_name_from_id id tbl = 
  Hashtbl.fold (fun name1 id1 acc ->
    if id1 = id 
    then name1
    else acc
  ) tbl ""
;;


(*
find mappings by comparing assembly instructions
return Hashtbl((node id for function1, node id for function2), score
  two functions are added to the table if function2 is the only function in
  program2 that has the same assembly instruction as function1;
@param matched_asm_inst: Hashtbl(function name1, function name2)
  this table contains all functions pairs that have the same assembly 
  instructions
@param tbl1, tbl2: Hashtbl(function name, node id in cg)
*)
let match_inst_name matched_asm_inst tbl1 tbl2 =
  let acc = Hashtbl.create (Hashtbl.length matched_asm_inst) in
  Hashtbl.iter (fun n1 n2 ->
    let count1 = ref 0 in
    let count2 = ref 0 in
    let () = try Hashtbl.iter (fun x1 x2 ->
        if n1 = x1 
        then count1 := !count1 + 1;
        if n2 = x2 
        then count2 := !count2 + 1;
        if !count1 > 1 || !count2 > 1 
        then raise EARLY_TERMINATE
        ) matched_asm_inst 
      with
        EARLY_TERMINATE -> ()
    in
    if !count1 = 1 && !count2 = 1
    then 
      (
      let id1 = get_id_from_name n1 tbl1 in
      let id2 = get_id_from_name n2 tbl2 in
      if n1 = n2 
      then Hashtbl.add acc (id1, id2) (score_same_inst +. score_same_name)
      else Hashtbl.add acc (id1, id2) score_same_inst
      )
    ) matched_asm_inst;
  Printf.printf "%d pairs of functions matched\n\n" (Hashtbl.length acc);
  acc
;;

(*pm: g1, g2: CFG of two functions. id1, id2: id of the functions in CG*)
let threaded_add_score (g1, g2, id1, id2, score, offset, block_matchings) =
  let t_self = Thread.self () in
	
	(*Printf.printf "threaded_add_score: 1-before mutex %d\n" (Thread.id t_self);
	flush stdout;*)
	
  let () = Mutex.lock m_threads in
	
	(*Printf.printf "threaded_add_score: 1-in mutex %d\n" (Thread.id t_self);
	flush stdout;*)
	
  let () = threads := t_self :: !threads in
  let () = threads_count := !threads_count + 1 in
  let () = Mutex.unlock m_threads in
	
	(*Printf.printf "threaded_add_score: 1-Exit mutex %d\n" (Thread.id t_self);
	flush stdout;*)
	
	(*Printf.fprintf !initscore_debug_ch "enter thread %d, before cal_cfg_diff " (Thread.id (Thread.self ()));*)
  let (ret,stp_count,testv_count,stp_true,quick_true) = Cfg_diff.cal_cfg_diff g1 g2 offset block_matchings cfg_diff_test_type cfg_diff_test_stp ((string_of_int id1) ^ "."  ^ (string_of_int id2))
  in
	(*Printf.fprintf !initscore_debug_ch "enter thread %d, after cal_cfg_diff " (Thread.id (Thread.self ()));*)
  (*let (ret,stp_count,testv_count,stp_true,quick_true) = 
    try (Cfg_diff.cal_cfg_diff g1 g2 offset block_matchings cfg_diff_test_type cfg_diff_test_stp ((string_of_int id1) ^ "."  ^ (string_of_int id2)))
    with Failure(int_of_string) -> (Printf.printf "!\n"; (0.1,1,1,1,1)) (*peng*)
  in*)
  (*let () = Printf.printf "in threaded_add_score, %s\n" ((string_of_int id1) ^ "."  ^ (string_of_int id2)) in(*peng*)*)
  (*Printf.printf "threaded_add_score: 2-before mutex %d\n" (Thread.id t_self);
	flush stdout;*)
	
	Mutex.lock m_score;
	
	(*Printf.printf "threaded_add_score: 2-in mutex %d\n" (Thread.id t_self);
	flush stdout;*)
  Hashtbl.add score (id1, id2) ret;
  Mutex.unlock m_score;
		(*Printf.printf "threaded_add_score: 2-Exit mutex %d\n" (Thread.id t_self);
	flush stdout;*)
  (*Printf.printf "Received from cal_cfg_diff: stp_queries=%d, testv_calls=%d, stp_true=%d, quick_true=%d\n" stp_count testv_count stp_true quick_true; *)
  
	(*Printf.printf "threaded_add_score: 3-before mutex %d\n" (Thread.id t_self);
	flush stdout;*)
	
	Mutex.lock m_stats;
	(*Printf.printf "threaded_add_score: 3-in mutex %d\n" (Thread.id t_self);
	flush stdout;*)
  sum_stp_queries := stp_count;
  sum_testv_calls := testv_count;
  sum_stp_true := stp_true;
  sum_quick_true := quick_true;
  Mutex.unlock m_stats;
	(*Printf.printf "threaded_add_score: 3-exit mutex %d\n" (Thread.id t_self);
	flush stdout;*)
  
	(*Printf.printf "threaded_add_score: 4-before mutex %d\n" (Thread.id t_self);
	flush stdout;*)
	Mutex.lock m_threads;
	(*Printf.printf "threaded_add_score: 4-in mutex %d\n" (Thread.id t_self);
	flush stdout;*)
  Printf.fprintf !debug_ch "joining %d\n" (Thread.id t_self);
  threads := List.filter (fun x -> 
    x <> t_self
    ) !threads;
  threads_count := !threads_count - 1;
  Mutex.unlock m_threads;
	(*Printf.printf "threaded_add_score: 4-exit mutex %d\n" (Thread.id t_self);
	flush stdout;*)
	
	(*let () = Printf.printf "Exit threaded_add_score, %s\n" ((string_of_int id1) ^ "."  ^ (string_of_int id2)) in(*pm*)*)
	()
;;


let non_threaded_add_score id1 id2 score value =
  Mutex.lock m_score;
  Hashtbl.add score (id1, id2) value;
  Mutex.unlock m_score
;;
(*
let kill_proc tid =
		let _ = try (
			let pid = Hashtbl.find tid_pid_tbl tid in 
			(*Unix.execv "kill" [|"-9 ";(string_of_int(pid))|];*)
			Unix.system ("kill -9 "^(string_of_int(pid)));
			Hashtbl.remove tid_pid_tbl tid;
			Printf.printf "tid:%d , pid:%d killed\n" tid pid;	
			) with Not_found -> 
			(
				Printf.printf "kill_proc: tid:%d , no pid found\n" tid;
			)
		in
()
;;
*)
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
(*
initialize the score table which records the score for each function pairs
return Hashtbl((node id for function1, node id for function2), score)
@param cfgs1 cfgs2: List(Function(), cfg)
@param tbl1 tbl2: Hashtbl(function name, node id in cg)
@param asmtbl1 asmtbl2: Hashtbl(function name, string list of assembly instructions)
*)
let init_cg_score cfgs1 cfgs2 tbl1 tbl2 asmtbl1 asmtbl2 fast_matchings block_matchings  =
  if use_hybridization then (

  let size1 = List.length cfgs1 in
  let size2 = List.length cfgs2 in
 let done1 = ref 0 in
  let done2 = ref 0 in
  
  let score = Hashtbl.create (size1 * size2) in
  let tmp_threads_count = ref 0 in

  let same_asm_table = create_asm_mappings asmtbl1 asmtbl2  in
(*pm*)
(*
	let () = List.iter (fun c1 -> match c1 with
      | (Function(n1,_,_,_,_),g1) -> 
				Printf.fprintf !initscore_debug_ch "CFGS1: function name: %s\n" n1;
  )cfgs1
	in
	
	let () = List.iter (fun c2 -> match c2 with
      | (Function(n2,_,_,_,_),g2) -> 
				Printf.fprintf !initscore_debug_ch "CFGS2: function name: %s\n" n2;
  )cfgs2
	in
	
	*)
(*pme end*)
	let () = List.iter (fun c1 -> match c1 with
        | (Function(n1,_,_,_,_),g1) -> (*pm: n1: function name, g1: cfg of function n1*)
   
	try  ( 
		let (n2, fast_score) = Hashtbl.find fast_matchings n1 in
		done1 := !done1 + 1;
     done2 := 0;
		
		if (fast_score > 0.9999999) then (
			let () = Printf.fprintf !initscore_debug_ch "Init_cg_score: fast matching %s with %s, score=%f.\n" n1 n2 score_same_inst in
                	let id1 = get_id_from_name n1 tbl1 in
                	let id2 = get_id_from_name n2 tbl2 in
                	non_threaded_add_score id1 id2 score score_same_inst
		)
		else (
			let (_,g2) = List.hd ( 
				List.filter ( fun (f,g) -> match f with
					Function(n3,_,_,_,_) -> n2=n3	
				) cfgs2  
			) in
                	let id1 = get_id_from_name n1 tbl1 in
                	let id2 = get_id_from_name n2 tbl2 in
			let new_thread = if n1 = n2
                        then Thread.create threaded_add_score (g1, g2, id1, id2, score, score_same_name, block_matchings)
                        else Thread.create threaded_add_score (g1, g2, id1, id2, score, 0.0, block_matchings)
			in
                    	Thread.delay threads_wait1;
			Printf.fprintf !initscore_debug_ch 
                      "new thread %d: comparing function %s from %s (fun_id=%d) with function %s from %s (fun_id=%d)\n\tprogress %d/%d; %d/%d\n%!" 
			(Thread.id new_thread) n1 !input_file1 id1 
			 n2 !input_file2  id2 !done1 size1 !done2 size2;
                    Mutex.lock m_threads;
                    tmp_threads_count := !threads_count;			(** FIXME: race condition!!!! *)
                    Mutex.unlock m_threads;
                    while !tmp_threads_count >= number_of_threads1
                    do 
                      (
                      Printf.fprintf !initscore_debug_ch "---waiting on thread id's:\n";
                      Mutex.lock m_threads;
                      List.iter (fun x ->
												
													(*pm*)
												(*let repeat_times = thread_count  (Thread.id x) in
												let _ = if (repeat_times > 4) then
													(
														kill_proc (Thread.id x) 
													)
												in*)
												
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
														
															  Printf.fprintf !debug_ch "joining %d\n" (Thread.id x);
															  threads := List.filter (fun y -> 
															    y <> x
															    ) !threads;
															  threads_count := !threads_count - 1;
															 
													)
												in
												(*pm end*)
												
                        Printf.fprintf !initscore_debug_ch "%d " (Thread.id x);
                        ) !threads;
                      Mutex.unlock m_threads;
											
                      Printf.fprintf !initscore_debug_ch "\n---\n%!";
                      Thread.delay threads_wait2;
                      Mutex.lock m_threads;
                      tmp_threads_count := !threads_count;		(** FIXME: race condition!!!! *)
                      Mutex.unlock m_threads
                      )
                    done;
										
										(*pm*)
										Hashtbl.clear thread_wait_tbl;
										(*pm end*)
		)
	)
	with Not_found -> (
		Printf.fprintf !initscore_debug_ch "\tInit_cg_score: %s not fast matched, might compare in later round.\n" n1;
	)
   ) cfgs1 in

	
  let () = if ( (List.length !no_fast_matchings1) > 0 && (List.length !no_fast_matchings2) > 0 ) then List.iter (fun c1 -> 
		done1 := !done1+1;
		done2 := 0;
    match c1 with
	| (n1,None,_) -> ( 
	   List.iter (fun c2 -> 
		match c2 with
		| (n2,None,_) -> (		(** match two external functions, score FIXME  *)
			let id1 = get_id_from_name n1 tbl1 in
			let id2 = get_id_from_name n2 tbl2 in
			if n1 = n2 
			then non_threaded_add_score id1 id2 score score_empty_and_same_name
			else non_threaded_add_score id1 id2 score score_empty
		)
		| (n2,Some(s),_) -> (		(* match external in cg1 with internal in cg2, score=0 *)
			let id1 = get_id_from_name n1 tbl1 in
			let id2 = get_id_from_name n2 tbl2 in
			non_threaded_add_score id1 id2 score score_diff
		)
	  ) !no_fast_matchings2
	)
	| (n1,Some(s),g1) -> (
          let id1 = get_id_from_name n1 tbl1 in

	  let bb_list_g1 = cfg_nodes g1 in
	  let bb_tbl_g1 = Hashtbl.create (List.length bb_list_g1) in
	  List.iter (fun id ->
		Hashtbl.add bb_tbl_g1 id (g1#find id);
	  ) bb_list_g1;

          List.iter (fun c2 ->
            done2 := !done2 + 1;
            match c2 with
              | (n2,None,_) -> (	(* match internal in cg1 with external in cg2, score=0 *)
                  let id2 = get_id_from_name n2 tbl2 in
                  non_threaded_add_score id1 id2 score score_diff
                )
              | (n2,Some(s),g2) -> (		(* match two internal functions *)
		    let id2 = get_id_from_name n2 tbl2 in
		    let bb_list_g2 = cfg_nodes g2 in
		    let bb_tbl_g2 = Hashtbl.create (List.length bb_list_g2) in
		    List.iter (fun id ->
			Hashtbl.add bb_tbl_g2 id (g2#find id);
		    ) bb_list_g2;
		    let new_thread = if n1 = n2
			then Thread.create threaded_add_score 
                          (g1, g2, id1, id2, score, score_same_name, block_matchings)
			else Thread.create threaded_add_score 
                          (g1, g2, id1, id2, score, 0.0, block_matchings)
		    in
                    Thread.delay threads_wait1;
                    Printf.fprintf !initscore_debug_ch 
                      "*peng* new thread %d: comparing function %s from %s (fun_id=%d, bb_count=%d) with function %s from %s (fun_id=%d, bb_count=%d)\n\tprogress %d/%d; %d/%d\n%!" 
                      (Thread.id new_thread) n1 !input_file1 id1 
                      (Hashtbl.length bb_tbl_g1) n2 !input_file2  id2 
                      (Hashtbl.length bb_tbl_g2) !done1 size1 !done2 size2;
                    Mutex.lock m_threads;
                    tmp_threads_count := !threads_count;			(** FIXME: race condition!!!! *)
                    Mutex.unlock m_threads;
                    while !tmp_threads_count >= number_of_threads1
                    do 
                      (
                      Printf.fprintf !initscore_debug_ch "---waiting on thread id's:\n";
                      Mutex.lock m_threads;
                      List.iter (fun x ->
					
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
															
															  Printf.fprintf !debug_ch "joining %d\n" (Thread.id x);
															  threads := List.filter (fun y -> 
															    y <> x
															    ) !threads;
															  threads_count := !threads_count - 1;
															 
													)
												in
												(*pm end*)
												Printf.fprintf !initscore_debug_ch "%d " (Thread.id x);
												
                        ) !threads;
                      Mutex.unlock m_threads;
                      Printf.fprintf !initscore_debug_ch "\n---\n%!";
                      Thread.delay threads_wait2;
                      Mutex.lock m_threads;
                      tmp_threads_count := !threads_count;		(** FIXME: race condition!!!! *)
                      Mutex.unlock m_threads
                      )
                    done;
										
										(*pm*)
										Hashtbl.clear thread_wait_tbl;
										(*pm end*)
                 )

            ) !no_fast_matchings2  (* end List.iter of cfgs2 *)
          )
    ) !no_fast_matchings1
  in
  while !threads_count > 0
  do
    (
    Mutex.lock m_threads;
    Printf.fprintf !initscore_debug_ch "waiting\n";
    List.iter (fun x ->
			(*pm*)
			let repeat_times = thread_count  (Thread.id x) in
			let _ = if (repeat_times > 10) then
				(
					try(
						
						Thread.kill x;				
						
						Printf.printf "3-killed thread %d\n" (Thread.id x);
						flush stdout;
						)
					with _  -> 
						(
							
							Printf.printf "3-killed thread %d and safe caught\n" (Thread.id x);
						flush stdout;
						) ;
					
					  Printf.fprintf !debug_ch "joining %d\n" (Thread.id x);
					  threads := List.filter (fun y -> 
					    y <> x
					    ) !threads;
					  threads_count := !threads_count - 1;
					
						
				)
			in
			(*pm end*)
      Printf.fprintf !initscore_debug_ch "%d " (Thread.id x)
      ) !threads;
    Printf.fprintf !initscore_debug_ch "\n---\n%!";
    Mutex.unlock m_threads;
    Thread.delay threads_wait2
    )
  done 
  ;
  (size1, size2, score)
  )


  else (

let size1 = List.length cfgs1 in
  let size2 = List.length cfgs2 in
  let done1 = ref 0 in
  let done2 = ref 0 in
  let score = Hashtbl.create (size1 * size2) in
  let tmp_threads_count = ref 0 in

  let same_asm_table = create_asm_mappings asmtbl1 asmtbl2  in

  let () = Printf.printf "Printing same assembly table, length=%d:\n" (Hashtbl.length same_asm_table) in
  let () = Hashtbl.iter (fun n sl ->
	Printf.printf "\tMatched with %s:" n;
	List.iter (fun s ->
		Printf.printf "\t%s" s
	) sl;
	Printf.printf "\n"
  ) same_asm_table in
  let () = flush stdout in

  List.iter (fun c1 ->
    done1 := !done1 + 1;
    done2 := 0;
    match c1 with
      | (Function(n1,_,_,_,None),_) -> List.iter (fun c2 -> 
          match c2 with
            | (Function(n2,_,_,_,None),_) -> (
                let id1 = get_id_from_name n1 tbl1 in
                let id2 = get_id_from_name n2 tbl2 in
                if n1 = n2 
                then non_threaded_add_score id1 id2 score 
                  (score_empty +. score_same_name)
                else non_threaded_add_score id1 id2 score score_empty
              )
            | (Function(n2,_,_,_,_),g2) -> (
                let id1 = get_id_from_name n1 tbl1 in
                let id2 = get_id_from_name n2 tbl2 in
                non_threaded_add_score id1 id2 score score_diff
              )
            | _ -> ()
          ) cfgs2
      | (Function(n1,_,_,_,_),g1) -> (
          let id1 = get_id_from_name n1 tbl1 in

	  let bb_list_g1 = cfg_nodes g1 in
	  let bb_tbl_g1 = Hashtbl.create (List.length bb_list_g1) in
	  let () = List.iter (fun id ->
		Hashtbl.add bb_tbl_g1 id (g1#find id);
	  ) bb_list_g1 in

          let same_inst_list = Hashtbl.find same_asm_table n1 in


          List.iter (fun c2 ->
            done2 := !done2 + 1;
            match c2 with
              | (Function(n2,_,_,_,None),_) -> (
                  let id2 = get_id_from_name n2 tbl2 in
                  non_threaded_add_score id1 id2 score score_diff
                )
              | (Function(n2,_,_,_,_),g2) -> (
                  let id2 = get_id_from_name n2 tbl2 in

		  let bb_list_g2 = cfg_nodes g2 in
		  let bb_tbl_g2 = Hashtbl.create (List.length bb_list_g2) in
		  List.iter (fun id ->
			Hashtbl.add bb_tbl_g2 id (g2#find id);
		  ) bb_list_g2;

 		 let () = Printf.printf "same_inst_list for %s has length %d:\n" n1 (List.length same_inst_list) in
		let () = flush stdout in

                   if (List.length same_inst_list) = 0

                  then
                    (
                    let new_thread = if n1 = n2
                      then Thread.create threaded_add_score 
                        (g1, g2, id1, id2, score, score_same_name, Hashtbl.create 1)
                      else Thread.create threaded_add_score 
                        (g1, g2, id1, id2, score, 0.0, Hashtbl.create 1)
                    in
                    Thread.delay threads_wait1;
                    Printf.fprintf !initscore_debug_ch 
                      "new thread %d: comparing function %s from %s (fun_id=%d, bb_count=%d) with function %s from %s (fun_id=%d, bb_count=%d)\n\tprogress %d/%d; %d/%d\n%!" 
                      (Thread.id new_thread) n1 !input_file1 id1 
                      (Hashtbl.length bb_tbl_g1) n2 !input_file2  id2 
                      (Hashtbl.length bb_tbl_g2) !done1 size1 !done2 size2;
                    Mutex.lock m_threads;
                    tmp_threads_count := !threads_count;
                    Mutex.unlock m_threads;
                    while !tmp_threads_count >= number_of_threads1
                    do 
                      (
                      Printf.fprintf !initscore_debug_ch "---waiting:\n";
                      Mutex.lock m_threads;
                      List.iter (fun x ->
												(*pm*)
												let repeat_times = thread_count  (Thread.id x) in
												let _ = if (repeat_times > 10) then
													(
														try(
															Thread.kill x;				
															Printf.printf "4-killed thread %d\n" (Thread.id x);
															flush stdout;
															)
														with _  -> 
															(
																Printf.printf "4-killed thread %d and safe caught\n" (Thread.id x);
															flush stdout;
																);
															  Printf.fprintf !debug_ch "joining %d\n" (Thread.id x);
															  threads := List.filter (fun y -> 
															    y <> x
															    ) !threads;
															  threads_count := !threads_count - 1;
																
													)
												in
												(*pm end*)
                        Printf.fprintf !initscore_debug_ch "%d " (Thread.id x)
                        ) !threads;
                      Mutex.unlock m_threads;
                      Printf.fprintf !initscore_debug_ch "\n---\n%!";
                      Thread.delay threads_wait2;
                      Mutex.lock m_threads;
                      tmp_threads_count := !threads_count;
                      Mutex.unlock m_threads
                      )
                    done;
											(*pm*)
										Hashtbl.clear thread_wait_tbl;
										(*pm end*)
                    )
                  else
                    (
                    if not (List.exists (fun x -> x = n2) same_inst_list)
                    then non_threaded_add_score id1 id2 score score_diff
                    )
                  )
              | _ -> ()
            ) cfgs2
          )
      | _ -> ()
    ) cfgs1
  ;
  while !threads_count > 0
  do
    (
    Mutex.lock m_threads;
    Printf.fprintf !initscore_debug_ch "waiting\n";
    List.iter (fun x ->
			(*pm*)
												let repeat_times = thread_count  (Thread.id x) in
												let _ = if (repeat_times > 10) then
													(
														try(
															
															Thread.kill x;				
															
											
															Printf.printf "5-killed thread %d\n" (Thread.id x);
															flush stdout;
															)
														with _  -> 
															(
																
																Printf.printf "5-killed thread %d and safe caught\n" (Thread.id x);
															flush stdout;
																);
														
													  Printf.fprintf !debug_ch "joining %d\n" (Thread.id x);
													  threads := List.filter (fun y -> 
													    y <> x
													    ) !threads;
													  threads_count := !threads_count - 1;
													  
														
													)
												in
		(*pm end*)
      Printf.fprintf !initscore_debug_ch "%d " (Thread.id x)
      ) !threads;
    Printf.fprintf !initscore_debug_ch "\n---\n%!";
    Mutex.unlock m_threads;
    Thread.delay threads_wait2
    )
  done
  ;
  (size1, size2, score)

  )

;;


(*
(*
print the call graph
@param cg: the call graph
@param cg_tbl: Hashtbl(function name, node id in cg)
@param ch: output channel to which the call graph is printed
*)
let print_cg cg cg_tbl ch = 
  let ftbl = Hashtbl.create (Hashtbl.length cg_tbl) in 
  let () = Hashtbl.iter (fun k v -> 
    Hashtbl.add ftbl v k
    ) cg_tbl in 
  let printer = function_name_printer ftbl in 
  print_dot_cfg cg "callgraph" printer ch
;;
*)


(*
analyze a cg to find out its functions
return 5 List(function name), each with a different property
  ret1: external functions
  ret2: functions without predecessors or successors (isolated)
  ret3: empty functions
  ret4: functions without predecessors
  ret5: normal functions (the remaining)
@param cg: the call graph
@param cg_tbl: Hashtbl(function name, node id in cg)
@param cfgs: List(cfg)
*)
let get_cg_func cg cg_tbl cfgs =
  let cfg_is_external name = List.fold_left (fun acc c ->
    match c with
      | (Function(n,_,_,_,None),_) when n = name -> true
      | _ -> acc
    ) false cfgs
  in


  let cfg_is_empty name =
    List.fold_left (fun acc1 c ->
      match c with
        | (Function(n,_,_,_,_),g) when n = name -> 

	  let bb_list_g = cfg_nodes g in
	  let bb_tbl_g = Hashtbl.create (List.length bb_list_g) in
	  List.iter (fun id ->
		Hashtbl.add bb_tbl_g id (g#find id);
	  ) bb_list_g;
            if (Hashtbl.fold (fun id blk acc2 ->
              if id <> BB(0)
              then acc2 + 1
              else acc2
              ) bb_tbl_g 0) = 0
            then true
            else acc1
        | _ -> acc1
      ) false cfgs
  in    


  let (ret1, ret2, ret3, ret4, ret5) = 
    Hashtbl.fold (fun id blk (r1, r2, r3, r4, r5) ->
      if id > 0 
      then
        (
        let name = get_name_from_id id cg_tbl in
        if cfg_is_external name
        then 
          (
          Printf.fprintf !debug_ch "external: %d %s\n" id name;
          (name :: r1, r2, r3, r4, r5)
          )
        else
          (
          if ((List.length (Mycg.pred cg blk)) = 0) && ((List.length (Mycg.succ cg blk)) = 0)
          then
            (
            Printf.fprintf !debug_ch "isolated: %d %s\n" id name;
            (r1, name :: r2, r3, r4, r5)
            )
          else
            (
            if cfg_is_empty name 
            then 
              (
              Printf.fprintf !debug_ch "empty: %d %s\n" id name;
              (r1, r2, name :: r3, r4, r5)
              )
            else 
              (
              if (List.length (Mycg.pred cg blk)) = 0 && name <> "main"
              then
                (
                Printf.fprintf !debug_ch "no pred: %d %s\n" id name;
                (r1, r2, r3, name :: r4, r5)
                )
              else
                (
                Printf.fprintf !debug_ch "normal: %d %s\n" id name;
                (r1, r2, r3, r4, name :: r5)
                )
              )
            )
          )
        )
      else (r1, r2, r3, r4, r5)
      ) cg.v_tbl ([], [], [], [], [])
  in
  Printf.fprintf !debug_ch "\n";
  (*print_cg cg cg_tbl !debug_ch;*)
  Printf.fprintf !debug_ch 
    "\n\nexternal func: %d\nisolated func: %d\nempty func: %d\nno pred func: %d\nnormal func: %d\n\n\n" 
    (List.length ret1) (List.length ret2) (List.length ret3) 
    (List.length ret4) (List.length ret5);
  (ret1, ret2, ret3, ret4, ret5)
;;


(*
print out informaiton of matched functions
@param matched: Hashtbl((node id for function1, node id for function2), score)
  function mappings with their corresponding score
@param tbl1, tbl2: Hashtbl(function name, node id in cg)
@param cg1_func, cg2_func: 5 List(function name)
  5 lists of functions with different properties
*)
let print_matched_name matched tbl1 tbl2 cg1_func cg2_func =
  let test_exist_funcs name (f1, f2, f3, f4, f5) = 
    if List.exists (fun x -> x = name) f1
    then 1
    else 
      (
      if List.exists (fun x -> x = name) f2
      then 2
      else 
        (
        if List.exists (fun x -> x = name) f3
        then 3 
        else
          (
          if List.exists (fun x -> x = name) f4
          then 4
          else
            (
            if List.exists (fun x -> x = name) f5
            then 5
            else 0
            )
          )
        )
      )
  in       


  let new_count (c1, c2, c3, c4, c5) t1 t2 =
    if t1 = t2
    then
      (
      match t1 with
        | 1 -> (c1 + 1, c2, c3, c4, c5)
        | 2 -> (c1, c2 + 1, c3, c4, c5)
        | 3 -> (c1, c2, c3 + 1, c4, c5)
        | 4 -> (c1, c2, c3, c4 + 1, c5)
        | 5 -> (c1, c2, c3, c4, c5 + 1)
        | _ -> (c1, c2, c3, c4, c5)
      )
    else (c1, c2, c3, c4, c5)
  in


  let get_possible_func_matches f1 f2 =
    List.fold_left (fun acc x ->
      if List.exists (fun y -> x = y) f2
      then x :: acc 
      else acc
      ) [] f1
  in


  let print_possible_func_matches l =
    List.iter (fun n ->
      let id1 = get_id_from_name n tbl1 in
      let id2 = get_id_from_name n tbl2 in
      let () = 
        try (
          let _ = Hashtbl.find matched (id1, id2) in
          Printf.fprintf !debug_ch "G: "
          ) 
        with
          | Not_found -> Printf.fprintf !debug_ch "B: "
      in
      Printf.fprintf !debug_ch "%s\n" n
      ) l
  in


  let print_func_matches (f11, f12, f13, f14, f15) (f21, f22, f23, f24, f25) =
    let l1 = get_possible_func_matches f11 f21 in
    let l2 = get_possible_func_matches f12 f22 in
    let l3 = get_possible_func_matches f13 f23 in
    let l4 = get_possible_func_matches f14 f24 in
    let l5 = get_possible_func_matches f15 f25 in
    Printf.fprintf !debug_ch "all possible matches-functions with the same name: G: really matched: (%d, %d, %d, %d, %d)\n" 
      (List.length l1) (List.length l2) (List.length l3) (List.length l4) 
      (List.length l5);
    Printf.fprintf !debug_ch "external functions: \n";
    print_possible_func_matches l1;
    Printf.fprintf !debug_ch "\nisolated functions: \n";
    print_possible_func_matches l2;
    Printf.fprintf !debug_ch "\nempty functions: \n";
    print_possible_func_matches l3;
    Printf.fprintf !debug_ch "\nno pred functions: \n";
    print_possible_func_matches l4;
    Printf.fprintf !debug_ch "\nnormal functions: \n";
    print_possible_func_matches l5;
  in


  let () = Printf.fprintf !debug_ch "-----printing matched name\n" in
  let (s1, s2, s3, s4, s5) = Hashtbl.fold (fun (id1, id2) score acc ->
    let n1 = get_name_from_id id1 tbl1 in
    let n2 = get_name_from_id id2 tbl2 in
    let test1 = test_exist_funcs n1 cg1_func in
    let test2 = test_exist_funcs n2 cg2_func in
    let () = if test1 = 5 
      then Printf.fprintf !debug_ch "*"
    in
    let () = Printf.fprintf !debug_ch "%d%d" test1 test2 in
    if n1 = n2
    then
      (
      Printf.fprintf !debug_ch "G: (%s[%d], %s[%d]) %f\n" n1 id1 n2 id2 score;
      new_count acc test1 test2
      )
    else 
      (
      Printf.fprintf !debug_ch "B: (%s[%d], %s[%d]) %f\n" n1 id1 n2 id2 score;
      acc
      )
    ) matched (0, 0, 0, 0, 0)
  in
  Printf.fprintf !debug_ch "same name = (%d, %d, %d, %d, %d)\n-----\n\n" 
    s1 s2 s3 s4 s5;
  print_func_matches cg1_func cg2_func
;;


let main argc argv = 
(

  let startTime = Unix.time () in

  let () = Random.init(0) in

  let () = input_file1 := argv.(1) in
  let () = input_file2 := argv.(2) in
  let () = input_file3 := argv.(3) in
  (*let () = input_file4 := argv.(4) in*)

  let in_ir_1 = open_in !input_file1 in
  let in_ir_2 = open_in !input_file2 in
  let (dl1a,sl1a,finfo_list1a) = (Marshal.from_channel in_ir_1 : Vine.decl list * Vine.stmt list * Vine_tovine.funinfo_t list) in
  let (dl2a,sl2a,finfo_list2a) = (Marshal.from_channel in_ir_2 : Vine.decl list * Vine.stmt list * Vine_tovine.funinfo_t list) in
  let () = close_in in_ir_1 in
  let () = close_in in_ir_2 in
	
	
	(*pm debug*)
	let () = List.iter(fun finfo -> 
		Printf.fprintf !debug_ch "read finfo_list1a: fun name: %s\n" finfo.name;
		)finfo_list1a 
	in
	
	let () = List.iter(fun finfo -> 
		Printf.fprintf !debug_ch "read finfo_list2a: fun name: %s\n" finfo.name;
		)finfo_list2a 
	in
	(*pm debug end*)
	
	
  let in_match = open_in !input_file3 in
	let () = Printf.printf "Before read fast matching file\n" in
  let fun_matchings_read = (Marshal.from_channel in_match : (string,(string*float)) Hashtbl.t ) in
	let () = Printf.printf "After read fast matching file\n" in
  (*let fun_matchings_read = Hashtbl.create 0 in*)
  let () = close_in in_match in

  (*let in_block_match = open_in !input_file4 in*)
  (*let block_matchings_read = (Marshal.from_channel in_block_match : (Int64.t,(Int64.t*float)) Hashtbl.t) in*)
  let block_matchings_read = Hashtbl.create 0 in
  (*let () = close_in in_block_match in*)

  
  let correct_order = (List.length finfo_list1a) <= (List.length finfo_list2a) in

  (* reorder, so smaller cg (based on number of functions) is first *)
  let (dl1, dl2, sl1, sl2, finfo_list1, finfo_list2) = 
    if correct_order
    then (dl1a, dl2a, sl1a, sl2a, finfo_list1a, finfo_list2a)
    else (  Printf.printf "WARNING: size of input1 CG > size of input2 CG....matchings may be reversed!!\n";
	(dl2a, dl1a, sl2a, sl1a, finfo_list2a, finfo_list1a)
    )
  in


  (*
     this ensures we remove function declarations for internally defined functions,
     and don't include the special function containing "misfit" instructions (prob don't need this check, though)
  *)
  let fl1 = List.filter (fun f ->
    match f with
     |   Function(n,_,_,false,Some(s)) when n <> unknown_addrs_function.name-> true 
     |   Function(n,_,_,true,_) when n <> unknown_addrs_function.name-> true 
     |   _ -> false
  ) sl1 in

  let fl2 = List.filter (fun f ->
    match f with
     |   Function(n,_,_,false,Some(s)) when n <> unknown_addrs_function.name-> true 
     |   Function(n,_,_,true,_) when n <> unknown_addrs_function.name-> true 
     |   _ -> false
  ) sl2 in


  let num_fun1 = (List.length finfo_list1) in
  let num_fun2 = (List.length finfo_list2) in

  let () = Printf.fprintf !toplevel_debug_ch "\nInput file 1 has %d functions in its finfo list and %d functions in its Function list\n" num_fun1 (List.length fl1) in
  let () = Printf.fprintf !toplevel_debug_ch "Input file 2 has %d functions in its finfo list and %d functions in its Function list\n" num_fun2 (List.length fl2) in
  let () = Printf.printf "\nInput file 1 has %d functions in its finfo list and %d functions in its Function list\n" num_fun1 (List.length fl1) in
  let () = Printf.printf "Input file 2 has %d functions in its finfo list and %d functions in its Function list\n" num_fun2 (List.length fl2) in

let () = output_string !toplevel_debug_ch "********* Printing finfo_l **********\n" in
let () =  List.iter (fun finfo -> 
	output_string !toplevel_debug_ch finfo.name;
	output_char !toplevel_debug_ch '\t';
	Printf.fprintf !toplevel_debug_ch "%x" (Int64.to_int finfo.start_address);
	output_char !toplevel_debug_ch '\t';
	Printf.fprintf !toplevel_debug_ch "%x" (Int64.to_int finfo.end_address);
	output_char !toplevel_debug_ch '\t';
	output_string !toplevel_debug_ch (string_of_bool finfo.is_extern);
	output_char !toplevel_debug_ch '\n' 
    ) finfo_list1 
in

let () = output_string !toplevel_debug_ch "********* Printing finfo_2 **********\n" in
let () =  List.iter (fun finfo -> 
	output_string !toplevel_debug_ch finfo.name;
	output_char !toplevel_debug_ch '\t';
	Printf.fprintf !toplevel_debug_ch "%x" (Int64.to_int finfo.start_address);
	output_char !toplevel_debug_ch '\t';
	Printf.fprintf !toplevel_debug_ch "%x" (Int64.to_int finfo.end_address);
	output_char !toplevel_debug_ch '\t';
	output_string !toplevel_debug_ch (string_of_bool finfo.is_extern);
	output_char !toplevel_debug_ch '\n' 
    ) finfo_list2 
in


  let saddr2name_tbl1 = Hashtbl.create num_fun1 in
  let saddr2name_tbl2 = Hashtbl.create num_fun2 in
  let () = List.iter (fun f -> 
	 Hashtbl.add saddr2name_tbl1 f.start_address f.name
  ) finfo_list1 in
  let () = List.iter (fun f -> 
	 Hashtbl.add saddr2name_tbl2 f.start_address f.name
  ) finfo_list2 in

  let name2saddr_tbl1 = Hashtbl.create num_fun1 in
  let name2saddr_tbl2 = Hashtbl.create num_fun2 in
  let () = List.iter (fun f -> 
	 Hashtbl.add name2saddr_tbl1 f.name f.start_address 
  ) finfo_list1 in
  let () = List.iter (fun f -> 
	 Hashtbl.add name2saddr_tbl2 f.name f.start_address 
  ) finfo_list2 in



  let () = Printf.fprintf !toplevel_debug_ch "****Creating callgraphs (one cg per binary file)..." in
  let () = flush !toplevel_debug_ch in
  let (cg1, cg_tbl1) = Mycg.create_callgraph (dl1, sl1) saddr2name_tbl1  in
  let (cg2, cg_tbl2) = Mycg.create_callgraph (dl2, sl2) saddr2name_tbl2 in
  let () = Printf.fprintf !toplevel_debug_ch "done\n" in


  let () = Printf.fprintf !toplevel_debug_ch "****Creating and printing cfg lists (one cfg per function)..." in
  let cfgs1 = make_cfgs fl1 in
  let cfgs2 = make_cfgs fl2 in
	(*pm: filter repeated name from sqlite*)
	let filter_cfgs1 = ref [] in
	let filter_cfgs2 = ref [] in
	
	let () = List.iter (fun c1 -> match c1 with
      | (Function(n1,_,_,_,_),g1) as f_c1 ->
				let exists = List.exists (fun (Function(f_n1,_,_,_,_),f_g1) ->
					(f_n1=n1) 
					) !filter_cfgs1 
				in
				
				let () = match exists with
					| true -> ()
					| false -> 
						filter_cfgs1 := f_c1 :: !filter_cfgs1;
				in
				()
  )cfgs1
	in
	
		let () = List.iter (fun c2-> match c2 with
      | (Function(n2,_,_,_,_),g2) as f_c2 ->
				let exists = List.exists (fun (Function(f_n2,_,_,_,_),f_g2) ->
					(f_n2=n2) 
					) !filter_cfgs2 
				in
				
				let () = match exists with
					| true -> ()
					| false -> 
						filter_cfgs2 := f_c2 :: !filter_cfgs2;
				in
				 ()
  )cfgs2
	in
	
	let cfgs1 = !filter_cfgs1 in
	let cfgs2 = !filter_cfgs2 in
	(*pm end*)
  let () = print_cfgs cfgs1 "1" in
  let () = print_cfgs cfgs2 "2" in
  let () = Printf.fprintf !toplevel_debug_ch "done\n" in



  let fast_matchings = fun_matchings_read in
  let () = no_fast_matchings2 := List.map (fun (Function(n2,_,_,_,e),g2) ->
	(n2,e,g2)
  ) cfgs2 in

  let () = List.iter (fun (Function(n1,_,_,_,e),g1) ->  
	try  ( 
		let (n2, score) = Hashtbl.find fast_matchings n1 in
		(*let () = Printf.fprintf !toplevel_debug_ch "Matching %s with %s, score=%f.\n" n1 n2 score in*)
		no_fast_matchings2 := List.filter (fun (f,_,_) ->
			f <> n2
		) !no_fast_matchings2
	)
	with Not_found -> (
		(*Printf.fprintf !toplevel_debug_ch "%s not matched!\n" n1;*)
		no_fast_matchings1 := (n1,e,g1) :: !no_fast_matchings1
	)
  ) cfgs1 in

  let () = Printf.printf "Number of fast matchings = %d, non-fastmatched1 = %d, non-fastmatched2 = %d.\n" (Hashtbl.length fast_matchings) (List.length !no_fast_matchings1) (List.length !no_fast_matchings2)
  in


  let () = Printf.printf "Number of block matchings read = %d.\n" (Hashtbl.length block_matchings_read) in
  let block_matchings = block_matchings_read in
  

(*
  let () = Hashtbl.iter (fun a (b,sc) ->
	Printf.printf "%s matched to %s, score = %f\n" a b sc

  ) block_matchings in
  let () = flush stdout in
*)

  let name2asm_tbl1 = create_name2asm_tbl fl1 in
  let name2asm_tbl2 = create_name2asm_tbl fl2 in



  let () = Printf.fprintf !toplevel_debug_ch "****Calling init_cg_score, see debug.initscore for details...\n" in
  let () = flush !toplevel_debug_ch in
  let () = flush stdout in
  let (cfgs1_size, cfgs2_size, score) = 
    init_cg_score cfgs1 cfgs2 cg_tbl1 cg_tbl2 name2asm_tbl1 name2asm_tbl2 fast_matchings block_matchings in
  let () = Printf.fprintf !toplevel_debug_ch "done\n" in

(***************************************************************************************************)
  let () = Printf.fprintf !stats_debug_ch "sum_stp_queries=%d\nsum_testv_calls=%d\nsum_stp_true=%d\nsum_quick_true=%d\n" !sum_stp_queries !sum_testv_calls !sum_stp_true !sum_quick_true in

  let () = Printf.fprintf !toplevel_debug_ch "****Starting isomorphism of the cg...\n" in
  let () = flush !toplevel_debug_ch in
  let (matched_ret, matched_size, matched_score, matched_cg) = 
    Cg_iso.isomorphism_accurate cg1 cg2 cfgs1_size (Hashtbl.create cfgs1_size) 
      score init_max_size_ratio_cg init_max_score_ratio_cg timeout_length_cg1 
      timeout_length_cg2 timeout_count_cg1 timeout_count_cg2 !toplevel_debug_ch false
  in
  let () = Printf.fprintf !toplevel_debug_ch "done\n" in
(*****************************debug*************************************)
		(*let yes_score_debug_ch = ref (open_out "debug/yes_score") in
		let no_score_debug_ch = ref (open_out "debug/no_score") in
		
let file_name1 = Hashtbl.create 1024 in
let file_name2 = Hashtbl.create 1024 in

	Printf.fprintf !toplevel_debug_ch "score table----------\n" ;
	let () = Hashtbl.iter (fun (id1,id2) value ->
		let n1 = get_name_from_id   id1 cg_tbl1 in
		let n2 = get_name_from_id  id2 cg_tbl2  in
		
		let _ = if (value > 0.0) then
			(
				Hashtbl.add file_name1 n1 (n2, value) ;
				Hashtbl.add file_name2 n2 (n1,value) ;		
			)
		in
		
		
		Printf.fprintf !toplevel_debug_ch "%s %s %f\n" n1 n2 value ;
		) score in
		Printf.fprintf !toplevel_debug_ch "score table end----------\n" ;
		
		let () = List.iter (fun (Function(n1,_,_,_,e),g1) ->  
			let _ = try(
				let (n2, value) = Hashtbl.find file_name1 n1 in
				Printf.fprintf !yes_score_debug_ch "1-yes score func: %s %s %f\n" n1 n2 value;
				)with _ -> 
					(
						Printf.fprintf !no_score_debug_ch "1-no score func: %s\n" n1;
						()
					)
					
			in
			()
			)cfgs1
		in
		
		let () = List.iter (fun (Function(n2,_,_,_,e),g2) ->  
			let _ = try(
				let (n1, value) = Hashtbl.find file_name2 n2 in
				Printf.fprintf !yes_score_debug_ch "2-yes score func: %s %s %f\n" n1 n2 value;
				)
				with Not_found -> 
					(
						
						Printf.fprintf !no_score_debug_ch "2-no score func: %s\n" n2;
					)
					
			in
			()
			)cfgs2
		in
		
		let () = close_out !yes_score_debug_ch in
		let () = close_out !no_score_debug_ch in*)
		(*****************************debug end*************************************)
	

	(*pm*)
	let bbs1_num = ref 0 in
	let bbs2_num = ref 0 in
	 
  let () = List.iter (fun (Function(n1,_,_,_,e),g1) -> 
		let bbid_list_cfg1 = cfg_nodes g1 in
		let num1 = (List.length bbid_list_cfg1) in
		bbs1_num := !bbs1_num +  num1;
		Printf.fprintf !toplevel_debug_ch "bin1: %s: %d bbs\n" n1 num1;
		)cfgs1 in
		
	let () = List.iter (fun (Function(n2,_,_,_,e),g2) -> 
		let bbid_list_cfg2 = cfg_nodes g2 in
		let num2 = (List.length bbid_list_cfg2) in
		bbs2_num := !bbs2_num +  num2;
		Printf.fprintf !toplevel_debug_ch "bin2: %s: %d bbs\n" n2 num2;
		)cfgs2 in
	
	(*pm end*)
	
	let () = Printf.fprintf !toplevel_debug_ch 
	"fun1 number: %d, fun2 number: %d, bbs num1: %d, bbs_num2: %d\n " 
	(List.length cfgs1)
	(List.length cfgs2)
	!bbs1_num
	!bbs2_num
	in

  let (result_size, result_score) = 
    ((float_of_int matched_size) /. (float_of_int cfgs1_size), 
      matched_score /. (float_of_int cfgs1_size)) 
  in
  let cg1_func = get_cg_func cg1 cg_tbl1 cfgs1 in
  let cg2_func = get_cg_func cg2 cg_tbl2 cfgs2 in
  let () = print_matched_name matched_cg cg_tbl1 cg_tbl2 cg1_func cg2_func in
  Printf.printf "***result_size: %f, result_score: %f, matched_score=%f, cfgs1_size=%d\n" result_size 
    result_score matched_score cfgs1_size;
  Printf.fprintf !toplevel_debug_ch "***result_size: %f, result_score: %f,matched_score=%f, cfgs1_size=%d\n" 
    result_size result_score matched_score cfgs1_size ;

  let endTime = Unix.time () in

	
  let () = Printf.printf "Total runtime: %f seconds (equal to %f minutes)\n" 
	(endTime -. startTime) ((endTime -. startTime)/. 60.0) in
  let () = Printf.fprintf !toplevel_debug_ch "Total runtime: %f seconds (equal to %f minutes)\n" 
	(endTime -. startTime) ((endTime -. startTime)/. 60.0) in
	
  close_out !toplevel_debug_ch;
  close_out !initscore_debug_ch;
  close_out !debug_ch;
)
in
main (Array.length Sys.argv) Sys.argv;;

