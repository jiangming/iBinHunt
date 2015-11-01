(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
open Vine
open Vine_tovine
open Vine_cfg
open Vine_util
open Exectrace 
open Trace_diff;;
module List = ExtList.List ;;
module String = ExtString.String ;;

type cmdlineargs_t = {
(*   mutable bins_file : string; *)
(*   mutable irin_file : string; *)
(*   mutable first_eip : int64; *)
(*   mutable last_eip : int64; *)
(*   mutable taintcheck : bool; *)
(*   mutable skip_addrs : int64 list; *)
(*   mutable block_by_block : bool; *)
  mutable trace_file : string;
  mutable irout_file : string;
  mutable wpout_file : string;
  mutable stpout_file : string;
  mutable state_file : string;
	mutable ida_file: string;(*pm*)
	(*pm start*)
	mutable trace_file2 : string;
  mutable irout_file2 : string;
  mutable wpout_file2 : string;
  mutable stpout_file2 : string;
  mutable state_file2 : string;
	mutable ida_file2: string;
	mutable taint_range_file: string;
	(*pm end*)
  mutable state_ranges : (int64 * int64) list;
	mutable state_ranges2 : (int64 * int64) list;(*pm*)
  mutable concrete : bool;
  mutable typecheck : bool;
  mutable eval : bool;
  mutable dead : bool;
  mutable early_exit : bool;
  mutable simplify : bool;
  mutable include_all : bool;
  mutable use_thunks : bool;
  mutable use_post_var : bool;
  mutable assertion_on_var : bool; 
  mutable deend : bool;
  mutable deend_multi : bool;
  mutable verify_expected : bool;
  mutable conc_mem_idx : bool;
  mutable prop_consts : bool;
  mutable remove_unknowns : bool;
  mutable flatten : bool;
} ;;

 

let findvar dl vname =
  List.find
    (fun (_,s,_) -> s = vname)
    dl

let debug s =
  print_endline s

let rec is_straightline stmts =
  match stmts with
  | Jmp(_)::tail -> false
  | CJmp(_,_,_)::tail -> false
  | Block(dl, sl)::tail ->
      is_straightline (List.rev_append sl tail)
  | Attr(s,_) :: tail ->
      is_straightline (s::tail)
  | s :: tail ->
      is_straightline tail
  | [] -> true

let writestp filename exp =
  let fd = open_out filename in
    debug("Writing STP file '"^filename^"'...");
    flush stdout;
    Stp.to_file fd exp;
    close_out fd

let writeir filename prog =
  let oc = open_out filename in
  let ft = Format.formatter_of_out_channel oc in
  format_program ft prog;
  Format.pp_print_newline ft ()

let findpost sl =
  let retval = ref (0, "", REG_1) in
  let revsl = List.rev sl in
  let rec is_post stmt =
    match stmt with
	Move(lv, rv) -> ( 
	  match lv with
	      Temp((_, name, _) as var) when String.length name >= 4 -> 
		let result = String.sub name 0 4 = "post" in
		  if result then retval := var; 
		  result
	    | _ -> false
	)
      | Block(dl, sl) -> (
	  try  
	    let revsl = List.rev sl in
	      ignore(List.find is_post revsl);
	      true
	  with
	      Not_found -> false 
	)
      | _ -> false
  in
    try 
      match List.find is_post revsl with
	  Move(Temp _, _) -> Lval(Temp(!retval))
	| _ -> raise (Invalid_argument "findpost")
    with 
       Not_found -> Constant(Int(REG_1, 1L))
	  
let inline_func prog =
  let (dl, sl) = prog in
  let funchash = Hashtbl.create 1000 in
  let rec process_stmt stmt = 
    match stmt with
      | Block(dl, sl) -> 
	  let newsl = List.map process_stmt sl in
	    Block(dl, newsl)
      | Function(name, t, dl, ext, ostmt) ->
	  (
	    match ostmt with
		None -> stmt
	      | Some(blk) -> Hashtbl.add funchash name blk; stmt
	  )
      | Call (_, e, _)  -> 
	  (
	    match e with
		Name(l) ->
		  let blk = Hashtbl.find funchash l in
		    process_stmt blk
	      | _ -> stmt
	  )
      | _ -> stmt
  in
  let inlinedsl = List.map process_stmt sl in
    (dl, inlinedsl)

(*pm print cfg*)

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
	(*****************************************************************************************)
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
(**************************************************************************)
let print_ir dl sl finfo_l = 
	let out_vineIR = open_out "debug/vineIR" in
	
		let sl = List.map (fun s -> match s with
	| Function(n,t,d,e,st) -> 
		( 
		let () = Printf.printf "Looking for function name %s\n" n in
		let fixed_name = (fix_name n) in
		let finfo = List.find (fun f -> (f.name = fixed_name)) finfo_l in
		let () = Printf.printf "Found function name %s=%s with %b=%b\n" n finfo.name e finfo.is_extern in
		Function(fixed_name,t,d,finfo.is_extern,st)
		)
	| a -> a
	) sl in

	let condense_block blk_sl = 
  	let (l, c, p, a) = List.fold_left (fun (curr_label, curr_comments, curr_sl, all_sl) s ->
		match s with 
		| Label(str) as s -> (
		match curr_label with
		| None -> 
			(
                     if (List.length all_sl) <> 0 then Printf.fprintf out_vineIR "Warning: all_sl should be empty at this point!\n"; (Some(str), curr_comments, [s], all_sl )
			) 
		| Some(x) -> (Some(str), [], [s], all_sl @ curr_sl)

		)
		| Comment _ as s -> (curr_label, curr_comments @ [s], curr_sl @ [s], all_sl)
		| Move _ | Special _ | ExpStmt _ | Attr _ | Assert _ | Jmp _ | CJmp _ as s -> (curr_label, curr_comments, curr_sl @ [s], all_sl)
		|  Return _ | Call _ | Halt _ as s -> 
		( match curr_label with
			| None -> (Printf.fprintf out_vineIR "Warning: should have seen a label!!!\n"; 					(curr_label, curr_comments, curr_sl, all_sl))
			| Some(x) -> (curr_label, curr_comments, Label(x) :: (curr_comments @ [s]), all_sl)

		)
        | Block _ | Function _ -> (Printf.fprintf out_vineIR "Warning: found Function or Block inside Block!!!\n"; 					(curr_label, curr_comments, curr_sl, all_sl))
  	) (None, [], [], []) blk_sl in
	p @ a
	in


	let sl = List.map (fun s -> match s with
	| Function(n,t,d,e,st) -> 
		(
		let () = Printf.printf "Looking for function name %s\n" n in
		let finfo = List.find (fun f -> (f.name = n)) finfo_l in
		let () = Printf.printf "Found function name %s=%s with %b=%b\n" n finfo.name e finfo.is_extern in
		Function(n,t,d,finfo.is_extern,st)
		)
	| a -> a
	) sl in

	let sl = List.map (fun s -> match s with
		| Function(l,t,d,e,Some(st)) as f-> 
		(	match st with			
			| Block(bdl,bsl) -> Function(l,t,d,e,Some(Block(bdl,condense_block bsl)))
			| _ -> (output_string out_vineIR "\tWarning, function statment not a block!\n"; f)
		)	
		| Function(l,t,d,e,None) as f-> f
		| a -> a (*(Printf.printf "Warning: top-level statement not a function!"; a)*)	
	) sl in


	let () = output_string out_vineIR "Starting statements *****************************\n" in

	let ()=
 	List.iter (fun s -> 
		output_string out_vineIR "\t\t ********New statement**********\n";
		let () = match s with 
		| Function(l,None,fun_dl,ex,Some(st)) -> output_string out_vineIR "Vine.Function found:\n" ;
			output_string out_vineIR "\tLabel=\"";
			output_string out_vineIR l;
			output_string out_vineIR "\"\n";
			output_string out_vineIR "\tRetType=None\n";
			output_string out_vineIR "\tDecList=\"";
			List.iter (fun d ->
				output_string out_vineIR (decl_to_string d);
			) fun_dl;
			output_string out_vineIR "\"\n";
			if ex
			then output_string out_vineIR "\tExternal=TRUE\n"
			else output_string out_vineIR "\tExternal=FALSE\n";
			let () = match st with			
				| Block(bdl,bsl) -> 
					output_string out_vineIR "\tVine.Block found!\n";
					List.iter (fun s3 ->
						match s3 with 
							| Call(_,expr,_) ->
							  output_string out_vineIR "\t\tCall=\"";
							  output_string out_vineIR (exp_to_string expr);
							  output_string out_vineIR "\"\n";
							| Special(s4) -> output_string out_vineIR "\t\tSpecial: ";
									output_string out_vineIR s4;
									output_string out_vineIR "\n";
							| Jmp(expr) ->
		  					  output_string out_vineIR "\t\tJump=\"";
							  output_string out_vineIR (exp_to_string expr);
							  output_string out_vineIR "\"-\n";
							| _ -> ();
						
					) bsl;
				| _ -> output_string out_vineIR "\tTop-level statment not a block!\n";
			in ();
		| Function(l,None,fun_dl,ex,None) -> output_string out_vineIR "Vine.Function found:\n" ;
			output_string out_vineIR "\tLabel=\"";
			output_string out_vineIR l;
			output_string out_vineIR "\"\n";
			output_string out_vineIR "\tRetType=None\n";
			output_string out_vineIR "\tDecList=\"";
			List.iter (fun d ->
				output_string out_vineIR (decl_to_string d);
			) fun_dl;
			output_string out_vineIR "\"\n";
			if ex
			then output_string out_vineIR "\tExternal=TRUE\n"
			else output_string out_vineIR "\tExternal=FALSE\n";
			output_string out_vineIR "\tNo Statments\n";
		| _ -> ()(*Printf.printf "top-level statement not a function!!!!!";	*)

        in
	output_string out_vineIR (stmt_to_string s);
	output_char out_vineIR '\n';

	) sl
	in

	let out_ir = open_out ("ir__" ^ !flag_idadb_file) in
	let () = Marshal.to_channel out_ir (dl,sl,finfo_l) [] in
	let () = flush out_ir in
	close_out out_ir ; 
;;(*pm: end print_ir*)

(**************************************************************************)	
	(*
let neg_post cfg =
	let () = Printf.printf "pm: Enter neg_post\n" in
	(*for debug*)
	let bbid_list = Vine_cfg.cfg_nodes cfg in
	let () = List.iter (fun bbid->
		Printf.printf "%s\n" (Vine_cfg.bbid_to_string bbid)	
		)bbid_list in
	(*for debug end*)
	let neg_post_intern cfg bbid=
		let new_stmts = ref [] in
		let old_stmts = Vine_cfg.bb_stmts cfg bbid in
		let () = List.iter (fun stmt->
			match stmt with
				|Move(Temp(n,"post",t),BinOp(BITAND, lval, e))->
					(*let news = Move(Temp(n,"post",t),BinOp(BITAND, lval,UnOp(NOT,e))) in*)
					(*let news = Move(Temp(n,"post",t),UnOp(NOT,e)) in*)
					let news = Move(Temp(n,"post",t),e) in 
					new_stmts := news:: !new_stmts
				|_-> new_stmts := stmt:: !new_stmts
			)(List.rev old_stmts) 
		in
		!new_stmts
	in
	let set_id = Vine_cfg.BB(161) in
	let new_cfg_stmts = neg_post_intern cfg set_id in
	let () = Vine_cfg.bb_set_stmts cfg  set_id new_cfg_stmts in
	cfg
	*)
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

	(***********************************************************************)
let self_label_to_addr_notail (l_t:label) =
	(*let l = del_label_tail l_t in*)
  try
    Scanf.sscanf l_t "pc_0x%Lx" (fun x-> x)
  with
      _ -> 
	raise (VineError "label_to_addr given non address-like label")


	(***********************************************************************)
	let label_is_addr l = 
  try
    let _ = label_to_addr l in
    true
  with
    VineError _ -> 
      false
	
(***********************************************************************)
let is_low_addr addr =
	if (addr < 0xb7000000L)
	then true
	else false
(***********************************************************************)
			
let neg_post cfg =
	let () = Printf.printf "pm: Enter neg_post\n" in
	(*for debug*)
	(*let bbid_list = Vine_cfg.cfg_nodes cfg in
	let () = List.iter (fun bbid->
		Printf.printf "%s\n" (Vine_cfg.bbid_to_string bbid)	
		)bbid_list in*)
	(*for debug end*)
	let low_addr = ref 0 in
	
	let neg_post_intern cfg bbid is_low=
		let new_stmts = ref [] in
		let old_stmts = Vine_cfg.bb_stmts cfg bbid in
		let () = List.iter (fun stmt->
			match stmt with
				|Move(Temp(n,"post",t),BinOp(BITAND, lval, e))->
					let () = match is_low with
						| true->
					(*let news = Move(Temp(n,"post",t),BinOp(BITAND, lval,UnOp(NOT,e))) in*)
					(*let news = Move(Temp(n,"post",t),UnOp(NOT,e)) in*)
						(*let news = Move(Temp(n,"post",t),e) in*)
							let news = Move(Temp(n,"post",t),BinOp(BITAND, lval,e)) in
							new_stmts := news:: !new_stmts
						| _->
							let news = Move(Temp(n,"post",t),lval) in
							new_stmts := news:: !new_stmts
					in 
					()
				|_-> new_stmts := stmt:: !new_stmts
			)(List.rev old_stmts) 
		in
		!new_stmts
	in(*end with neg_post_intern*)
	
	let bbid_list = Vine_cfg.cfg_nodes cfg in
	let () = List.iter (fun bbid->
		 let stmts = Vine_cfg.bb_stmts cfg bbid in
		 let () = List.iter(fun stmt->
			match stmt with
				| Label l->
					let is_addr = label_is_addr l in
					let () = match is_addr with
						| true->
							let addr =  self_label_to_addr l in	
							let is_low = is_low_addr addr in
							let new_cfg_stmts = neg_post_intern cfg bbid is_low in
							Vine_cfg.bb_set_stmts cfg  bbid new_cfg_stmts
						| false->() 
					in	  
					()
				|_->()
			)stmts	 in
		()
	)bbid_list in
cfg
(*pm end*)

(*
let appreplay args trace =
(*   uncomment this to inline functions *)
(*   let trace = inline_func trace in *)
    (* to SSA *)
  let cfg = Vine_cfg.prog_to_cfg trace in
	
	(*pm*)
	let cfg = neg_post cfg in
	let () = print_cfg cfg "appreplay_cfg" in
	(*pm end*)
  let () = Vine_cfg.coalesce_bb cfg in
 	let cfg = Ssa.cfg2ssa cfg in
  let cfg = Ssa.to_vine cfg in

  let trace = Vine_cfg.normal_cfg_to_prog cfg in
  let (dl,sl) = trace in
  let () = debug "Tranlating trace to GCL..." in
  let gcl = 
    if is_straightline sl then
      Gcl.of_straightline sl
    else
      Gcl.of_trace trace in
(*   let qvar = findvar dl "post" in *)
  let q = findpost sl in
(*   let q = Lval(Temp(qvar)) in *)
  let () = debug "Computing wp..." in
  let (simp1, simplast) =
    if args.simplify
    then
      (Vine_opt.constant_fold_more (fun _->None),
       Vine_opt.simplify_faster <@ Vine_alphavary.alpha_vary_exp)
    else (id,id)
  in
  let wp = simplast(Wp.calculate_wp simp1 q gcl) in
  let () =
    if args.wpout_file <> "" then writeir args.wpout_file (dl, [ExpStmt wp])
  in
  let () =
    if args.stpout_file <> "" then writestp args.stpout_file wp
  in
  
   () 
;;

*)
(**************************************************************************************)
let is_continuous id cover_list=
	(*let () = Printf.printf "enter is_exist, id=%s\n" (bbid_to_string(id)) in*)
	let num_of_list = List.length cover_list in
	let ret = match num_of_list with 
		| 0->false
		| _->
		let last = List.hd cover_list in
		let equal = (last = id) in
		equal
	in
ret
;;
(**************************************************************************************)
let exclude_bb s_cfg  bb_range_tbl addr (s_cfg_cover_list: bbid list ref)=
	(*let () = Printf.printf "enter exclude_bb\n" in*)
		let is_low = is_low_addr addr in
		let () = match is_low with
			| true ->
				(*let () = Printf.printf "before find, addr=%Lx\n" addr in*)
				let id = Hashtbl.find bb_range_tbl addr in 
				(*let () = Printf.printf "After find\n" in*)
				let exist = is_continuous id !s_cfg_cover_list in
				let () = match exist with
								| true->()
								| false->s_cfg_cover_list:= id::!s_cfg_cover_list
				in
				()
			| _ -> ()
	 in
is_low
;;
(**************************************************************************************)
(*let exclude_bbs d_cfg s_cfg bb_range_tbl=
	let bbid_list = Vine_cfg.cfg_nodes d_cfg in
	let s_cfg_cover_list = ref [] in
	let s_cfg_uncover_list = ref [] in
	
	let bbid_list = List.rev bbid_list in
	(*let ()=List.iter(fun bbid->
		Printf.printf "dynamic bb seq: %s\n" (bbid_to_string(bbid))
		)bbid_list in*)
	
	let () = Printf.printf "d_cfg.length=%d" (List.length bbid_list) in
	let () = List.iter(fun bbid->
					let stmts = Vine_cfg.bb_stmts d_cfg bbid in
					let () = List.iter(fun stmt->
						let () = match stmt with
							| Label l->
								let is_addr = label_is_addr l in
								let () = match is_addr with
									| true->
										let addr =  self_label_to_addr l in
										(*let () = Printf.printf "before enter exclude_bb\n" in	*)
										let s_cfg = exclude_bb s_cfg bb_range_tbl addr s_cfg_cover_list in
										()
									| false->()
								in
								()
							|_->()
						in
						()
					)stmts in 
	()
	)bbid_list in
	
	s_cfg_cover_list := List.rev (!s_cfg_cover_list);
	let () = Printf.printf "s_cfg_cover_list.length=%d\n" (List.length !s_cfg_cover_list) in
	let () = List.iter (fun id->
			Printf.printf "%s\n" (bbid_to_string id)
			)!s_cfg_cover_list in
s_cfg_cover_list
;;
*)
(*****************************************************************************************)
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


(**************************************************************************************)
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
(**********************************************************************************)
let print_range_list range_tbl str_file_append=
	let bb_range_ch = ref(open_out ("debug/"^str_file_append^"_bbrange")) in
	let () =  Hashtbl.iter (fun addr id->
			let () = Printf.fprintf !bb_range_ch "addr=%Lx   bbid=%s\n" addr (bbid_to_string(id)) in
			()
	) range_tbl	in
	let () = close_out !bb_range_ch in 
()
;;

(**************************************************************************************)
let static_analyze_db ida_file =
(*pm start flat*)
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
		let fl = sl in
  	let num_fun = (List.length finfo_l) in
	
		(*let ()=print_ir dl sl finfo_l in*)
	
		let saddr2name_tbl = Hashtbl.create num_fun in
	  let () = List.iter (fun f -> 
		 Hashtbl.add saddr2name_tbl f.start_address f.name
	  ) finfo_l in
	  let () = Hashtbl.add saddr2name_tbl Int64.zero "non-direct-function-call" in
	  let name2saddr_tbl = Hashtbl.create num_fun in
	
	  let () = List.iter (fun f -> 
		 Hashtbl.add name2saddr_tbl f.name f.start_address 
	  ) finfo_l in
		
 		let cfgs_f = make_cfgs fl in
 	
		let (flat_f,flat_cfg)= List.hd cfgs_f in
		
		(*let ()=print_cfg flat_cfg "flat_cfg" in*)
		(*let ()=cfg_to_dot 	flat_cfg "flat_cfg" in*)
		(********************BB range*******************************)
		(*let rang_list = make_BB_range flat_cfg in*)
		let range_tbl = make_BB_range flat_cfg in
(*		let rang_list = sort_list rang_list in*)
		(*let () = print_range_list range_tbl ida_file in*)
(range_tbl, flat_cfg)
;;

(**************************************************************************************)
let is_init_comment cmt=
	try 
		let m = Scanf.sscanf cmt "%s Already initd input (%ld, %ld)" (fun x y  n -> n) in
		true
	with
		_->false
;;

let get_taint_seq cmt=
	let m = Scanf.sscanf cmt "%s Already initd input (%ld, %ld)" (fun x y  n -> n) in
	m
;; 

(****************************************************************************************)
let is_temp_var str=
	try 
		let m = Scanf.sscanf str "INPUT_%s" (fun n -> n) in
		true
	with
		_->false
;;

let get_temp_seq str=
	let rindex  = String.rindex str '_' in
	let no_tail = String.sub str (rindex+1) ((String.length str) -rindex-1) in
	let m = Scanf.sscanf no_tail "%ld" (fun n-> n) in
	(*let () = Printf.printf "get_temp_seq: s=%s  seq=%ld\n" str m in*)
	m
;; 
(**************************************************************************************)
(*let taint_tag d_cfg s_cfg_cover_list=
let seq_start = ref 0 in
let seq_long = ref 0 in
let bb_input_list = ref [] in
let seq_list = ref [] in
let bbid_list = Vine_cfg.cfg_nodes d_cfg in
let () = List.iter (fun blk_id->
	seq_start := List.length !bb_input_list;
	seq_long := 0;
	let sl = d_cfg#get_info (d_cfg#find blk_id) in
	let () = List.iter(fun stmt->
		let () = match stmt with
			| Comment str->
				let is_init = is_init_comment str in
				let () = match is_init with
					| true->
						let seq = get_taint_seq str in
						seq_list := seq::(!seq_list);
						seq_long := !seq_long + 1 ;
						(*Printf.printf "BBID=%s, INIT_INPUT_SEQ=%ld\n" (bbid_to_string blk_id) seq*)
					| false->()
				in
				()
			| Move(lval, rval)->
				let () = match rval with
					| Lval rlv->
						let () = match rlv with
						| Temp ((i,s,t))->
							(*let () = Printf.printf "temp s=%s\n" s in*)
							let is_temp_input = is_temp_var s in
							let () = match is_temp_input with
								| true ->
									let  seq = get_temp_seq s in
									seq_list := seq::(!seq_list);
									seq_long := !seq_long + 1 ;
									(*Printf.printf "BBID=%s, temp_INIT_INPUT_SEQ=%ld\n" (bbid_to_string blk_id) seq*)
								| _ -> ()
							in
							()
						| _->()
						in
						()
					| _ -> ()
				in
				()
			| _->()
		in
		()
		)sl in
		let bb_input = {blk_id=blk_id; seq_start = !seq_start; seq_long = !seq_long} in
		bb_input_list := bb_input::(!bb_input_list) 
		)bbid_list in
		
		bb_input_list := List.rev (!bb_input_list);
		seq_list := List.rev (!seq_list);
(!bb_input_list, !seq_list)
;;*)
(**************************************************************************************)
	(*let rec print_input_seq seq_list seq_start seq_end=
		(*let () = Printf.printf "print_input_seq: seq_start=%d, seq_end=%d" seq_start seq_end in *)
		(*let () = match seq_start with
			| seq_end -> ()
			| _ ->
				let  () = Printf.printf "~%ld~ " (List.nth  seq_list seq_start) in
				print_input_seq seq_list (seq_start+1) seq_end
		in*)
		if (seq_start <> seq_end) then
			 	(
					Printf.printf "~%ld~ " (List.nth  seq_list seq_start);
					print_input_seq seq_list (seq_start+1) seq_end;
				)
		
		else 
			Printf.printf "end\n"; 
	;;*)
(**************************************************************************************)
(*let print_bbs_sep bb_input_list1 bb_input_list2 seq_list1 seq_list2 s_cfg_cover_list1 s_cfg_cover_list2 bb_tag_list1 bb_tag_list2=
	let () = Printf.printf "Trace1....................\n" in
	
	(*let () = List.iter (fun seq->
		Printf.printf "%ld " seq
		)seq_list1 in*)
		
	
	let () = List.iter(fun bb_input->
		let () = Printf.printf "\n%s: seq_start=%d seq_long=%d" (bbid_to_string(bb_input.blk_id)) (bb_input.seq_start) (bb_input.seq_long)in
		let () = Printf.printf "\n%s: " (bbid_to_string(bb_input.blk_id))in
		let () = print_input_seq seq_list1 (bb_input.seq_start) ((bb_input.seq_start)+(bb_input.seq_long)) in
		()
		)bb_input_list1 in
		
	let () = Printf.printf "s_cfg_cover_list1..............\n" in
	let () = List.iter(fun id->
		Printf.printf "%s\n" (bbid_to_string(id))
		)s_cfg_cover_list1 in
	
	let () = Printf.printf "color1..............\n" in
	let () = List.iter(fun bbtag->
		let () = Printf.printf "\n%s: "  (bbid_to_string(bbtag.tag_blk_id)) in
		List.iter(fun color -> 
			Printf.printf "%d" color
			)(bbtag.color_list)
		)bb_tag_list1
	in
		
				
	let () = Printf.printf "Trace2....................\n" in
	(*let () = List.iter (fun seq->
		Printf.printf "%ld " seq
		)seq_list2 in*)
	
		let () = Printf.printf "s_cfg_cover_list1..............\n" in
	let () = List.iter(fun id->
		Printf.printf "%s\n" (bbid_to_string(id))
		)s_cfg_cover_list2 in
		
	let () = List.iter(fun bb_input->
		let () = Printf.printf "\n%s: " (bbid_to_string(bb_input.blk_id)) in
		let () = print_input_seq seq_list2 (bb_input.seq_start) ((bb_input.seq_start)+(bb_input.seq_long)) in
		()
		)bb_input_list2 in
		
	let () = Printf.printf "color2..............\n" in
	let () = List.iter(fun bbtag->
		let () = Printf.printf "\n%s: " (bbid_to_string(bbtag.tag_blk_id)) in
		List.iter(fun color -> 
			Printf.printf "%d" color
			)(bbtag.color_list)
		)bb_tag_list2
	in
	()
;;*)
(**************************************************************************************)
let same_s_blk s_cfg_cover_list bb_input_list=
	let length = List.length s_cfg_cover_list in
	
	let is_same = match length with
		| 0 -> true
		| _ -> 
			let length2 = List.length bb_input_list in
			match length2 with
				| 0 -> false
				| _ -> 
					let cover_hd_id = List.hd s_cfg_cover_list in
					let bb_input_hd = List.hd bb_input_list in
					if ((bb_input_hd.blk_id) <> cover_hd_id) then false
					else true
	in
is_same
;;
(**************************************************************************************)
let taint_cover d_cfg s_cfg bb_range_tbl=
	let seq_start = ref 0 in
	let seq_long = ref 0 in
	
	let bb_input_list = ref [] in
	let s_cfg_cover_list = ref [] in
	(*let seq_list = ref [] in*)
	
	let s_blk_id = ref (BB(0)) in
	let is_low = ref false in

	let bbid_list = Vine_cfg.cfg_nodes d_cfg in
	let bbid_list = List.rev bbid_list in
	let () = List.iter (fun d_blk_id->
		let d_sl = d_cfg#get_info (d_cfg#find d_blk_id) in
		(*let d_sl = List.rev d_sl in*)
		let () = List.iter(fun d_stmt->
		let () = match d_stmt with
			| Label l -> 
				let is_addr = label_is_addr l in
				let () = match is_addr with
					| true->
						let addr =  self_label_to_addr l in
						(*let () = Printf.printf "before enter exclude_bb\n" in	*)
						is_low := exclude_bb s_cfg bb_range_tbl addr s_cfg_cover_list;
						let () = match !is_low with
							| true ->
								s_blk_id := List.hd !s_cfg_cover_list; 
							| false ->() 
						in
						(*let is_same_blk = same_s_blk  !s_cfg_cover_list !bb_input_list in*)					
								
								(*let bb_input = {blk_id = !s_blk_id; seq_start = !seq_start; seq_long = !seq_long} in
								let () = Printf.printf "taint_cover, add a input, id=%s, start=%d, end=%d\n" (bbid_to_string(!s_blk_id)) !seq_start ((!seq_start)+(!seq_long) )  in
								bb_input_list := bb_input::(!bb_input_list);
								seq_start := List.length !bb_input_list;
								seq_long := 0*)

						()
					| false->()
				in
				()
			| Comment str->
				let () = match !is_low with
					| true -> 
						let is_init = is_init_comment str in
						let () = match is_init with
							| true->
								let seq = get_taint_seq str in
								(*seq_list := seq::(!seq_list);
								seq_long := !seq_long + 1 ;*)
								let bb_input = {blk_id = !s_blk_id; seq = seq} in
								bb_input_list := bb_input::(!bb_input_list);
								(*Printf.printf "BBID=%s, INIT_INPUT_SEQ=%ld, str=%s\n" (bbid_to_string !s_blk_id) seq str*)
							| false->()
						in
						()
					| false -> ()
				in
				()
			| Move(lval, rval)->
				match !is_low with
					| true -> 
						let () = match rval with
							| Lval rlv->
								let () = match rlv with
								| Temp ((i,s,t))->
									(*let () = Printf.printf "temp s=%s\n" s in*)
									let is_temp_input = is_temp_var s in
									let () = match is_temp_input with
										| true ->
											let  seq = get_temp_seq s in
											let bb_input = {blk_id = !s_blk_id; seq = seq} in
											bb_input_list := bb_input::(!bb_input_list);
											(*seq_list := seq::(!seq_list);
											seq_long := !seq_long + 1 ;*)
											(*Printf.printf "BBID=%s, temp_INIT_INPUT_SEQ=%ld\n" (bbid_to_string !s_blk_id) seq*)
										| _ -> ()
									in
									()
								| _->()
								in
								()
							| _ -> ()
						in
						()
					| false -> ()
			| _->()
		in
		()
		)d_sl in
		()
		)bbid_list in
		
		(**d-cfg is from back to end*)
		bb_input_list := List.rev (!bb_input_list);
		s_cfg_cover_list := List.rev (!s_cfg_cover_list);
(!bb_input_list, !s_cfg_cover_list)
;;
(*************************************************************************************)
let get_blk_match_tbl ida_file =
	let block_matchings = Hashtbl.create  0 in 
(*TODO: build real table*)
block_matchings
;;
(**************************************************************************************)
let mk_taint_tag taint_range_file=
	let taint_range_file_ch = open_in  taint_range_file in
	let ref_tag_range_list = ref [] in
	let ref_color = ref 0 in
	
	let rec read_line f_ch ref_tag_range_list ref_color=
		let ret = try(
				let str = input_line taint_range_file_ch in
				let str_len = String.length str in
				let index  = String.index str ' ' in
				let start_str = String.sub str 0 index in
				let end_str = String.sub str (index+1) (str_len-index-1) in 
				let tag = 
					{start_byte_no = (Int32.of_string start_str); end_byte_no = (Int32.of_string end_str); color = !ref_color} 
				in
				ref_color := !ref_color + 1;
				ref_tag_range_list := tag::!ref_tag_range_list;
				read_line f_ch ref_tag_range_list ref_color;
				)
		with End_of_file -> ()
		in		
		()
	in
	
	let () = read_line taint_range_file_ch ref_tag_range_list ref_color in
	
	let () =  close_in taint_range_file_ch in
	ref_tag_range_list := List.rev !ref_tag_range_list;
!ref_tag_range_list
;;
(**************************************************************************************)
let print_tag_range_list tag_range_list=
	let () = List.iter(fun x -> 
		Printf.printf "start_byte_no=%ld, end_byte_no=%ld, color=%d\n" x.start_byte_no x.end_byte_no x.color 
		)tag_range_list in
	()
;;

(**not duplicate*)
let print_bb_color bb_tag_tbl trace_id=
	let () = Printf.printf "print_bb_color%d: bb_tag_tbl's length is %d" trace_id (Hashtbl.length bb_tag_tbl) in
	let () = Hashtbl.iter (fun id color_list -> 
		let () = Printf.printf "\nprint_bb_color: %s\n" (bbid_to_string(id)) in
		List.iter(fun color-> 
			Printf.printf "%d " color 
			)color_list
		) bb_tag_tbl 
	in
()
;;

let get_color seq tag_range_list=
		(*let find_fun x =
			if (seq >= x.start_byte_no) then
			(
				if (seq <= x.end_byte_no) then true
				else false
			)
			else false
		in *)
		
		let find_fun x =
			 ((seq >= x.start_byte_no) && (seq <= x.end_byte_no))
		in
		
		let color =try(
			let tag_range = List.find	find_fun tag_range_list		in
			tag_range.color			
		)
		with Not_found -> 
			(
				Printf.printf "Exception: get_color: get_color not found,seq=%ld\n" seq;
				let () = print_tag_range_list tag_range_list in
				-1
			)
		in
color
;;

let is_exist l x = 
	try (List.find (fun y -> (y=x)) l; true) 
	with Not_found ->false 
;;

(**a bb's all input seqs to tag*)
let seq_to_tag blk_id (seq:int32) (tag_range_list:tag_range list) ref_bb_tag_tbl=
		let ref_color_list = ref [] in
		
		let ret = try(
			let tag = Hashtbl.find !ref_bb_tag_tbl	blk_id in
			ref_color_list := tag.color_list;	
			true
			)
		with Not_found -> 
			false
		in
		
		let color = get_color seq tag_range_list in
		let exist = is_exist (!ref_color_list) color in	
		let () = match exist with
			| true -> ()
			| false -> 
				ref_color_list := color::(!ref_color_list);
				let tag = {tag_blk_id=blk_id; color_list=(!ref_color_list)} in
				Hashtbl.add !ref_bb_tag_tbl blk_id tag
		in
()
;;

(**all bb of the list's input to tag*)
let intern_byte_to_tag bb_input_list tag_range_list=
	let ref_bb_tag_tbl = ref (Hashtbl.create (List.length bb_input_list)) in
	
	let () = List.iter(fun bb_input -> 
		(*let ref_color_list = ref [] in*)
		let () = seq_to_tag  
							(bb_input.blk_id) 
							(bb_input.seq) 
							tag_range_list 
							ref_bb_tag_tbl 
		in
		()
	)bb_input_list 
	in
	
!ref_bb_tag_tbl
;;
	
let byte_to_tag bb_input_list1 bb_input_list2 tag_range_list=
	let bb_tag_tbl1 = intern_byte_to_tag bb_input_list1 tag_range_list in
	let bb_tag_tbl2 = intern_byte_to_tag bb_input_list2 tag_range_list in
(bb_tag_tbl1, bb_tag_tbl2)
;;

(****************************************************************************************)
let print_bb_info bb_input_list s_cfg_cover_list trace_id=
	let () = List.iter(fun id -> 
		Printf.printf "s_cfg_cover_list%d %s " trace_id (bbid_to_string(id)) 
		)s_cfg_cover_list in
	
	let () = List.iter(fun input -> 
		Printf.printf "bb_input_list%d: %s : input_seq=%ld\n"trace_id (bbid_to_string(input.blk_id)) (input.seq)
		)bb_input_list
	in
	
	()
;;

let print_cover_list l t_id = 
	let () = Printf.printf "cover_list length:%d\n" (List.length l) in
	List.iter(fun x -> 
		Printf.printf "cover_list%d: %s\n" t_id (bbid_to_string(x))
		)l
;;
(***************************************************************************************)
let filter_cover_l s_cfg_cover_list=
	let ref_new_cover_list = ref [] in	
	let () = List.iter(fun id -> 
		let exist = is_exist !ref_new_cover_list id in
		let () = match exist with
			| true ->() 
			| false -> 
				ref_new_cover_list := id::(!ref_new_cover_list)
		in
		()
		)s_cfg_cover_list in
	
	ref_new_cover_list := List.rev !ref_new_cover_list;
!ref_new_cover_list
;;
(****************************************************************************************)
let handle_one_trace ida_file d_cfg t_id =
	let (bb_range_tbl, s_cfg) =static_analyze_db ida_file in
		(*let () = print_cfg s_cfg "static_cfg" in 
	let () = print_cfg cfg "appreplay_cfg" in*)
	let (bb_input_list,s_cfg_cover_list) = taint_cover d_cfg s_cfg  bb_range_tbl in
	(*let s_cfg_cover_list = filter_cover_l s_cfg_cover_list in*)
	
		(*let () = print_bb_info bb_input_list2 s_cfg_cover_list2 2 in
	let () = print_cover_list s_cfg_cover_list2 t_id in*)
	
(bb_input_list, s_cfg_cover_list)
;;
(****************************************************************************************)
(*pm*)
let appreplay args trace ida_file trace2 ida_file2 taint_range_file=
	let ref_count = ref 0 in
	(**taint range file*)
	let  tag_range_list = mk_taint_tag taint_range_file in
	(*let () = print_tag_range_list tag_range_list in*)
	(**for 1st trace*)
  let cfg = Vine_cfg.prog_to_cfg trace in
	let (bb_input_list1, s_cfg_cover_list1) =  handle_one_trace ida_file cfg 1 in 
	(*let cfg = neg_post cfg in*)
	
	(**for 2nd trace*)
	let cfg2 = Vine_cfg.prog_to_cfg trace2 in
	let (bb_input_list2, s_cfg_cover_list2) =  handle_one_trace ida_file2 cfg2 2 in
	(*let cfg = neg_post cfg in*)
	
	
	(**byte input to color*)
	(*let (bb_tag_tbl1, bb_tag_tbl2) = byte_to_tag 
			bb_input_list 
			bb_input_list2  
			tag_range_list
	in*)
	
	(*let () = print_bb_color bb_tag_tbl1 1 in
	let () = print_bb_color bb_tag_tbl2 2 in*)
	
	(*let block_matchings_tbl = get_blk_match_tbl ida_file in
	let () = Trace_diff.cal_trace_diff 
						s_cfg
						s_cfg2 
						s_cfg_cover_list (*for sequece of the BB*) 
						s_cfg_cover_list2  
						bb_tag_tbl1 (*for color check of the BB*)
						bb_tag_tbl2
						block_matchings_tbl true true ida_file
	in*)
	(*(*for deubg*)
	let rec print_bb_input count seq_list seq_start seq_long =
		match  count with
			| seq_long -> ()
			| _->
				let () = Printf.printf "%ld  " (List.nth seq_list (seq_start+count)) in
				print_bb_input (count+1) seq_list seq_start seq_long
	in
	
	let () = List.iter (fun bb_input->
		let () = Printf.printf "\n%s : seq_start=%d seq_long=%d" (bbid_to_string(bb_input.blk_id)) (bb_input.seq_start) (bb_input.seq_long) in
		print_bb_input 0 seq_list (bb_input.seq_start) (bb_input.seq_long)
		)bb_input_list in
	(*for deubg end*)*)
	(*pm end*)
	
	(****STP just for trace1******)
(*  let () = Vine_cfg.coalesce_bb cfg in
 	let cfg = Ssa.cfg2ssa cfg in
  let cfg = Ssa.to_vine cfg in

  let trace = Vine_cfg.normal_cfg_to_prog cfg in
  let (dl,sl) = trace in
  let () = debug "Tranlating trace to GCL..." in
  let gcl = 
    if is_straightline sl then
      Gcl.of_straightline sl
    else
      Gcl.of_trace trace in
(*   let qvar = findvar dl "post" in *)
  let q = findpost sl in
(*   let q = Lval(Temp(qvar)) in *)
  let () = debug "Computing wp..." in
  let (simp1, simplast) =
    if args.simplify
    then
      (Vine_opt.constant_fold_more (fun _->None),
       Vine_opt.simplify_faster <@ Vine_alphavary.alpha_vary_exp)
    else (id,id)
  in
  let wp = simplast(Wp.calculate_wp simp1 q gcl) in
  let () =
    if args.wpout_file <> "" then writeir args.wpout_file (dl, [ExpStmt wp])
  in
  let () =
    if args.stpout_file <> "" then writestp args.stpout_file wp
  in
  *)
   () 
;;
(**************************************************************************************)
(*pm end*)
(**************************************************************************************)
let lval_to_decl lv =
  match lv with
  | Temp(v) -> v
  | Mem(v, _,_) -> v

let unwrap_lets exp =
  let decl_set = ref VarSet.empty in

  let vis =
object(s)
  inherit nop_vine_visitor
  method visit_alvalue l =
    let v = lval_to_decl l in
    assert (not (VarSet.mem v !decl_set));
    decl_set := VarSet.add v !decl_set;
    DoChildren

  method visit_rlvalue l = 
    s#visit_alvalue l
end 
  in

  let rec loop stmts exp =
    match exp with
    | Let(lv, rv, lexp) ->
        let mov = Move(lv,rv) in
        let _ = stmt_accept vis mov in
        loop
          (mov::stmts)
          lexp
    | _ -> 
        let decls = 
          VarSet.elements !decl_set in
        (List.rev stmts), decls, exp
  in
  loop [] exp
    

let deadcode trace =
  let (dl, sl) = trace in
  let post_var = findvar dl "post" in
  let mem_var = findvar dl "mem_arr" in

  let cfg = Vine_cfg.prog_to_cfg trace in
  ignore(Vine_dataflow.do_dce cfg ~globals:[post_var; mem_var]); 
  Vine_cfg.normal_cfg_to_prog cfg

(*   let exit_node = Vine_cfg.exit_node cfg in *)
(*   let entry_node = Vine_cfg.entry_node cfg in *)
(*   let gcl = Gcl.of_cfg cfg exit_node entry_node in *)
(*   let q = Lval(Temp(post_var)) in *)
(*   let simp = (fun x->x) in *)
(*   let wp = Wp.calculate_wp simp q gcl in *)
(*   let stmts, decls, exp = unwrap_lets wp in *)
(*   (\*  Vine.Block(decls, stmts @ [Move(Temp("post", bool_t), exp)]) *\) *)
(*   (\* drop the last exp, which is just "post" *\) *)
(*   (decls, stmts) *)
;;

if true
then Gc.set
  { (Gc.get()) with
    (* Gc.verbose = 0x00c; *)
    Gc.max_overhead = 999999 };;

let _ = Sys.signal Sys.sigusr1 (Sys.Signal_handle (fun _ ->
  prerr_endline "Manually triggered heap compaction."; Gc.compact())) ;;


let parse_cmdline =
  let cmdlineargs = {
    trace_file = "";
    irout_file = "";
    wpout_file = "";
    stpout_file = "";
    state_file = "";
		ida_file = ""; (*pm*)
    state_ranges = [];
		(*pm start*)
		trace_file2 = "";
   irout_file2 = "";
    wpout_file2 = "";
    stpout_file2 = "";
    state_file2 = "";
		ida_file2 = ""; 
		taint_range_file="";
    state_ranges2 = [];
		(*pm end*)
    typecheck = false;
    eval = false;
    concrete = false;
    dead = false;
    early_exit = false;
    simplify = false;
    include_all = false;
    use_thunks = false;
    use_post_var = true;
    assertion_on_var = false; 
    deend = true;
    deend_multi = false;
    verify_expected = false;
    (*conc_mem_idx = true;*)(*pm*)
		conc_mem_idx = false;
    prop_consts = false;
    remove_unknowns = false;
    flatten = false;
  } in
  
  let arg_spec = 
    [
      (**** input sources ****)
     ("-trace", 
      Arg.String (fun s -> cmdlineargs.trace_file <- s),
      "FILE\tread trace from FILE") ;
			
			("-trace2", 
      Arg.String (fun s -> cmdlineargs.trace_file2 <- s),
      "FILE\tread trace from FILE") ; (*pm*)
			
     ("-ida", 
      Arg.String (fun s -> cmdlineargs.ida_file <- s),
      "FILE\tread ida.db from FILE") ;(*pm*)
			
     ("-ida2", 
      Arg.String (fun s -> cmdlineargs.ida_file2 <- s),
     "FILE\tread ida.db from FILE") ;(*pm*)

		 ("-tag",
			Arg.String (fun s-> cmdlineargs.taint_range_file<-s),
			"");(*pm*)

     ("-state", 
      Arg.String (fun s -> cmdlineargs.state_file <- s),
      "FILE\tread process state from FILE") ;
			
			("-state2", 
      Arg.String (fun s -> cmdlineargs.state_file2 <- s),
      "FILE\tread process state from FILE") ; (*pm*)

     (**** options and transformations ****)
     ("-state-range",
      Arg.String 
        (fun s -> 
           assert (cmdlineargs.state_file <> "");
           Scanf.sscanf 
             s 
             "0x%Lx:0x%Lx" 
             (fun x y -> 
                cmdlineargs.state_ranges <- (x,y)::cmdlineargs.state_ranges)
        ),  
      "0xDEAD:0xBEEF\tinitialize range 0xDEAD to 0xBEEF") ;
			
			("-state-range2",
      Arg.String 
        (fun s -> 
           assert (cmdlineargs.state_file2 <> "");
           Scanf.sscanf 
             s 
             "0x%Lx:0x%Lx" 
             (fun x y -> 
                cmdlineargs.state_ranges2 <- (x,y)::cmdlineargs.state_ranges2)
        ),  
      "0xDEAD:0xBEEF\tinitialize range 0xDEAD to 0xBEEF") ;(*pm*)

     ("-conc-mem-idx",
      Arg.Bool (fun b -> cmdlineargs.conc_mem_idx <- b),
      "\trewrite non-tainted mem indexes to literal values");

     ("-prop-consts",
      Arg.Bool (fun b -> cmdlineargs.prop_consts <- b),
      "\tUse evaluator to do constant propagation");

     ("-flatten",
      Arg.Bool (fun b -> cmdlineargs.flatten <- b),
      "\tflatten IR");

     ("-use-thunks",
      Arg.Bool (fun b -> cmdlineargs.use_thunks <- b),
      "\tuse eflag thunks (lazy eflag computation).");

     ("-use-post-var",
      Arg.Bool (fun b -> cmdlineargs.use_post_var <- b),
      "\tuse a post-condition variable instead of asserts.");

     ("-assertion-on-var",
      Arg.Bool (fun b -> cmdlineargs.assertion_on_var <- b),
      "\tcreate a unique boolean variable for each assertion.");

     ("-deend",  
      Arg.Bool (fun b -> cmdlineargs.deend <- b),
      "\tDeendianize all memory accesses");

     ("-deend_multi",
      Arg.Bool (fun b -> cmdlineargs.deend_multi <- b),
      "\tWhen de-endianizing, use separate arrays by access size");

     ("-verify-expected",
      Arg.Bool (fun b -> cmdlineargs.verify_expected <- b),
      "\tAdd asserts to check whether propagated inputs have expected"
      ^ " values.\n\t\t(Only makes sense with -concrete)"
     );  

     ("-include-all",
      Arg.Unit (fun () -> cmdlineargs.include_all <- true),
      "\tDisasm and include all instructions, not just tainted.");

     ("-remove-unknowns",
      Arg.Bool (fun b -> cmdlineargs.remove_unknowns <- b),
      "\tRemoves some unsupported instructions");

     ("-typecheck", 
      Arg.Unit (fun () -> cmdlineargs.typecheck <- true),
      "\tType check the generated IR");

     ("-concrete",
      Arg.Unit (fun () -> cmdlineargs.concrete <- true),
      "\tAssign concrete values to input (when building from exec trace)");

     ("-dead",
      Arg.Unit (fun () -> cmdlineargs.dead <- true), 
      "\tperform dead code elimination");

     ("-early-exit",
      Arg.Unit (fun () -> cmdlineargs.early_exit <- true),
      "\tadd early exits when post-condition cannot be satisfied");

     ("-simplify",
      Arg.Unit (fun () -> cmdlineargs.simplify <- true),
      "\tapply simplifications to the WP");

     (**** outputs ****)
     ("-ir-out", 
      Arg.String (fun s -> cmdlineargs.irout_file <- s),
      "FILE\toutput trace ir to FILE") ;
     
     ("-wp-out",
      Arg.String (fun s -> cmdlineargs.wpout_file <- s),
      "FILE\toutput WP to FILE in IR format");

     ("-stp-out",
      Arg.String (fun s -> cmdlineargs.stpout_file <- s),
      "FILE\toutput trace to FILE in stp format") ;

     ("-eval",
      Arg.Unit (fun () -> cmdlineargs.eval <- true),
      "\trun trace through the evaluator");

    ]
  in
  let () = 
    Arg.parse 
      arg_spec 
      (fun s -> ()) 
      "Usage: appreplay [options] <tracefile> " 
  in
  cmdlineargs
;;




if not !Sys.interactive then
  let args = parse_cmdline in
	let bb_range_list=ref [] in

  deend_use_multi args.deend_multi;
  deend_use args.deend;

  (* get trace from one source *)
  print_string "Getting trace\n";
  flush stdout;
  let prog =
    Printf.printf "statefile %s\n" args.state_file;
    List.iter 
      (fun (x,y) -> Printf.printf "%Lx %Lx\n" x y)
      args.state_ranges;


    (* build ir trace from execution trace *)
    if (args.trace_file <> "")
    then (
      let tracker = new track_opval_filter in
      let filters = 
        [if args.include_all then new disasm_all else new disasm_tainted;
         new print_filter;
         new handle_outsw;
         new constrain_mem_accesses args.state_ranges;
         new make_straightline_filter;
         (tracker :> eh_filter);
         new initialize_operands_small tracker args.verify_expected;
         new uniqify_labels;
        ]
      in
      let filters = 
	if args.remove_unknowns then 
	  filters @ [new unknowns_filter]
	else 
	  filters
      in

(*       let filters = *)
(*         if args.conc_mem_idx then *)
(*           filters @ [new conc_idx_filter] *)
(*         else *)
(*           filters *)
(*       in *)
      let filters =
        if args.concrete then
          filters @ [new initialize_input_symbols tracker]
        else
          filters
      in
      let filters =
        if true then (* XXX make optional *)
          filters @ [new break_dep_chains_filter tracker]
        else
          filters
      in
      let trace_prog, trace_insns = 
        disasm_trace ~use_thunks:args.use_thunks args.trace_file filters in
      
      (* Initialize memory regions from state file *)
      let memvar = Asmir.gamma_lookup trace_prog.gamma "$mem" in
      let mem_inits = 
	Temu_state.generate_range_inits args.state_file args.state_ranges memvar
      in
      let trace_prog = 
        {trace_prog with prog_setup_ir =
            Block([],mem_inits)::trace_prog.prog_setup_ir} in

      let prog = 
        trace_to_prog ~deend:args.deend trace_prog trace_insns in

      (* XXX should make this a transformation step.
         may need to make asserts_to_post more generic, though *)
      let prog =
        if args.assertion_on_var then
          let prog = create_assert_variable prog in
            prog
        else
          prog
      in

      let prog =
        if args.use_post_var then
          let prog, post_var = asserts_to_post prog in
          prog
        else
          prog
      in


      prog
    )
    (* read ir trace from file *)
(*     else if (args.irin_file <> "")  *)
(*     then ( *)
(* (\*       Vine_absyn.strip_nums := true;  *\) *)
(*       Vine_parser.parse_file args.irin_file  *)
(*     ) *)
    else
      raise (Arg.Bad "No input specified")
  in

(*pm start*)

    (* get trace2 from one source *)
  print_string "Getting trace2n";
  flush stdout;
  let prog2 =
    Printf.printf "statefile2 %s\n" args.state_file2;
    List.iter 
      (fun (x,y) -> Printf.printf "%Lx %Lx\n" x y)
      args.state_ranges2;


    (* build ir trace from execution trace *)
    if (args.trace_file2 <> "")
    then (
      let tracker = new track_opval_filter in
      let filters = 
        [if args.include_all then new disasm_all else new disasm_tainted;
         new print_filter;
         new handle_outsw;
         new constrain_mem_accesses args.state_ranges;
         new make_straightline_filter;
         (tracker :> eh_filter);
         new initialize_operands_small tracker args.verify_expected;
         new uniqify_labels;
        ]
      in
      let filters = 
	if args.remove_unknowns then 
	  filters @ [new unknowns_filter]
	else 
	  filters
      in

      let filters =
        if args.concrete then
          filters @ [new initialize_input_symbols tracker]
        else
          filters
      in
      let filters =
        if true then (* XXX make optional *)
          filters @ [new break_dep_chains_filter tracker]
        else
          filters
      in
      let trace_prog, trace_insns = 
        disasm_trace ~use_thunks:args.use_thunks args.trace_file2 filters in
      
      (* Initialize memory regions from state file *)
      let memvar = Asmir.gamma_lookup trace_prog.gamma "$mem" in
      let mem_inits = 
	Temu_state.generate_range_inits args.state_file2 args.state_ranges2 memvar
      in
      let trace_prog = 
        {trace_prog with prog_setup_ir =
            Block([],mem_inits)::trace_prog.prog_setup_ir} in

      let prog2 = 
        trace_to_prog ~deend:args.deend trace_prog trace_insns in

      (* XXX should make this a transformation step.
         may need to make asserts_to_post more generic, though *)
      let prog2 =
        if args.assertion_on_var then
          let prog2 = create_assert_variable prog2 in
            prog2
        else
          prog2
      in

      let prog2 =
        if args.use_post_var then
          let prog2, post_var = asserts_to_post prog2 in
          prog2
        else
          prog2
      in


      prog2
    )
    else
      raise (Arg.Bad "No input2 specified")
  in
(*pm end*)
(********** tranformations ***************)
  (* propagate all constants forward. *)
  let prog = 
    if (args.prop_consts || args.conc_mem_idx ) then
      prop_constants prog (not args.prop_consts) 
    else
      prog
  in

  (* flatten ir *)
  let prog =
    if (args.flatten) then
      flatten_blocks prog
    else
      prog
  in

  if (args.typecheck) then (
    print_string "Typechecking\n";
    flush stdout;
    (* type check *)
    Vine_typecheck.typecheck prog
  );

  print_string "Performing transformations\n";
  let prog = 
    if (args.dead) then 
      deadcode prog
    else 
      prog
  in

  let prog =
    if (args.early_exit) then
      let (dl,sl) = prog in
	match Exectrace.post_vars_to_cjmps (findvar dl "post") (Block(dl,sl))
	with
	    Block(dl,sl) -> (dl,sl)
	  | _ -> raise (Invalid_argument "appreplay")
    else
      prog
  in
  (* type check *)
  if (args.typecheck) then (
        print_string "Typechecking again\n";
        flush stdout;
        Vine_typecheck.typecheck prog
  );

(*************** outputs **********************)
  print_string "Outputting~\n";
  flush stdout;
	Printf.printf "After flush_stdout\n";

  (* evaluate *)
  if (args.eval) then (
    Printf.printf "Evaluating\n%!";
    let evaluator = new Vine_ceval.concrete_evaluator prog in
    let _ = evaluator#run in
    ()
  );

  (* output ir file *)
  if (args.irout_file <> "") then (
    Printf.printf "Writing ir to %s\n%!" args.irout_file;
    let ir_channel = open_out args.irout_file in
      pp_program (output_string ir_channel) prog;
      close_out ir_channel
   ) ;
	
	  
  (* output stp file *)
  if (args.stpout_file <> "" || args.wpout_file <> "")
  then (
    let t1 = Unix.gettimeofday () in
    appreplay args prog args.ida_file prog2 args.ida_file2 args.taint_range_file;
    let t2 = Unix.gettimeofday () in
    Printf.printf "Time to create sym constraint from TM: %f\n%!"
	(t2 -. t1) 
  )

;;


(*
   if Array.length Sys.argv < 3
   then  
   print_string "Usage: appreplay <tracefile> <model_output>\n"; exit 0;;
   
   let (trace, fout) = 
   if Sys.argv.(1) = "-m"
   then (Marshal.from_channel(open_in Sys.argv.(2)), Sys.argv.(3))
   else 
   (Vine_parser.parse_channel (open_in Sys.argv.(1)), Sys.argv.(2))
   ;;
   debug(Printf.sprintf "Read %d statements.\n" (List.length trace));;
   appreplay trace fout
*)
