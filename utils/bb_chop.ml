(*date: 10-19-2009*)
(*Made by: mengpan*)
(*usage: flat cfg of whole program, CFG chopping*)

open Vine;;
open Vine_tovine
open Vine_cfg;;
open Vine_util;;
open Exectrace ;;
open Mycg;;
module List = ExtList.List;;


type bb_range = 
{
	id: bbid;
	start_addr: int64;
	end_addr: int64;
};;



let usage = "callstrings [options]* outfile\n" in
let infile = ref "" in 
let irchopfile = ref "" in 
let irfile = ref "" in

let infile_set = ref false in 
let arg_name s = 
  infile := s; 
  infile_set := true 
in

let debug_ch = ref (open_out "debug/callinsts.debug") in
let cfgprint_debug_ch = ref(open_out "debug/cfgprint.debug") in
let cgprint_debug_ch = ref(open_out "debug/cgprint.debug") in
let callgraph_dot = ref(open_out "debug/dot/callgraph.dot") in
let out_debug = open_out "debug/debug.txt" in
let out_vineIR = open_out "debug/vineIR" in
let debug_flag = ref(true) in
let cfgprint_debug_ch = ref(open_out "pm_cfg_chop_bb.debug") in

let wpout_file = "debug/wp.txt" in
let stpout_file = "debug/stp.stp" in

let print_cfgs cfgs_list file_append =
 let counter = ref 0 in
  List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
    let bbid_list = Vine_cfg.cfg_nodes current_cfg in  (** return a list of all basic blocks id's in a cfg *)
    let () = Printf.fprintf !cfgprint_debug_ch "\nProcessing cfg # %d corresponding to function %s. " !counter n  in
    let () = Printf.fprintf !cfgprint_debug_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
    (** let () = Printf.fprintf !cfgprint_debug_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in*)
    let () = List.iter (fun bblock_id ->
    	let () = Printf.fprintf !cfgprint_debug_ch "\t Looking at basic block id %s\n" (Vine_cfg.bbid_to_string bblock_id) in
	let block_pred_list = Vine_cfg.bb_pred current_cfg bblock_id in
	let block_succ_list = Vine_cfg.bb_succ current_cfg bblock_id in
	let () = Printf.fprintf !cfgprint_debug_ch "\t\t Predecessors: " in
	let () = List.iter (fun b_id ->
	        Printf.fprintf !cfgprint_debug_ch "%s " (Vine_cfg.bbid_to_string b_id)
	) block_pred_list in
	let () = Printf.fprintf !cfgprint_debug_ch "\n\t\t Successors: " in
	let () = List.iter (fun b_id ->
	        Printf.fprintf !cfgprint_debug_ch "%s " (Vine_cfg.bbid_to_string b_id)
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

	Printf.fprintf !cfgprint_debug_ch "\n\t\t Assembly:\n%s\n" asm
    ) bbid_list in
    counter := !counter + 1 
 ) cfgs_list
in


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
	
	let cmp_func (Function(_, _, _, _, _), g1) (Function(_, _, _, _, _), g2)=
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
	in
	
  (*let cfgs= List.sort cmp_func cfgs in*)
	cfgs;
in

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
in

let cfg_to_dot cfg1 file_append =

     let cfgdot_ch = open_out ("debug/dot/cfg_" ^ file_append ^ ".dot") in
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

     Dot.output_graph cfgdot_ch !g;
		 close_out cfgdot_ch
in

let print_ir dl sl finfo_l = 
	
	let () = output_string out_debug "********* Printing finfo_l **********\n" in
	let () =  List.iter (fun finfo -> 
		output_string out_debug finfo.name;
		output_char out_debug '\t';
		Printf.fprintf out_debug "%x" (Int64.to_int finfo.start_address);
		output_char out_debug '\t';
		Printf.fprintf out_debug "%x" (Int64.to_int finfo.end_address);
		output_char out_debug '\t';
		output_string out_debug (string_of_bool finfo.is_extern);
		output_char out_debug '\n' 
    ) finfo_l 
	in


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

	let () = output_string out_debug "******** Printing list of Functions ******\n" in
	let () = List.iter (fun s -> match s with
	| Function(n,t,d,e,Some(st)) -> 
	( 
		output_string out_debug "Label=\"";
		output_string out_debug n;
		output_string out_debug "\"\n";
		if e 
		then output_string out_debug "\tExternal=TRUE\n"
		else output_string out_debug "\tExternal=FALSE\n";
		output_string out_debug "\tSome Statments\n";
	)
	| Function(n,t,d,e,None) -> 
	(
		output_string out_debug "Label=\"";
		output_string out_debug n;
		output_string out_debug "\"\n";
		if e
		then output_string out_debug "\tExternal=TRUE\n"
		else output_string out_debug "\tExternal=FALSE\n";
		output_string out_debug "\tNo Statments\n";
	)
	| _ -> ()
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
in(*pm: end print_ir*)

(************************************print CFG************************************)
let print_cfg current_cfg str_file_append=
      
    let counter = ref 0 in
    let cfgprint_ch = ref(open_out ("debug/"^str_file_append^"_cfgprint.txt")) in
      
    let bbid_list = cfg_nodes current_cfg in
    
    let () = Printf.fprintf !cfgprint_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
    let () = Printf.fprintf !cfgprint_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
   
    let () = List.iter (fun bblock_id ->
    	let () = Printf.fprintf !cfgprint_ch "\t Looking at basic block id %s\n" (bbid_to_string bblock_id) in
	    let block_pred_list = bb_pred current_cfg bblock_id in
	    let block_succ_list = bb_succ current_cfg bblock_id in
	    let () = Printf.fprintf !cfgprint_ch "\t\t Predecessors: " in
	    let () = List.iter (fun b_id ->
	    Printf.fprintf !cfgprint_ch "%s " (bbid_to_string b_id)
    ) block_pred_list 
    in
      
	let () = Printf.fprintf !cfgprint_ch "\n\t\t Successors: " in
      
	let () = List.iter (fun b_id ->
	        Printf.fprintf !cfgprint_ch "%s " (bbid_to_string b_id)
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

	(*Printf.fprintf !cfgprint_ch "\n\t\t Assembly:\n%s\n" asm*)
	()
    ) bbid_list in

	let () = close_out !cfgprint_ch in 
  Printf.printf "print_cfg %s done!\n" str_file_append;
in

(*******************************WP*******************************************************)
let debug s =
  print_endline s
in

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

in

let writestp filename exp =
  let fd = open_out filename in
    flush stdout;
    Stp.to_file fd exp;
    close_out fd
in


let writeir filename prog =
  let oc = open_out filename in
  let ft = Format.formatter_of_out_channel oc in
  format_program ft prog;
  Format.pp_print_newline ft ()
in

let findpost sl =
  let retval = ref (0, "", REG_1) in
  let revsl = List.rev sl in
	
  let rec is_post stmt =
		let ()=Printf.printf "pm: is_post stmt=%s" (stmt_to_string stmt) in
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
      match List.find is_post revsl with (*pm: find the first element of revsl that satisfies is_post func*)
	  Move(Temp _, _) -> Lval(Temp(!retval))
	| _ -> raise (Invalid_argument "findpost")
    with 
       Not_found -> Constant(Int(REG_1, 1L))

in


let appreplay cfg simplify  finfo_l=
	
	let () = Vine_cfg.coalesce_bb cfg in	
	let cfg = Ssa.cfg2ssa cfg in
	
	(*let  () = Printf.printf "pm: appreplay-cfg2ssa BB(2) print \n" in
		let stmts = cfg#get_info (cfg#find (BB(2))) in
		let () = List.iter (fun s->
			Printf.printf "s=%s" (Ssa.stmt_to_string s)
			)stmts
		in
		let  () = Printf.printf "pm: BB(2) print end \n" in*)
		
  let cfg = Ssa.to_vine cfg in
  let trace = Vine_cfg.normal_cfg_to_prog cfg in
  let (dl,sl) = trace in
  
	(*let () = List.iter (fun s->
		Printf.printf "s=%s" (stmt_to_string s)
		)sl
		in
	let  () = Printf.printf "pm: appreplay print finish" in*)
		
		
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
    if simplify
    then
      (Vine_opt.constant_fold_more (fun _->None),
       Vine_opt.simplify_faster <@ Vine_alphavary.alpha_vary_exp)
    else (id,id)
  in
  let wp = simplast(Wp.calculate_wp simp1 q gcl) in
  let () =
    writeir wpout_file (dl, [ExpStmt wp])
  in
  let () =
    writestp stpout_file wp
  in
  
   () 
  
in
	(***********************************************************************)
let del_label_tail l_t = 
	let idx = String.rindex l_t '_' in
	let l = String.sub l_t 0 idx in
	l
in
(**********************************************************************************)
let self_label_to_addr (l_t:label) =
	(*let l = del_label_tail l_t in*)
  try
    Scanf.sscanf l_t "pc_0x%Lx" (fun x-> x)
  with
      _ -> 
	raise (VineError "label_to_addr given non address-like label")
in
(***********************************************************************)
let label_is_addr l = 
  try
    let _ = label_to_addr l in
    true
  with
    VineError _ -> 
      false
in
(***********************************************************************)

let make_BB_range cfg=
	let range_list = ref [] in
	let start_addr = ref 0L in
	let end_addr = ref 0L in
	
	let bbid_list = Vine_cfg.cfg_nodes cfg in
	let () = List.iter(fun id->
		let stmts = Vine_cfg.bb_stmts cfg id in
		let () = List.iter(fun stmt->
			let () = match stmt with
				| Label l->
					let is_addr = label_is_addr l in
					let () = match is_addr with
						| true->
							let addr =  self_label_to_addr l in
							let () = match !start_addr with
								| 0L->  start_addr := addr
								|_->()
							in
							end_addr := addr 
						| false->() 
					in	  
					()
				|_->()
		in
		()	
		)stmts in
	let bbr = [{id=id; start_addr= (!start_addr); end_addr= (!end_addr)}] in
	range_list := !range_list@bbr;
	start_addr := 0L;
	end_addr := 0L;
	)bbid_list in
!range_list
in
(**********************************************************************************)
let sort_list (range_list: (bb_range list)) =
	List.sort ~cmp:(fun  (recd1:bb_range) (recd2:bb_range)->
		if (recd1.start_addr = recd2.start_addr) then 0
		else if (recd1.start_addr > recd2.start_addr) then 1
		else	-1 
	) range_list
in 
(**********************************************************************************)
let print_range_list range_list str_file_append=
	let bb_range_ch = ref(open_out ("debug/"^str_file_append^"_bbrange")) in
	let () =  List.iter (fun range_bb->
			let () = Printf.fprintf !bb_range_ch "bbid: %s\n" (bbid_to_string (range_bb.id)) in
			let () = Printf.fprintf !bb_range_ch "start_addr: 0x%Lx\n" (range_bb.start_addr) in
			let () = Printf.fprintf !bb_range_ch "end_addr: 0x%Lx\n\n" (range_bb.end_addr) in
			()
	)range_list	in
	let () = close_out !bb_range_ch in 
()
in
(**********************************************************************************) 
let main argc argv = 
  (
    let speclist = Vine_tovine.speclist in 
    let myspeclist = [
    ("-chopir", Arg.Set_string(irchopfile),
     " <file> chop ir output file");
    ("-ir", Arg.Set_string(irfile),
     " <file> IR output file");
    ] in 
    let speclist = speclist @ myspeclist in
		 
    let () = Arg.parse speclist arg_name usage in 
     
    (*pm start flat*)
			let ()=Printf.printf "pm:before from_ida_flat\n" in
			let ()=Printf.printf "pm: flag_idadb_file=%s\n" !flag_idadb_file in
			let ((dl,sl),finfo_l) = Vine_tovine.from_ida_flat true !flag_idadb_file 1 in
			let ()=Printf.printf "pm:before replace_calls_and_returns\n" in
			let (dl,sl) = Vine_tovine.replace_calls_and_returns (dl,sl) finfo_l in
			let () = Printf.printf "pm: sl's num is %d\n" (List.length sl ) in		
			(*let finfo_l = Vine_tovine.do_function_heuristics finfo_l in*)
			let finfo_l = List.map (fun f -> 
			{f with name= (fix_name f.name) }
			) finfo_l in
			let ()=Printf.printf "pm:before Printing: finfo_l length=%d\n"  (List.length finfo_l) in
			let ()=Printf.printf "pm:before Printing: finfo_l.name = %s\n"  ((List.hd finfo_l).name) in

(*print IR*)
			(*let ()=print_ir dl sl finfo_l in*)

		(*to db*)
		(*let out_ir = open_out ("debug/ir__" ^ !flag_idadb_file) in
		let () = Marshal.to_channel out_ir (dl,sl,finfo_l) [] in
		let () = flush out_ir in
		let ()=close_out out_ir in *)
		
(*end print IR*)
(*callinst: make CFG*)
	
		let fl = List.filter (fun f ->
    match f with
     |   Function(n,_,_,false,Some(s)) when n <> Vine_tovine.unknown_addrs_function.name-> true 
     |   Function(n,_,_,true,_) when n <> Vine_tovine.unknown_addrs_function.name-> true 
     |   _ -> false
  ) sl in
	let fl = sl in
  let num_fun = (List.length finfo_l) in
	
	let ()=print_ir dl sl finfo_l in
	
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
 		(*let () = print_cfgs cfgs_f "binary" in*) 
		(*let ()=close_out !cfgprint_debug_ch in*)
	
		let (flat_f,flat_cfg)= List.hd cfgs_f in
		
		let ()=print_cfg flat_cfg "flat_cfg" in
		(*let ()=cfg_to_dot 	flat_cfg "flat_cfg" in*)
		(********************BB range*******************************)
		let rang_list = make_BB_range flat_cfg in
(*		let rang_list = sort_list rang_list in*)
		let () = print_range_list rang_list "" in
			(************************************cfg chop**************************************)
		(*let (f,flat_cfg) = (List.hd cfgs_f) in
		
		let bbid_bottom = (BB(110)) in
		let bbid_top = Vine_cfg.get_top_BB flat_cfg  bbid_bottom in
		
		let (dl, sl, bb_chop_cfg) = Vine_cfg.prog2bb_chop flat_cfg  bbid_top bbid_bottom Vine_cfg.BB_Exit in
		let () = Printf.printf "pm: after Vine_cfg.prog2bb_chop\n" in
		
		let bbidl=Vine_cfg.cfg_nodes bb_chop_cfg in
		
		let ()=Printf.printf "the bbid after chopping\n" in
    let ()=List.iter(fun bbid->
    let idstr=bbid_to_string bbid in
    Printf.printf "%s\n" idstr;
    )bbidl
    in
		
		let ()=cfg_to_dot 	bb_chop_cfg !flag_idadb_file in
		let ()=print_cfg bb_chop_cfg "bb_chop_cfg" in
		(************************Single chop path*************************************************************)
		let single_chop_cfg = Vine_cfg.single_path_cfg bb_chop_cfg bbid_bottom in
 
    let ()=print_cfg bb_chop_cfg "single_cfg" in
		let () = cfg_to_dot single_chop_cfg  "single_cfg"  in
	
			(*cfg chop end*)
			
		(*TODO: add post condition*)
		let (dl, sl) = Vine_cfg.cfg_to_prog single_chop_cfg BB_Entry BB_Exit in
		
		
		let(dl, sl) =  Exectrace.add_post (dl, sl) in
		(*let () = Printf.printf "pm: after Exectrace.addpost, sl.length=%d\n" (List.length sl) in 
		
		let () = List.iter (fun s->
		Printf.printf "s=%s" (stmt_to_string s)
		)sl
		in
		let  () = Printf.printf "pm: print finish" in*)
		
		(*let ()=print_ir dl sl finfo_l in*)
		
		let ((dl, sl), post_var) = Exectrace.asserts_to_post (dl, sl) in
		
		(*let () = List.iter (fun s->
		Printf.printf "s=%s" (stmt_to_string s)
		)sl
		in
		let  () = Printf.printf "pm: asserts_to_post print finish" in*)
		
		(*let (dl,sl) = Vine_alphavary.descope_program (dl, sl) in*)
    let  () = Printf.printf "--------------------->>>>>>>>" in
		let cfg_post =  Vine_cfg.stmts_to_bb dl sl in
		
		(*let  () = Printf.printf "pm: BB(4) print \n" in
		let stmts = cfg_post#get_info (cfg_post#find (BB(4))) in
		let () = List.iter (fun s->
			Printf.printf "s=%s" (stmt_to_string s)
			)stmts
		in
		let  () = Printf.printf "pm: BB(4) print end \n" in*)
		
		let ()=print_cfg cfg_post "post_cfg" in
		let () = cfg_to_dot cfg_post "post_cfg"  in
		(*add post condition end*)
			
			(****************************wp*********************************)
		let () = appreplay cfg_post false finfo_l in (*todo: prog_to_cfg*) *)
			(**************************wp  end*****************************)
		Printf.printf "bb_chop done!\n" ;
			(*pm end*)
 )
in
main (Array.length Sys.argv) Sys.argv;;