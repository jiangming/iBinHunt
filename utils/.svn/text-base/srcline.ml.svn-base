(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
open Vine
open Vine_tovine
open Vine_cfg
open Vine_util
open Exectrace ;;
open Sqlite3;;

module List = ExtList.List ;;
module String = ExtString.String ;;

let header_update = ref(true);;
let int_tbl_header = ref([]);;
let int_tbl_rows = ref([]);;

let ref_fun_range_list1 = ref [] ;;
let ref_fun_range_list2 = ref [] ;;

let app_debug_ch = open_out ("debug/appreplay.debug")
let fun_name1_ch = open_out ("debug/fun_name1.debug")
let fun_name2_ch = open_out ("debug/fun_name2.debug")


type cmdlineargs_t = {
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

  
(*let ref_tag_range_list = [] *)

(***************************************appreplay**********************************************************************)
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

let is_exist l x = 
	try (List.find (fun y -> (y=x)) l; true) 
	with Not_found ->false 
;;
(****************************************************************************************)
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


let get_fun_range ida_file ref_fun_range_list =
	let () = Printf.printf "get_fun_range %s\n" ida_file in
	(**function dfg*)
	let dfg_list = ref [] in
	let sqlite_db_handle = db_open ida_file in
	let query4 = "select name, start_address, end_address from functions" in
	let ret = exec  sqlite_db_handle ~cb:store_tbl  query4 in
	let () = Printf.printf "return = %s\n" (Sqlite3.Rc.to_string ret) in
	let query_tbl_header4 = !int_tbl_header in
	let query_tbl_rows4 = !int_tbl_rows in
	let () = header_update := true in
	let () = int_tbl_rows := [] in
	
	let () = List.iter (fun r ->  
		let name = (List.hd r) in
		let sa = Int64.of_string (List.hd (List.tl r)) in
		let ea = Int64.of_string (List.hd (List.tl (List.tl r))) in
		ref_fun_range_list := (name, sa, ea)::(!ref_fun_range_list);
	) query_tbl_rows4 in
	
	let ret = db_close sqlite_db_handle in
()
;;

(****************************************************************************************)
(*pm*)
let appreplay args trace ida_file trace2 ida_file2 =
	(**for 1st trace*)
	let fun_name_tbl1 = Hashtbl.create 1000 in
	let () =  get_fun_range ida_file ref_fun_range_list1 in
	
	let () = List.iter(fun (name, sa, ea) ->
		Printf.fprintf app_debug_ch "ref_fun_range_list1: %s, %Lx, %Lx\n" name sa ea ; 
		)!ref_fun_range_list1 in
	
  let d_cfg1 = Vine_cfg.prog_to_cfg trace in
	let () = Printf.printf "After prog_to_cfg\n" in
	let cfg = d_cfg1 in
	
	let is_low = ref false in

	let bbid_list1 = Vine_cfg.cfg_nodes d_cfg1 in
	let bbid_list1 = List.rev bbid_list1 in
	let () = List.iter (fun d_blk_id->
		let d_sl = d_cfg1#get_info (d_cfg1#find d_blk_id) in
		let () = List.iter(fun d_stmt->
		let () = match d_stmt with
			| Label l -> 
				let is_addr = label_is_addr l in
				let () = match is_addr with
					| true->
							let addr =  self_label_to_addr l in
							is_low := is_low_addr addr ;
							let () = match !is_low with
								| true ->
									let () = try(
									 let (name, sa, ea) = List.find (fun (n, s, e) -> ((addr >= s) && (addr <= e))) !ref_fun_range_list1 in
									 let () = Hashtbl.replace fun_name_tbl1 name name in
										()
									)
									with Not_found -> 
										(
											let () = Printf.printf "addr1 not found: %Lx\n" addr in
											()
											)
									in
									()
								| false -> ()
						 in
						(**)
						()
				 | false->() (*end match is_addr with*)
				in
				()
			| _->()
		in
		()
		)d_sl in
		()
		)bbid_list1 in
			

	
(**for 2nd trace*)
	let fun_name_tbl2 = Hashtbl.create 1000 in
	let () =  get_fun_range ida_file2 ref_fun_range_list2 in
  let d_cfg2 = Vine_cfg.prog_to_cfg trace2 in
	let is_low = ref false in

	let bbid_list2 = Vine_cfg.cfg_nodes d_cfg2 in
	let bbid_list2 = List.rev bbid_list2 in
	let () = List.iter (fun d_blk_id->
		let d_sl = d_cfg2#get_info (d_cfg2#find d_blk_id) in
		let () = List.iter(fun d_stmt->
		let () = match d_stmt with
			| Label l -> 
				let is_addr = label_is_addr l in
				let () = match is_addr with
					| true->
							let addr =  self_label_to_addr l in
							is_low := is_low_addr addr ;
							let () = match !is_low with
								| true ->
										let () = try(
									 let (name, sa, ea) = List.find (fun (n, s, e) -> ((addr >= s) && (addr <= e))) !ref_fun_range_list2 in
									 let () = Hashtbl.replace fun_name_tbl2 name name in
										()
									)
									with Not_found -> 
										(
											let () = Printf.printf "addr2 not found: %Lx\n" addr in
											()
											)
									in
									()
								| false -> ()
						 	in
						()
				 | false->() (*end match is_addr with*)
				in
				()
			| _->()
		in
		()
		)d_sl in
		()
	)bbid_list2 in
		
	
(**print*)
let () = Hashtbl.iter (fun name _  -> Printf.fprintf fun_name1_ch "%s\n" name) fun_name_tbl1 in
let () = Hashtbl.iter (fun name _  -> Printf.fprintf fun_name2_ch "%s\n" name) fun_name_tbl2 in
	
		(***************************trace_diff***************************************************************)
	close_out app_debug_ch;
	close_out fun_name1_ch;
	close_out fun_name2_ch;	

	(*pm end*)
	  
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
  
    let t1 = Unix.gettimeofday () in
    appreplay args prog args.ida_file prog2 args.ida_file2 ;
    let t2 = Unix.gettimeofday () in
    Printf.printf "Time to create sym constraint from TM: %f\n%!"
	(t2 -. t1) ;

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
