(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  callstrings.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@gs3102.sp.cs.cmu.edu>
*
*  Started on  Tue Apr 24 13:42:26 2007 David Brumley
*  Last update Wed Jun 20 18:36:09 2007 David Brumley
*)
open Vine;;
open Vine_tovine
open Vine_cfg;;
open Vine_util;;
module List = ExtList.List;;

let usage = "callstrings [options]* outfile\n" in
let infile = ref "" in 
let csdotfile = ref "" in 
let chopdotfile = ref "" in 
let irchopfile = ref "" in 
let irfile = ref "" in
let start_chop_name = ref [] in 
let end_chop_addrs = ref [] in 
let root = ref "main" in 
let infile_set = ref false in 
let arg_name s = 
  infile := s; 
  infile_set := true 
in
let prepend reference arg =
  reference := arg :: !reference
in

(*pm*)

let debug_ch = ref (open_out "debug/callinsts.debug") in
let cfgprint_debug_ch = ref(open_out "debug/cfgprint.debug") in
let cgprint_debug_ch = ref(open_out "debug/cgprint.debug") in
let callgraph_dot = ref(open_out "debug/dot/callgraph.dot") in
let out_debug = open_out "debug/debug.txt" in
let out_vineIR = open_out "debug/vineIR" in
let debug_flag = ref(true) in

let cfgprint_debug_ch = ref(open_out "pm_cfg_chop_bb.debug") in

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

(*let cfg_to_dot cfg1 file_append =

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
in*)
(*pm end*)

let main argc argv = 
  (
    let speclist = Vine_tovine.speclist in 
    let myspeclist = [
    ("-chopstart", Arg.String(prepend start_chop_name),
    " <name> Add start chop function name (not address) for chop.");
    ("-chopend", Arg.String(prepend end_chop_addrs 
			    <@ Int64.of_string),
    " <addr> Add end address for chop.");
    ("-dot", Arg.Set_string(csdotfile), 
    " <file> cs dot output file.");
    ("-chopdot", Arg.Set_string(chopdotfile), 
    " <file> chop cs dot output file");
    ("-chopir", Arg.Set_string(irchopfile),
     " <file> chop ir output file");
    ("-ir", Arg.Set_string(irfile),
     " <file> IR output file");
    ("-root", Arg.Set_string(root),
     " <name> Set root of callstring (default is main)");
    ] in 
    let speclist = speclist @ myspeclist in 
    let () = Arg.parse speclist arg_name usage in 
    let flag_do_chop = 
      if List.length !end_chop_addrs > 0 then 
	true
      else 
	false 
    in 
    (*let (prog,funinfos) = Vine_tovine.to_program false  in*)
		let (prog,funinfos) = Vine_tovine.to_program true  in (*pm*) 
    let prog = Vine_tovine.replace_calls_and_returns prog funinfos in
    let () = 
      if !irfile <> "" then
	Vine.pp_program (output_string (open_out !irfile)) prog
      else () 
    in 
    let () = 
      if (!csdotfile = "") then () else  (
	let g = Vine_callstring.mk_csg prog !root in 
	  Vine_callstring.output_dot  g (open_out !csdotfile )
      )
    in
      if flag_do_chop then (
	assert (List.length !start_chop_name = 1);
	
	let ()=Printf.printf "pm: before standard_multichop\n" in
	
	let chop = Vine_callstring.standard_multichop prog !root
	  (List.hd !start_chop_name) !end_chop_addrs 
	in
	
	let ()=Printf.printf "pm: after standard_multichop\n" in
	
	  if !chopdotfile <> "" then 
	    Vine_callstring.output_dot  chop (open_out !chopdotfile);
	  if !irchopfile <> "" then (
	    let prog = Vine_callstring.csg_to_program chop in 
				Vine.pp_program (output_string (open_out !irchopfile)) prog;
			
			(*pm start flat*)
			(*
			let ()=Printf.printf "pm:before from_ida_flat\n" in
			let ()=Printf.printf "pm: flag_idadb_file=%s\n" !flag_idadb_file in
			let ((dl,sl),finfo_l) = Vine_tovine.from_ida_flat true !flag_idadb_file 1 in
			let ()=Printf.printf "pm:before replace_calls_and_returns\n" in
			let (dl,sl) = Vine_tovine.replace_calls_and_returns (dl,sl) finfo_l in
			
			let finfo_l = Vine_tovine.do_function_heuristics finfo_l in
			let finfo_l = List.map (fun f -> 
			{f with name= (fix_name f.name) }
			) finfo_l in
			let ()=Printf.printf "pm:before callinsts\n" in


(*print IR*)


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
	| a -> (Printf.printf "Warning: top-level statement not a function!"; a)	
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
		| _ -> Printf.printf "top-level statement not a function!!!!!";	

        in
	output_string out_vineIR (stmt_to_string s);
	output_char out_vineIR '\n';

) sl
in

let out_ir = open_out ("ir__" ^ !flag_idadb_file) in
let () = Marshal.to_channel out_ir (dl,sl,finfo_l) [] in
let () = flush out_ir in
let ()= close_out out_ir in 


(*end print IR*)
(*callinst*)

		let fl = List.filter (fun f ->
    match f with
     |   Function(n,_,_,false,Some(s)) when n <> Vine_tovine.unknown_addrs_function.name-> true 
     |   Function(n,_,_,true,_) when n <> Vine_tovine.unknown_addrs_function.name-> true 
     |   _ -> false
  ) sl in
	let fl = sl in
  let num_fun = (List.length finfo_l) in
	
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
 let () = print_cfgs cfgs_f "binary" in 
	let ()=close_out !cfgprint_debug_ch in
	(*pm: now can't use, must output to .db, and use callinst*)
			(*cfg chop*)
			let (f,flat_cfg) = (List.hd cfgs_f) in
			let (dl, sl, bb_chop_cfg) = Vine_cfg.prog2bb_chop flat_cfg  (BB(266)) (BB(77)) Vine_cfg.BB_Exit in
			let () = Printf.printf "pm: after Vine_cfg.prog2bb_chop\n" in
			
			let bbidl=Vine_cfg.cfg_nodes bb_chop_cfg in
			let ()=Printf.printf "the bbid after chopping\n" in
	    let ()=List.iter(fun bbid->
	    let idstr=bbid_to_string bbid in
	    Printf.printf "%s\n" idstr;
	    )bbidl
	    in
				
			(*cfg_to_dot 	bb_chop_cfg !flag_idadb_file;*)
			(*let out_ir = open_out ("ir_bbchop__" ^ !flag_idadb_file) in
			let () = Marshal.to_channel out_ir (dl,sl,finfo_l) [] in
			let () = flush out_ir in
			close_out out_ir ; *)
			
			(*let cfgprint_debug_ch = ref(open_out "debug/bb_cfgprint.debug") in
			let () = print_cfgs [(f ,bb_chop_cfg)] "binary" in 
			let ()=close_out !cfgprint_debug_ch in*)		
			
			let prog = (dl, sl) in
			let () = Vine.pp_program (output_string (open_out !irchopfile)) prog in
			let chop_ir = !irchopfile in
			let dot_index=String.rindex chop_ir '.' in
			let chop_ir_db= "ir__"^(String.sub chop_ir 0 dot_index)^".db" in
			let out_chop_ir_db = open_out chop_ir_db in
			Marshal.to_channel out_chop_ir_db prog [] ;
			
			(*cfg chop end*)
			
*)
			(*pm end*)
	  ) else ()
      ) else ()
 )
in
main (Array.length Sys.argv) Sys.argv;;

			