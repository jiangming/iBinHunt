open Vine
open Vine_tovine
open Vine_cfg
open Mycg


let debug_ch = ref (open_out "debug/callinsts.debug");;
let cfgprint_debug_ch = ref(open_out "debug/cfgprint.debug");;
let cgprint_debug_ch = ref(open_out "debug/cgprint.debug");;
let callgraph_dot = ref(open_out "debug/dot/callgraph.dot");;

let input_file1 = ref "";;
let totalcn = ref 0 in
let libfl = ref [] in

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


let print_cfgs cfgs_list file_append =
 let counter = ref 0 in
 List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
    let bbid_list = cfg_nodes current_cfg in  (** return a list of all basic blocks id's in a cfg *)
    let () = Printf.fprintf !cfgprint_debug_ch "\nProcessing cfg # %d corresponding to function %s. " !counter n  in
    let () = Printf.fprintf !cfgprint_debug_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in
    (** let () = Printf.fprintf !cfgprint_debug_ch  "\tIt has %d basic blocks.\n" (List.length bbid_list) in*)
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

	let () = Printf.fprintf !cfgprint_debug_ch "\n\t\t Assembly:\n%s\n" asm in
	(*pm*)
			let stmts = Vine_cfg.bb_stmts current_cfg bblock_id in
			let () = Printf.fprintf !cfgprint_debug_ch "\n\t\t IR:\n" in
			let () = List.iter(fun stmt->
			Printf.fprintf !cfgprint_debug_ch "%s\n" (stmt_to_string stmt)
			)stmts in
	()
	(*pm end*)
	
	(*let statement_list = current_cfg#get_info (current_cfg#find bblock_id) in
	  List.iter (fun s -> match s with
		       | Comment(comment_str) -> Printf.fprintf !cfgprint_debug_ch "\t\t\t%s\n" comment_str
			   (*| _ -> () *)
		       | _ -> Printf.fprintf !cfgprint_debug_ch "\t\t\t%s\n" (stmt_to_string s)
		    ) statement_list*) 
    ) bbid_list in
    counter := !counter + 1 
 ) cfgs_list
in

(*
generate function control flow graph dot script specified by input
@param cfgs_list: LList(Function(..) * cfg)
*)
let generate_cfgdot cfgs_list  =  
	let () = Printf.printf "please input the fuction name to generate CFG,input one name per line and input # to exit\n" in
	let fun_name = ref "" in
	let fun_find = ref 0 in
  fun_name := read_line();
while( !fun_name <> "#") do
   fun_find := 0;
   List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
    if (!fun_find = 0) && (n = !fun_name) then
			(
				let ()= Printf.printf "Generating %s control flow graph\n" (!fun_name) in
				fun_find:=1;  
				cfg_to_dot current_cfg n;  
		  )	
	 )cfgs_list;
	if !fun_find = 0 then
	  Printf.printf "no such function: %s \n" (!fun_name) ;
	fun_name := read_line() 
done
in

(*
generate function control flow graph dot script specified by input
@param cfgs_list: LList(Function(..) * cfg)
*)
let generateAll_cfgdot cfgs_list  =  

	let () = Printf.printf"Generate all functions CFG!\n" in
	let start = Sys.time() in
  List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
   cfg_to_dot current_cfg n; 
	 )cfgs_list;
	let finish = Sys.time() in
	Printf.printf "Generating %d CFGs!\n" (List.length cfgs_list );
	Printf.printf "Elapsed time: %f seconds\n" (finish -. start);

in

(*
output function control flow graph dot scripts specified by input num:
0: All Functions CFGs
1: CFG specified by users
@param cfgs_list: LList(Function(..) * cfg)
*)
let output_cfgdot cfgs_list =
let () = Printf.printf("Generating Function Control Flow Graph! Input Number:\n ") in
let () = Printf.printf("0: All Functions CFGs\n ") in
let () = Printf.printf("1: CFG specified by users\n") in
let num = ref 0 in
  num := int_of_string (read_line());
while ( (!num < 0 ) || (!num > 1)) do
  let () = Printf.printf(" A wrong number!  Please input again!\n") in
  num := int_of_string (read_line());
done;

if (!num = 0) then
  (
    generateAll_cfgdot cfgs_list;
  );
if (!num = 1) then
 (
  generate_cfgdot cfgs_list;
 )
in

(*get return address from cfg and bbid, mainly for retrieving the return adddress in new binary function *)
let get_r_from_cfg cfgs fname bbid =
  let r = ref 0x0L in
  let mkstr = String.create 9 in
  let () =  List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
		 if (n = fname) 
		 then 
		   (
		     (*let () = Printf.fprintf !debug_ch "cfg for function %s located\n" fname in*)
		     let bbid_list = cfg_nodes current_cfg in
		     let () = List.iter (fun bblock_id ->
					   if bblock_id = bbid 
					   then (
    					     (*let () = Printf.fprintf !debug_ch "basic block %s located \n" (bbid_to_string bblock_id) in*)
					     let block_pred_list = bb_pred current_cfg bblock_id in
					     let block_succ_list = bb_succ current_cfg bblock_id in
					     (*let () = Printf.fprintf !debug_ch "\t\t Successor is : " in
					     let () = List.iter (fun b_id ->
							       Printf.fprintf !debug_ch "%s " (bbid_to_string b_id)
							    ) block_succ_list in
					     let () = Printf.fprintf !debug_ch "\n" in*)
					     let sl = current_cfg#get_info (current_cfg#find (List.hd block_succ_list)) in(* we get the only successor first*)
					                                                                                                     (*we get the address of the first s in sl as the r*)
					     let asm = List.fold_left (fun acc s ->
     									 match s with
     									   | Comment str -> 
									       (
         	  								 let col_pos = (
          	   								   try String.index str ':'
           	   								   with
               	 								       Not_found -> 7
           	   								 ) - 7
           	 								 in
            									   acc ^ "\n" ^ (String.sub str col_pos (String.length str - col_pos)) 
            								       )
        								   | _ -> acc
      								      ) "" sl in
					     let asm = String.sub asm 0 8 in
					    
					    let () = String.set mkstr 0 '0' in
					    let () = String.set mkstr 1 'x' in
					    let () = String.set mkstr 2 (String.get asm 1) in
					    let () = String.set mkstr 3 (String.get asm 2) in
					    let () = String.set mkstr 4 (String.get asm 3) in
					    let () = String.set mkstr 5 (String.get asm 4) in
					    let () = String.set mkstr 6 (String.get asm 5) in
					    let () = String.set mkstr 7 (String.get asm 6) in
					    let () = String.set mkstr 8 (String.get asm 7) in
					   (*Printf.fprintf !debug_ch "\t\t Starting address of bb is : %Lx\n\n" (Int64.of_string mkstr);*)()
					   )
					   else ();
				      ) bbid_list in
		     ();
		 )
		 else ();
	      ) cfgs
  in
    r := (Int64.of_string mkstr);
(*    let () = Printf.fprintf !debug_ch "r is : %Lx\n" !r in*)
      r
in

(*
  get reachable function set from a specific function 
  @param: fname (old/new)cg
  @return: a list of function names
*)
let gl = ref [] in
let rec get_reachable_funs fname cg =
  let l = ref [] in
    if  not (List.exists (fun x -> x = fname) !gl)
    then gl := fname :: !gl
    else ();

    (*let () = Printf.printf "gl is : \n" in
    let () = List.iter(fun f ->
			 Printf.printf "%s ; \n" f;
		      ) !gl in*) 
  let () = Printf.fprintf !debug_ch "----------------recursively find succ in cg to get reachable funs : %s -----------------\n" fname in
  let () = DotGraph.iter_vertex (fun v ->
				   if fname = (snd(G.V.label v))
				   then 
				     (
				       let () = G.iter_succ (fun s -> 
							       if not (List.exists (fun x -> x = (snd(G.V.label s))) !gl)
							       then 
								 (
								   let ltemp = get_reachable_funs  (snd(G.V.label s)) cg in
								   let () = List.iter (fun u -> 
											 if not (List.exists (fun x -> x = u) !gl)
											 then l := u :: !l
										   else () ;
										      ) ltemp in
								     if not (List.exists(fun x -> x = (snd(G.V.label s))) !gl)
								     then l := (snd(G.V.label s)) :: !l
								 else ();
								 ) 
							       else ();
							    ) cg.graph v in
				     Printf.fprintf !cgprint_debug_ch "\n";
				     )
				   else ();
			 ) cg.graph in
    ();
    !l
in



(*
ifreached tells whether a basic block id2 is reachable from another one with id1  in the maximum common induced subgraph, 
para@ cfgs: old or new cfg set;
para@ fn: function name of the cfg we are examining here;
para@ id1, id2: basic block ids;
para@ subg: maximum common induced subgraph, it is a list of bbs;
*)

let ifreached cfgs fn id1 id2 subg = 
  let reached = ref false in
  let () =  List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
			 if (n = fn) 
			 then 
			   (
			     (*let () = Printf.fprintf !debug_ch "cfg for function %s located in ifconnected()\n" fn in
    			     let () = Printf.fprintf !debug_ch "basic block %s located \n" (bbid_to_string id1) in
			     let () = List.iter(fun id ->
						  Printf.fprintf !debug_ch "one successor of %s is : %s\n" (bbid_to_string id1) (bbid_to_string id);
						 ) (bb_succ current_cfg id1) in*)
			     let () = Printf.fprintf !debug_ch "%s and %s\n" (string_of_bool (List.exists (fun x -> x = id1) subg)) (string_of_bool (List.exists (fun x -> x = id2) subg)) in
			     let hisl = ref [] in
			     let rec ifsucc ida idb =
			       hisl := ida :: !hisl;
			       (*let () = Printf.fprintf !debug_ch "ifsucc %s and %s\n" (bbid_to_string ida) (bbid_to_string idb) in*)
			       let block_succ_list = bb_succ current_cfg ida in
			       (*let () = List.iter(fun id ->
						    Printf.fprintf !debug_ch "one successor of %s is : %s\n" (bbid_to_string ida) (bbid_to_string id);
						 ) block_succ_list in*)
			       let () = List.iter(fun succ_id ->
						    if List.exists (fun x -> x = succ_id) subg
						    then 
						      (
							(*let () = Printf.fprintf !debug_ch "%s's successor %s is in subgraph\n" (bbid_to_string ida) (bbid_to_string succ_id) in*)
							if succ_id = BB_Exit 
							then ()
							else
							  (
							    if succ_id = idb
							    then 
							      (
								(*let () = Printf.fprintf !debug_ch "idb is %s, turning true?\n" (bbid_to_string idb) in*)
								  reached := true
							      )
							    else
							      (
								if List.exists (fun x -> x = succ_id) !hisl
								then ()
								else ifsucc succ_id idb;
							      )
							  )
						      )
						    else (); (*Printf.fprintf !debug_ch "successor %s not in subgraph\n" (bbid_to_string succ_id);*)
						 ) block_succ_list in
				 ();
			     in
				 ifsucc id1 id2;
			   )
			 else ();
		      ) cfgs  in
    reached
in


(* callwhataddr:
input: cfgs, fn, bbid
return: if it is call bb, ret the address; if not, ret 0L
$$ could also be used to determine whether a bb is a call bb or not
*)
let callwhataddr cfgs fn bbid =
  let calleeaddr = ref 0L in
  let () = List.iter (fun (Function(n,_,_,_,_),cfg_f) -> 
	if  n = fn
	then 
	  (
	    (*let () = Printf.fprintf !debug_ch "and cfg found, let's find bbid for it\n" in*)
	    let bbid_list = cfg_nodes cfg_f in
	    let () = List.iter (fun bblock_id ->
		if bblock_id = bbid
		then (
		  let sl = cfg_f#get_info (cfg_f#find bblock_id) in
		  let () = List.iter (fun s ->
     			match s with
     			  | Comment str -> 
			      (
         	  		let call_pos = (
          	   		  try String.rindex str 'l'
           	   		  with
               	 		      Not_found -> 0
           	   		)
           	 		in
            			(*let () = Printf.fprintf !debug_ch "%s " str in
				let () = Printf.fprintf !debug_ch "call_pos = %d\n" call_pos in*)
				  if call_pos <> 0
				  then 
				    (
				      (*if ((String.get (String.sub str (call_pos-1) 1) 0) =  'l')*)
							if ((String.get (String.sub str (call_pos-1) 1) 0) =  'l') && ((String.get (String.sub str (call_pos-2) 1) 0) =  'a')
				      then 
					(
					  if (String.get (String.sub str (call_pos+2) 1) 0) = '0'
					    then (  
					      let mkstr = String.create 8 in
					      let () = String.set mkstr 0 (String.get (String.sub str (call_pos+2) 8) 0) in
					      let () = String.set mkstr 1 (String.get (String.sub str (call_pos+2) 8) 1) in
					      let () = String.set mkstr 2 (String.get (String.sub str (call_pos+2) 8) 2) in
					      let () = String.set mkstr 3 (String.get (String.sub str (call_pos+2) 8) 3) in
					      let () = String.set mkstr 4 (String.get (String.sub str (call_pos+2) 8) 4) in
					      let () = String.set mkstr 5 (String.get (String.sub str (call_pos+2) 8) 5) in
					      let () = String.set mkstr 6 (String.get (String.sub str (call_pos+2) 8) 6) in
					      let () = String.set mkstr 7 (String.get (String.sub str (call_pos+2) 8) 7) in
					      (*let () = String.set mkstr 8 (String.get (String.sub str (call_pos+2) 9) 8) in*)
					      (* let () = Printf.fprintf !debug_ch "mkstr is : %s\n" mkstr in*)
						calleeaddr := Int64.of_string mkstr
					    )
					  else ();
					)
				      else ();
				    )
				  else ();
            		      )
        		  | _ -> ();
      				     ) sl in
		    
		    Printf.fprintf !debug_ch ""
		)
		else ();
				  (*let statement_list = current_cfg#get_info (current_cfg#find bblock_id) in
				    List.iter (fun s -> match s with
				    | Comment(comment_str) -> Printf.fprintf !cfgprint_debug_ch "\t\t\t%s\n" comment_str
				  (*| _ -> () *)
				    | _ -> Printf.fprintf !cfgprint_debug_ch "\t\t\t%s\n" (stmt_to_string s)
				    ) statement_list*) 
			       ) bbid_list in
	      ();
	  )
	else ();
		     ) cfgs in
    !calleeaddr
in    


(*create crs edges from one unmatched bb, going one step down within the cfg
paras: 
cfgs, fn to determine the cfg
bbid: one unmatched bb to start
mcis: maximum common induced subgraph, excluding esunmatched part
mapped_ndtbl: some nodes have been created by mapping
*)
let one_step_down cfgs fn bbid mapped_ndtbl mcis =
  let () = Printf.fprintf !debug_ch "enter one_step_down on bbid : %s\n" (bbid_to_string bbid) in 
  let mnl = Hashtbl.fold(fun r (fn,bid) acc ->
			   bid :: acc;
			) mapped_ndtbl [] in

  let t = Hashtbl.create 0 in (*crs edge table (bbid,bbid)*)
  let () =  List.iter (fun (Function(n,_,_,_,_),current_cfg) ->
	if (n = fn) 
	then 
	  (
	    let hisl = ref [] in
	    let rec one_step ida =
	      hisl := ida :: !hisl;
	      (*let () = Printf.fprintf !debug_ch "ifsucc %s and %s\n" (bbid_to_string ida) (bbid_to_string idb) in*)
		let block_succ_list = bb_succ current_cfg ida in
		  (*let () = List.iter(fun id ->
		    Printf.fprintf !debug_ch "one successor of %s is : %s\n" (bbid_to_string ida) (bbid_to_string id);
		    ) block_succ_list in*)
		let () = List.iter(fun succ_id ->
			if List.exists (fun x -> x = succ_id) mnl (*in mcis and mapped (implies call bb)*)
			then 
			  (
			    if bbid <> succ_id
			    then Hashtbl.add t bbid succ_id
			  )
			else if (false = List.exists (fun x -> x = succ_id) mcis) && ((Int64.compare (callwhataddr cfgs fn succ_id) 0L) <> 0)(*unmatched call bb*)
			then 
			  (
			    if bbid <> succ_id
			    then Hashtbl.add t bbid succ_id
			  )
			else if (succ_id = BB_Exit)
			then () 
			else 
			  (
			    if List.exists (fun x -> x = succ_id) !hisl
			    then ()
			    else one_step succ_id
			  )
				  ) block_succ_list in
		  ();
	    in
	      one_step bbid;
	  )
	else ();
) cfgs  in
   t
in

(* countcallnodes:
input: cfgs, fn, address to name table
return: the number of call nodes within a function
*)
let countcallnodes cfgs fn a2n =
  let counts = ref 0 in
  let () = List.iter (fun (Function(n,_,_,_,_),cfg_f) -> 
	if  n = fn
	then 
	  (
	    (*let () = Printf.fprintf !debug_ch "and cfg found, let's find bbid for it\n" in*)
	    let bbid_list = cfg_nodes cfg_f in
	    let () = List.iter (fun bblock_id ->
		  let sl = cfg_f#get_info (cfg_f#find bblock_id) in
		  let () = List.iter (fun s ->
     			match s with
     			  | Comment str -> 
			      (
         	  		let call_pos = (
          	   		  try String.rindex str 'l'
           	   		  with
               	 		      Not_found -> 0
           	   		)
           	 		in
            			  (*let () = Printf.fprintf !debug_ch "%s; " str in
				   let () = Printf.fprintf !debug_ch "%d\n" call_pos in*)
				    if call_pos <> 0
				    then 
				      (
					if ((String.get (String.sub str (call_pos-1) 1) 0) =  'l') && ((String.get (String.sub str (call_pos-2) 1) 0) =  'a') (*call instruction*)
					then 
					  (
					    let () = Printf.fprintf !debug_ch "target address : 0x%Lx ----> " (callwhataddr cfgs fn bblock_id) in
                                            let targetfun = (
                                               try Hashtbl.find a2n (callwhataddr cfgs fn bblock_id)
                                               with Not_found -> "no such function"
                                            ) (*can not find in hashtbl*)
                                           in				    
                                           let () = Printf.fprintf !debug_ch "%s\n" targetfun in
					      counts := !counts + 1;
					  )
					else ();
				      )
				    else ();
            		      )
        		  | _ -> ();
      				     ) sl in
		    Printf.fprintf !debug_ch ""
			       ) bbid_list in
	      ();
	  )
	else ();
		     ) cfgs in
    !counts
in    


let main argc argv =
(
  let () = Random.init(0) in
  let () = input_file1 := argv.(1) in
  let in_ir_1 = open_in !input_file1 in
  let (dl1a,sl1a,finfo_list1a) = (Marshal.from_channel in_ir_1 : Vine.decl list * Vine.stmt list * Vine_tovine.funinfo_t list) in
	let ()=Printf.printf "pm: after Marshal.from_channel\n" in
  let () = close_in in_ir_1 in
  let (dl1, sl1, finfo_list1) = (dl1a, sl1a, finfo_list1a)in
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
  let num_fun1 = (List.length finfo_list1) in

	let ()=Printf.printf "pm: num_fun1=%d" num_fun1 in
  let saddr2name_tbl1 = Hashtbl.create num_fun1 in
  let () = List.iter (fun f -> 
	 Hashtbl.add saddr2name_tbl1 f.start_address f.name
  ) finfo_list1 in
  let () = Hashtbl.add saddr2name_tbl1 Int64.zero "non-direct-function-call" in
  let name2saddr_tbl1 = Hashtbl.create num_fun1 in

  let () = List.iter (fun f -> 
	 Hashtbl.add name2saddr_tbl1 f.name f.start_address 
  ) finfo_list1 in
	
	
  let (cg1, cg_tbl1) = Mycg.create_callgraph (dl1, sl1) saddr2name_tbl1 in
  let () = Printf.fprintf !debug_ch "call graph created ---------------\n" in
  let () = Printf.fprintf !cgprint_debug_ch "-----------------printing call graph-----------------\n\n" in
  let () = DotGraph.iter_vertex (fun v ->
				   let () = Printf.fprintf !cgprint_debug_ch "no. %d : %s\ncalls to : " (fst(G.V.label v)) (snd(G.V.label v)) in
				   let () = G.iter_succ (fun s -> 
						  Printf.fprintf !cgprint_debug_ch "no. %d : %s; " (fst(G.V.label s)) (snd(G.V.label s));
					       ) cg1.graph v in
				     Printf.fprintf !cgprint_debug_ch "\n\n";
			 ) cg1.graph in
	
	close_out !cgprint_debug_ch;
	let () = Mycg.output_dot cg1 !callgraph_dot in 
	close_out !callgraph_dot;
	
  let () = Printf.fprintf !debug_ch "****Creating and printing cfg lists (one cfg per function) binconv itself..." in

let ()=Printf.printf "pm: before make_cfgs\n" in
	 let cfgs1 = make_cfgs fl1 in
	let ()=Printf.printf "pm: after make_cfgs\n" in
  let () = Printf.fprintf !debug_ch "done\n" in

  let () = print_cfgs cfgs1 "binary" in
	close_out !cfgprint_debug_ch;
	let () = output_cfgdot cfgs1 in (**MJ*)
    
  let () =  List.iter (fun finfo -> 
			 if finfo.is_extern = false
			 then
			   (
			     let () = Printf.fprintf !debug_ch "until now, total # of call nodes is : %d\n" !totalcn in
			     let () = Printf.fprintf !debug_ch "processing function : %s\n" finfo.name in
			      totalcn := !totalcn + (countcallnodes cfgs1 finfo.name saddr2name_tbl1)
			   ) 
			 else 
			   (
			     libfl := finfo.name :: !libfl;
			   )
		      ) finfo_list1 in
    
    Printf.fprintf !debug_ch "cg & cfg done!\n";
		close_out !debug_ch;
)

in
main (Array.length Sys.argv) Sys.argv