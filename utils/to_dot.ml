open Vine
open Vine_tovine
open Vine_cfg
open Mycg
open Vine_util
open Exectrace 
open Sqlite3;;

module List = ExtList.List ;;
module String = ExtString.String ;;


(*****************************************************************************************************************)
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


(**************************************************************************)
let main argc argv = 
(
	let ida_file = argv.(1) in
	let cfg = static_analyze_db ida_file in
	let () = cfg_to_dot cfg ida_file in
	
()
)
;;
main (Array.length Sys.argv) Sys.argv;;
  