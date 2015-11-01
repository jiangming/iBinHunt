open Vine;;
open Vine_tovine;;
open Vine_cfg;;
open Mycg;;

(*
let input1 = "a.out";;
let input2 = "a2.out";;
*)


let input1 = "asp_old.db";;
let input2 = "asp_new.db";;


let out_c = open_out "debug.txt";;
let out_main1 = open_out "main1.txt";;
let out_main2 = open_out "main2.txt";;
let out_prog = open_out "vine1";;
let out_prog2 = open_out "vine2";;





let in_ir_1 = open_in ("ir__" ^ input1) ;;
let in_ir_2 = open_in ("ir__" ^ input2) ;;
let (dl1,sl1,finfo_l1) = (Marshal.from_channel in_ir_1 : Vine.decl list * Vine.stmt list * Vine_tovine.funinfo_t list);;
let (dl2,sl2,finfo_l2) = (Marshal.from_channel in_ir_2 : Vine.decl list * Vine.stmt list * Vine_tovine.funinfo_t list);;
close_in in_ir_1;;
close_in in_ir_2;;


(*
output_string out_prog "Starting statements *****************************\n";;

List.iter (fun s -> 
	output_string out_prog "\t\t ********New statement**********\n";
	let () = match s with 
		| Function(l,None,fun_dl,ex,Some(st)) -> output_string out_prog "Vine.Function found:\n" ;
			output_string out_prog "\tLabel=\"";
			output_string out_prog l;
			output_string out_prog "\"\n";
			output_string out_prog "\tRetType=None\n";
			output_string out_prog "\tDecList=\"";
			List.iter (fun d ->
				output_string out_prog (decl_to_string d);
			) fun_dl;
			output_string out_prog "\"\n";
			if ex
			then output_string out_prog "\tExternal=TRUE\n"
			else output_string out_prog "\tExternal=FALSE\n";
			let () = match st with			
				| Block(bdl,bsl) -> 
					output_string out_prog "\tVine.Block found!\n";
					List.iter (fun s3 ->
						match s3 with 
							| Call(_,expr,_) ->
							  output_string out_prog "\t\tCall=\"";
							  output_string out_prog (exp_to_string expr);
							  output_string out_prog "\"\n";
							| Special(s4) -> output_string out_prog "\t\tSpecial: ";
									output_string out_prog s4;
									output_string out_prog "\n";
							| Jmp(expr) ->
		  					  output_string out_prog "\t\tJump=\"";
							  output_string out_prog (exp_to_string expr);
							  output_string out_prog "\"\n";
							| _ -> ();
						
					) bsl;
				| _ -> output_string out_prog "\tTop-level statment not a block!\n";
			in ();
		| Function(l,None,fun_dl,ex,None) -> output_string out_prog "Vine.Function found:\n" ;
			output_string out_prog "\tLabel=\"";
			output_string out_prog l;
			output_string out_prog "\"\n";
			output_string out_prog "\tRetType=None\n";
			output_string out_prog "\tDecList=\"";
			List.iter (fun d ->
				output_string out_prog (decl_to_string d);
			) fun_dl;
			output_string out_prog "\"\n";
			if ex
			then output_string out_prog "\tExternal=TRUE\n"
			else output_string out_prog "\tExternal=FALSE\n";
			output_string out_prog "\tNo Statments\n";
		| _ -> Printf.printf "top-level statement not a function!!!!!";	

        in
	output_string out_prog (stmt_to_string s);
	output_char out_prog '\n';

) sl1
;;

*)


(*
Printf.printf "starting decoding of 2nd file\n";;

(*let ((dl2,sl2),finfo_l2) = from_ida true "asp_new.db" 1;;*)
let (dl2,sl2, finfo_l2) = My_toir.translateFromElf input2;;

Printf.printf "finished decoding of 2nd file\n";;

let finfo_l2 = do_function_heuristics finfo_l2;;

let finfo_l2 = List.map (fun f -> 
		if ( (String.contains f.name '(') && (String.contains f.name ')') )
		then (
			let left_index = String.rindex f.name '(' in
			let fixed_name = String.sub f.name 0 left_index in
			{f with name=fixed_name}
		)
		else f
) finfo_l2;;


List.iter (fun d -> 
	output_string out_prog2 (decl_to_string d);
	output_char out_prog2 '\n';

) dl2
;;

let sl2 = List.map (fun s -> match s with
	| Function(n,t,d,e,st) -> 
		( let finfo = List.find (fun f -> (f.name = n)) finfo_l2 in
		 (* let () = Printf.printf "Found function name %s=%s with %b=%b\n" n finfo.name e finfo.is_extern in*)
		Function(n,t,d,finfo.is_extern,st)
		)
	| a -> a
) sl2;;

output_string out_prog2 "Starting statements *****************************\n";;

List.iter (fun s -> 
	output_string out_prog2 "\t\t ********New statement**********\n";
	let () = match s with 
		| Function(l,None,fun_dl,ex,Some(st)) -> output_string out_prog2 "Vine.Function found:\n" ;
			output_string out_prog2 "\tLabel=\"";
			output_string out_prog2 l;
			output_string out_prog2 "\"\n";
			output_string out_prog2 "\tRetType=None\n";
			output_string out_prog2 "\tDecList=\"";
			List.iter (fun d ->
				output_string out_prog2 (decl_to_string d);
			) fun_dl;
			output_string out_prog2 "\"\n";
			if ex
			then output_string out_prog2 "\tExternal=TRUE\n"
			else output_string out_prog2 "\tExternal=FALSE\n";
			let () = match st with			
				| Block(bdl,bsl) -> 
					output_string out_prog2 "\tVine.Block found!\n";
					List.iter (fun s3 ->
						match s3 with 
							| Call(_,expr,_) ->
							  output_string out_prog2 "\t\tCall=\"";
							  output_string out_prog2 (exp_to_string expr);
							  output_string out_prog2 "\"\n";
							| Special(s4) -> output_string out_prog2 "\t\tSpecial: ";
									output_string out_prog2 s4;
									output_string out_prog2 "\n";
							| Jmp(expr) ->
		  					  output_string out_prog2 "\t\tJump=\"";
							  output_string out_prog2 (exp_to_string expr);
							  output_string out_prog2 "\"\n";
							| _ -> ();
						
					) bsl;
				| _ -> output_string out_prog2 "\tTop-level statment not a block!\n";
			in ();
		| Function(l,None,fun_dl,ex,None) -> output_string out_prog2 "Vine.Function found:\n" ;
			output_string out_prog2 "\tLabel=\"";
			output_string out_prog2 l;
			output_string out_prog2 "\"\n";
			output_string out_prog2 "\tRetType=None\n";
			output_string out_prog2 "\tDecList=\"";
			List.iter (fun d ->
				output_string out_prog2 (decl_to_string d);
			) fun_dl;
			output_string out_prog2 "\"\n";
			if ex
			then output_string out_prog2 "\tExternal=TRUE\n"
			else output_string out_prog2 "\tExternal=FALSE\n";
			output_string out_prog2 "\tNo Statments\n";	
		| _ -> Printf.printf "top-level statement not a function!!!!!\n";	

        in
	output_string out_prog2 (stmt_to_string s);
	output_char out_prog2 '\n';

) sl2
;;


output_string out_c "********* Printing finfo_l2 **********\n";;


 List.iter (fun finfo -> 
	output_string out_c finfo.name;
	output_char out_c '\t';
	output_string out_c (Int64.to_string finfo.start_address);
	output_char out_c '\t';
	output_string out_c (Int64.to_string finfo.end_address);
	output_char out_c '\t';
	output_string out_c (string_of_bool finfo.is_extern);
	output_char out_c '\n' 
    ) finfo_l2 ;;


*)



let num_fun = (List.length finfo_l1);;

output_string out_c "\n\nSize of finfo list: ";;
output_string out_c (string_of_int (List.length finfo_l1));; 

let saddr_to_name_tbl1 = Hashtbl.create num_fun;;
List.iter (fun f -> 
	Hashtbl.add saddr_to_name_tbl1 f.start_address f.name
) finfo_l1 ;;

output_string out_c "\n\nSize of saddr_to_name_tbl1: ";;
output_string out_c (string_of_int (Hashtbl.length saddr_to_name_tbl1));; 


let (cmap1,fmap1) = Mycg.mk_callmap sl1 saddr_to_name_tbl1;;

output_string out_c "\n\nSize of cmap1 hashtable: ";;
output_string out_c (string_of_int (Hashtbl.length cmap1));; 

output_string out_c "\n\nSize of fmap1 hashtable: ";;
output_string out_c (string_of_int (Hashtbl.length fmap1));; 




output_string out_c "\nPrinting cmap1 hashtable:\n";;
Hashtbl.iter (fun fname cl ->
	output_string out_c fname;
	output_string out_c "\n";
	List.iter (function
		(called_name,st_no) ->
			output_string out_c "\t";
			output_string out_c called_name;
			output_string out_c "\t";
			output_string out_c (string_of_int st_no);
			output_string out_c "\n";
	) cl	

) cmap1;;


let (cg1,tbl1) = Mycg.create_callgraph (dl1, sl1)  saddr_to_name_tbl1;;


let out_dot = open_out "cg1.dot";;
Mycg.output_dot cg1 out_dot;;
close_out out_dot;;

let cg_tbl = Hashtbl.create 2;;
Mycg.iter_vertex (fun v ->
	Hashtbl.add cg_tbl v (label_of v)
) cg1;;

output_string out_c "\n\n*********Printing cg_tbl******\n";
Hashtbl.iter (fun v (i,l,s) ->
	output_string out_c "Vertex:\t";
	output_string out_c (string_of_int i);
	output_string out_c "\t";
	output_string out_c l;
	(*output_string out_c (stmt_to_string s);*)
	output_string out_c "\n";
) cg_tbl;;





let num_fun2 = (List.length finfo_l2);;

output_string out_c "\n\nSize of finfo_l2: ";;
output_string out_c (string_of_int (List.length finfo_l2));; 

let saddr_to_name_tbl2= Hashtbl.create num_fun2;;
List.iter (fun f -> 
	Hashtbl.add saddr_to_name_tbl2 f.start_address f.name
) finfo_l2 ;;

output_string out_c "\n\nSize of saddr_to_name_tbl2: ";;
output_string out_c (string_of_int (Hashtbl.length saddr_to_name_tbl2));; 


let (cmap2,fmap2) = Mycg.mk_callmap sl2 saddr_to_name_tbl2;;

output_string out_c "\n\nSize of cmap2 hashtable: ";;
output_string out_c (string_of_int (Hashtbl.length cmap2));; 

output_string out_c "\n\nSize of fmap2 hashtable: ";;
output_string out_c (string_of_int (Hashtbl.length fmap2));; 

let (cg2,tbl2) = Mycg.create_callgraph (dl2, sl2)  saddr_to_name_tbl2;;

let out_dot2 = open_out "cg2.dot";;
Mycg.output_dot cg2 out_dot2;;
close_out out_dot2;;



close_out out_prog;;
close_out out_prog2;;
close_out out_c;;
close_out out_main1;;
close_out out_main2;;







