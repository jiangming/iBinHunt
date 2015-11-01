open Vine;;
open Vine_tovine;;
open Vine_cfg;;
open Mycg;;
open Vine_idadb;;
open Sqlite3;;



let out_debug = open_out "debug.txt";;
let out_vineIR = open_out "vineIR";;


(*let debug_flag = ref(true);; *)
let debug_flag = ref(false);; 
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


let main argc argv = 
(

let db = Sqlite3.db_open argv.(1) in
 let infos = get_idainfos db in
 let i = List.hd infos in
 let (file_id, _, _, _, _, _, _, _, _, _, _, _) = i in
 let ((dl,sl),finfo_l) =  Vine_tovine.from_ida true argv.(1) file_id in

(*pm: filter the functions that have the same name, addr.This is a sqlite bug*)
	let filter_finfo_l = ref [] in
	let () = List.iter (fun f -> 
		
		let exist = List.exists (fun filter_f ->
			 ((f.name=filter_f.name) && (f.start_address = filter_f.start_address ) && (f.end_address =filter_f.end_address ))
			)  !filter_finfo_l 
		in
			
		let () = match exist with
			|true -> ()
			 |false ->
				filter_finfo_l := f::!filter_finfo_l;		 
				()
		in
		
		()		
		)finfo_l 
	in
	
	let finfo_l = !filter_finfo_l in
(*pm end*)

(*let ((dl,sl),finfo_l) = Vine_tovine.from_ida true argv.(1) 1 in(*peng*)
let ((dl,sl),finfo_l) = Vine_tovine.from_elf true argv.(1)  in*)

(* get 1/4 of dl,sl,finfo_l*)(*peng*)
(*let finfo_l = 
  List.fold_left (fun acc finfo1 ->
    if ((List.length acc) = (List.length finfo_l)/4) then
      (
	Printf.printf "over 1/4, cut; "; acc
      ) else (
	finfo1::acc
      )
  ) [] finfo_l
in

let dl = 
  List.fold_left (fun acc a ->
    if ((List.length acc) = (List.length dl)/4) then
      (
	Printf.printf "over 1/4, cut; "; acc
      ) else (
	a::acc
      )
  ) [] dl
in

let sl = 
  List.fold_left (fun acc a ->
    if ((List.length acc) = (List.length sl)/4) then
      (
	Printf.printf "over 1/4, cut; "; acc
      ) else (
	a::acc
      )
  ) [] sl
in*)


let (dl,sl) = Vine_tovine.replace_calls_and_returns (dl,sl) finfo_l in

let finfo_l = do_function_heuristics finfo_l in


let () = List.iter(fun f -> 
	Printf.fprintf out_debug "function name-before fix: %s\n" (f.name);
	)finfo_l 
in

let finfo_l = List.map (fun f -> 
	{f with name= (fix_name f.name) }
) finfo_l in

let () = List.iter(fun f -> 
	Printf.fprintf out_debug "function name-after fix: %s\n" (f.name);
	)finfo_l in



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
	  (** let () = Printf.printf "Looking for function name %s\n" n in *)(**MJ*) 
		let fixed_name = (fix_name n) in
		let finfo = List.find (fun f -> (f.name = fixed_name)) finfo_l in
	  (** let () = Printf.printf "Found function name %s=%s with %b=%b\n" n finfo.name e finfo.is_extern in *)(**MJ*) 
		Function(fixed_name,t,d,finfo.is_extern,st)
		)
	| a -> a
) sl in

(*let () = output_string out_debug "********* Printing finfo_l **********\n" in
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
in*)(*peng*)

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
		(**let () = Printf.printf "Looking for function name %s\n" n in *) (**MJ *) 
		let finfo = List.find (fun f -> (f.name = n)) finfo_l in
	  (**let () = Printf.printf "Found function name %s=%s with %b=%b\n" n finfo.name e finfo.is_extern in *) (**MJ*) 
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

let () = if !debug_flag then (

let () = output_string out_vineIR "Starting statements *****************************\n" in

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

)
in

let filepath = "/"^argv.(1) in
let slash = String.rindex filepath '/'  in
let lenth = String.length filepath  in
let sublen = lenth - slash - 1 in
let left = slash +1 in
(**
let () = Printf.printf "%s\n" filepath in
let () = Printf.printf "%d\n" left in
let () = Printf.printf "%d\n" sublen in
*)(**MJ*)
let filename = String.sub filepath left sublen in
let out_ir = open_out ("ir__" ^ filename) in
let () = Marshal.to_channel out_ir (dl,sl,finfo_l) [] in
let () = flush out_ir in
close_out out_ir
)


in

main (Array.length Sys.argv) Sys.argv;;

close_out out_vineIR;;
close_out out_debug;;







