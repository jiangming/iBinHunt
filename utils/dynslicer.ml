(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   A driver to do dynamic slicing on straight-line IRs
   @author Juan Caballero
*)  
    
open Vine
open Vine_util
open Trace_slice
module D = Debug.Make(struct let name = Sys.argv.(0) and default=`Debug end)

(*=========================== globals ========================== *)
  let in_ir_file = ref ""
  let include_all_insn_in_ir = ref false
  let concretize_mem_indices = ref false
  let concretize_all_mem_indices = ref false
  let concrete_input = ref true
  let no_mem_vars = ref false
  let no_asserts = ref false
  let keep_labels = ref false
  let early_exit = ref false
  let slice_group_flag = ref false
  let slice_buf_flag = ref false
  let slice_vars_flag = ref false
  let buffer_start = ref Int32.zero
  let buffer_offset = ref 0
  let buffer_length = ref 0
  let group_list = ref []
  let var_list = ref []
  let slice_batch_size = ref 0
  let process_remaining_only = ref false
  let filter_unknowns = ref false
  let ignore_unsafe = ref false
  let no_mem_constraints = ref false
  let last_insn_num = ref 0L
  let ignore_origin = ref 0l
  let deendianize = ref true
(*============================================================== *)

(* Find output buffer (start,len) from netlog file *)
let get_output_from_netlog netlog_file =
  let ic =
    (try open_in netlog_file with Not_found -> failwith "Netlog file not found")
  in
  let ic = IO.input_channel ic in
  D.dprintf "Getting network input from: %s\n" netlog_file;
  let rec read_all_lines () =
    let line = IO.read_line ic in
    (* process line *)
    let re = Str.regexp "[ \t]+" in
    let param_list = Str.split re line in
    if ((List.nth param_list 0) = "ADDR:") then (
      let addr_str = "0x" ^ (List.nth param_list 1) in
      let first_output_pos = Int32.of_string addr_str in
      let output_len = int_of_string (Str.global_replace 
	(Str.regexp "\n$") "" (List.nth param_list 3)) 
      in
      (first_output_pos, output_len)
    )
    else read_all_lines ()
  in
  let (first, len) =
    try read_all_lines () with IO.No_more_input -> (Int32.zero,0) in
  IO.close_in ic;
  (first, len)

(* Driver for let simplification *)
let let_simplify ir_ssa_file = 
  (* Get IR from file *) 
  let prog = get_ir_from_file ir_ssa_file in
  let (dl,sl) = prog in

  (* Create VC for STP *)
  let vc = Stpvc.create_validity_checker () in
  let ctx = Vine_stpvc.new_ctx vc dl in

  (* Simplify using STP *)
  let simplified_exp = let_simplification vc ctx prog in

  (* Print stats *)
  let stats_vis = new stats_vis in
  let _ = print_exp_stats stats_vis simplified_exp in

  (* Print simplified formula as program to file *)
  let formula_filename = change_ext ir_ssa_file "formula" in 
  let formula_prog = exp_to_prog simplified_exp in
  write_prog formula_filename formula_prog

(* Driver for slicing variables defined through command line *)
let slice_vars ir_file varname_list =
  (* Parse the IR *)
  let prog = get_ir_from_file ~parser_strip_nums_flag:false ir_file in

  (* Get list of variables *)
  let (dl,_) = prog in
  let gamma = create_var_map dl in
  let process_name l name =
    try (let var = Hashtbl.find gamma name in var::l)
    with Not_found -> D.dprintf "Could not find var: %s\n" name; l
  in
  let group_var_list = List.fold_left process_name [] varname_list in

  (* Create visitor for slicing *)
  let vis = new slice_vis (List.length group_var_list) in

  (* Slice *)
  let _ = 
    slice_prog ~var_group:group_var_list ~early_exit_flag:!early_exit 
      ~keep_labels_flag:!keep_labels vis prog []
  in

  (* D.pdebug "Finished slicing\n"; *)
  let var_list = vis#get_var_started_list in
  let process_var var =
    (* Get slice *)
    let (_,name,_) = var in
    let id = vis#get_id_from_lv (Temp(var)) in
    let sl = vis#get_slice id in

    (* Extract declaration list from statement list *)
    let dl' = get_dl_from_sl sl in
    let sliced_prog = (dl',sl) in

    (* Output IR to file *)
    let output_file = name ^ ".slice" in
    write_prog output_file sliced_prog
  in
  List.iter process_var var_list

(* Driver for slicing all assert variables in program *)
let slice_asserts ir_file = 
  (* Parse the IR *)
  let prog = get_ir_from_file ~parser_strip_nums_flag:false ir_file in
  let (dl,sl) = prog in
  
  (* Get list of assert variables *)
  let assert_var_list = get_assert_vars sl in

  (* Split list of asser variables into smaller ones *)
  let assert_var_list_list = 
    if (!slice_batch_size > 0) 
    then split_list assert_var_list !slice_batch_size
    else [assert_var_list]
  in

  let slice_assert_list assert_var_list =
    (* Create visitor for slicing *)
    let vis = new slice_vis (List.length assert_var_list) in

    (* Slice *)
    let _ = 
      slice_prog  ~early_exit_flag:!early_exit 
	~keep_labels_flag:!keep_labels vis prog assert_var_list
    in

    (* D.pdebug "Finished slicing\n"; *)
    let var_list = vis#get_var_started_list in
    let process_var var = 
      (* Get slice *)
      let (_,name,_) = var in
      let id = vis#get_id_from_lv (Temp(var)) in
      let sl = vis#get_slice id in

      (* Extract declaration list from statement list *)
      let dl' = get_dl_from_sl sl in
      let sliced_prog = (dl',sl) in
	(* Output IR to file *)
	  let token_list = Str.split (Str.regexp "_") name in
	  let num_tokens = List.length token_list in
	  let output_file =
	    if (num_tokens >= 4) then (
	      let insn_counter_str =
		Printf.sprintf "%06d" (int_of_string (List.nth token_list 1))
	      in
	      "cond_" ^ insn_counter_str ^ "_" ^ (List.nth token_list 2) ^
		"_" ^ (List.nth token_list 3) ^ ".slice"
	    )
	    else name ^ ".slice"
	  in
	write_prog output_file sliced_prog
    in
    List.iter process_var var_list
  in List.iter slice_assert_list assert_var_list_list
 

(* Driver to create a union slice for a group of vars *)
let slice_group ir_file varname_list =
  (* Parse the IR *)
  let prog = get_ir_from_file ~parser_strip_nums_flag:false ir_file in

  (* Create list with all variables from group *)
  let (dl,_) = prog in
  let gamma = create_var_map dl in
  let process_name l name =
    try (let var = Hashtbl.find gamma name in var::l)
    with Not_found -> D.dprintf "Could not find var: %s\n" name; l
  in
  let group_var_list = List.fold_left process_name [] varname_list in

  (* Create visitor for slicing *)
  let vis = new slice_vis (List.length group_var_list) in

  (* Slice *)
  let _ = 
    slice_prog ~var_group:group_var_list ~early_exit_flag:!early_exit 
      ~keep_labels_flag:!keep_labels vis prog []
  in

  (* Print group slice *)
  let sl = vis#get_slice 0 in
  let dl' = get_dl_from_sl sl in
  let sliced_prog = (dl',sl) in

  (* Output IR to file *)
  let output_file = "group.slice" in
  write_prog output_file sliced_prog


(* Driver to slice all bytes in buffer *)
let slice_buffer
  ?(use_offset_names_flag=true)
  ir_file buf_start buf_off buf_len =

  (* Parse the IR *)
  let prog = get_ir_from_file ~parser_strip_nums_flag:false ir_file in
  let (dl,sl) = prog in

  (* Get list of buffer variables *)
  let buf_var_list = get_buffer_vars sl buf_start buf_off buf_len in

  (* Create visitor for slicing *)
  let vis = new slice_vis (List.length buf_var_list) in

  (* Slice *)
  let _ = 
    slice_prog  ~early_exit_flag:!early_exit 
      ~keep_labels_flag:!keep_labels vis prog buf_var_list 
  in

  (* D.pdebug "Finished slicing\n"; *)
  let var_list = vis#get_var_started_list in
  let process_var var =
    (* Get slice *)
    let (_,name,_) = var in
    let id = vis#get_id_from_lv (Temp(var)) in
    let sl = vis#get_slice id in

    (* Extract declaration list from statement list *)
    let dl' = get_dl_from_sl sl in
    let sliced_prog = (dl',sl) in

    (* Output IR to file *)
    let output_file =
      if (use_offset_names_flag) then (
        let curr_index = get_index (Temp(var)) in
        let curr_offset64 = 
          Int64.sub curr_index (Int64.of_int32 buf_start) in
        let curr_offset = Int64.to_int curr_offset64 in
        (Printf.sprintf "offset_%02d_addr_0x%Lx" curr_offset curr_index) ^ 
	  ".slice"
      )
      else ( name ^ ".slice")
    in
    write_prog output_file sliced_prog
  in
  List.iter process_var var_list


(* Driver to convert an IR program to SSA'ed IR *)
let to_ssa_prog ir_file = 
  (* Parse the IR *)
  let prog = get_ir_from_file ir_file in

  (* Convert program to SSA program *)
  let prog_from_ssa = 
    ir_to_ssa  ~translate_notation_flag:!no_mem_vars prog 
      ~ignore_unsafe:!ignore_unsafe 
  in

  (* Output IR to file *)
  let output_file = (ir_file^".ssa") in
  write_prog output_file prog_from_ssa

(* Driver to generate IR from trace *)
let trace_to_prog trace_file =
  (* Get IR from trace *)
  let prog = 
    get_ir_from_trace 
      ~include_all_insn_flag:!include_all_insn_in_ir 
      ~concretize_mem_indices_flag:!concretize_mem_indices
      ~concretize_all_mem_indices_flag:!concretize_all_mem_indices
      ~filter_unknowns_flag:!filter_unknowns
      ~no_asserts_flag:!no_asserts
      ~constrain_mems_flag:(not !no_mem_constraints)
      ~stop_ctr:!last_insn_num
      ~filter_origin:!ignore_origin
      ~deend_flag:!deendianize
      trace_file 
  in

  (* Select output file name *)
  let output_file =
    if (!concretize_all_mem_indices) then (change_ext trace_file "ir.concall")
    else if (!concretize_mem_indices) then (change_ext trace_file "ir.conc")
    else (change_ext trace_file "ir")
  in

  (* Write IR *)
  D.dprintf "Writing ir to %s\n%!" output_file;
  write_prog output_file prog

(* Concretize memory indices in a program *)
let concretize_program ir_file = 
  (* Parse the IR *)
  let prog = get_ir_from_file ir_file in

  (* Concretize memory indices *)
  D.pdebug "Concretizing memory indices";
  let conc_prog = make_concrete_indices prog in

  (* Output IR to file *)
  let output_file = (ir_file^".concall") in
  write_prog output_file conc_prog

(* Simplify all slices in a directory *)
let simplify_dir dir_name = 
  let file_type = Unix.stat dir_name in
  if file_type.Unix.st_kind <> Unix.S_DIR then failwith "Not a directory";
  (* D.pdebug "Reading directory"; *)
  let file_array =
    try Sys.readdir dir_name with _ -> failwith "Could not read dir"
  in

  (* Create VC for STP *)
  let vc = Stpvc.create_validity_checker () in

  let process_file filename = 
    let token_list = Str.split (Str.regexp "\\.") filename in
    if ((List.length token_list > 1) && (List.nth token_list 1) = "slice") 
    then (
      let formula_filename = change_ext filename "formula" in
      let exists = Sys.file_exists formula_filename in
      if ((not !process_remaining_only) || (not exists)) 
      then (
	let filename = dir_name ^ "/" ^ filename in
	(* Get IR from file *)
	let prog = get_ir_from_file filename in
	let (dl,sl) = prog in
	(* Simplify using STP *)
	let ctx = Vine_stpvc.new_ctx vc dl in
	let simplified_exp = let_simplification vc ctx prog in
	(* Print simplified formula as program *)
	let simple_prog = exp_to_prog simplified_exp in
	let new_filename = dir_name ^ ((List.nth token_list 0) ^ ".formula") in
	write_prog new_filename simple_prog
      )
    )
  in
  Array.iter process_file file_array;
  exit 0

(* Remove unknown statements from program *)
let remove_unknowns_in_prog filename = 
  (* Get IR from file *)
  let prog = get_ir_from_file filename in
  let (dl,sl) = prog in

  (* Remove unknowns *)
  let process_stmt stmt = 
    let (stmt',_) =  Vine.remove_unknowns stmt in
    stmt'
  in
  let sl' = List.map process_stmt sl in

  (* Output program *)
  write_prog "no_unknowns.ir" (dl,sl');
  exit 0


(* Convert memory access with concrete memory index to Temp variables in IR 
    NOTE: The input file should be a program in SSA notation 
*)
let rewrite_mems_in_ir ssa_filename = 
  (* Get IR from file *)
  let ssa_prog = get_ir_from_file ssa_filename in

  (* Translate mems *)
  let rewritten_prog = translate_ssa ssa_prog in

  (* Write program to file *)
  write_prog "no_mems.ir" rewritten_prog;
  exit 0


(* Parse program arguments *)
let parse_args () = 
  let usage = "USAGE: Check dynslicer -h\n" in
  let ignore_arg x = () in
  let read_buffer_data file =
    let  (output_buf_start, output_buf_len) = get_output_from_netlog file in
    if (!buffer_start = 0l) then buffer_start := output_buf_start;
    if (!buffer_length = 0) then buffer_length := output_buf_len
  in
  let set_slice_buf x = in_ir_file := x; slice_buf_flag := true in
  let set_slice_group x = in_ir_file := x; slice_group_flag := true in
  let set_slice_vars x = in_ir_file := x; slice_vars_flag := true in
  let add_to_slice_group s = group_list := (varname_notype s) :: !group_list in
  let add_to_slice_var_list s = var_list := (varname_notype s) :: !var_list in
  let set_buf_start s = buffer_start := Int32.of_string s in
  let rec arg_spec = 
    ("-all", Arg.Set(include_all_insn_in_ir), 
	"<> Include all instructions when generating the IR")
    ::("-batch", Arg.Set_int slice_batch_size, 
	"<int> Slice only this number of variables at a time. " ^ 
	"Use with -sliceasserts")
    ::("-bs", Arg.String set_buf_start, "<int> Fix the buffer start")
    ::("-bo", Arg.Set_int(buffer_offset), "<int> Fix the buffer offset")
    ::("-bl", Arg.Set_int(buffer_length), "<int> Fix the buffer length")
    ::("-conc", Arg.Set(concretize_mem_indices), 
	"<> Concretize memory indexes that are not tainted")
    ::("-concall", Arg.Set(concretize_all_mem_indices), 
	"<> Concretize all memory indexes. Concretizes tainted indices as well")
    ::("-concretize", Arg.String concretize_program,  
	"<string> Concretize memory indexes in given IR program")
    ::("-deend", Arg.Set(deendianize),  
	"<bool> Set/Unset deendianization for IR generation (default is on) 
	  Currently unsetting this does nothing")
    ::("-earlyexit", Arg.Set early_exit, 
	"<> Use with slice options to stop slicing when a memory read 
	  with tainted index is found")
    ::("-gvar", Arg.String add_to_slice_group, 
	"<string> Add variable with this name to the slice-group")
    ::("-unsafe", Arg.Set ignore_unsafe, 
	"<> Use with -nomem flag to ignore memory writes with tainted index")
    ::("-ir", Arg.String trace_to_prog, 
	"<string> Generate an IR program from given trace. Outputs file")
    ::("-keeplabels", Arg.Set(keep_labels), 
	"<> Use with slice options to keep labels in slice")
    ::("-last", Arg.String (fun s -> last_insn_num := Int64.of_string s), 
	"<int> Stop generating the IR after this number of instructions")
    ::("-let", Arg.String let_simplify, 
	"<string> Letify given IR program and simplify let using STP")
    ::("-letdir", Arg.String simplify_dir, 
	"<string> Apply -let to all slice files in given directory")
    ::("-noconcinput", Arg.Clear(concrete_input), 
	"<> Do not add concretize initializers for INPUT variables")
    ::("-nomem", Arg.Set(no_mem_vars), 
	"<> Use with -ssa to remove mem variables from final SSA-IR")
    ::("-nounknowns", Arg.Set(filter_unknowns), 
	"<> Use with -ir to remove unknown statements from resulting IR")
    ::("-noasserts", Arg.Set(no_asserts), 
	"<> Use with -ir to convert asserts to post condition")
    ::("-nomemconstraints", Arg.Set(no_mem_constraints), 
	"<> Use with -ir to avoid introducing constraints for memory accesses 
	  with tainted indices")
    ::("-filterorigin", Arg.String (fun s -> ignore_origin := Int32.of_string s),
        "<int32> Exclude instructions that use this origin. Use with -ir")
    ::("-readbuf", Arg.String read_buffer_data,
        "<string> Read buffer start and length from netlog file")
    ::("-removeunknowns", Arg.String remove_unknowns_in_prog, 
	"<string> Remove unknown stmt from given IR program")
    ::("-rewritemems", Arg.String rewrite_mems_in_ir, 
	"<string> Rewrite concrete memory indices to Temps in given IR program")
    ::("-remaining", Arg.Set process_remaining_only, 
	"<> Generate formulas only for slices without them in the directory." ^ 
	"Useful when running out of memory on simplifying slices in directory.")
    ::("-sliceasserts", Arg.String slice_asserts, 
	"<string> Slice all assert variables in given program")
    ::("-slicebuf", Arg.String set_slice_buf, 
	"<string> Create a slice for the given buffer or variable")
    ::("-slicegroup", Arg.String set_slice_group, 
	"<string> Create a single slice for a group of variables")
    ::("-slicevars", Arg.String set_slice_vars, 
	"<string> Create a slice for each variable defined using -var")
    ::("-ssa", Arg.String to_ssa_prog, 
	"<string> Convert given IR program to SSA form")
    ::("-var", Arg.String add_to_slice_var_list, 
	"<string> Add variable with this name to list of variables to slice")
    ::[] 
  in 
    (
      Arg.parse arg_spec ignore_arg usage
    )

(* main *)
let main () =
  (* Parse arguments *) 
  parse_args ();

  (* Find output var if needed *)
  if (!slice_buf_flag) then (
    D.dprintf "BUFFER START: 0x%lx LEN: %d\n" !buffer_start !buffer_length;
    let buf_off = Int32.of_int !buffer_offset in
    slice_buffer !in_ir_file !buffer_start buf_off !buffer_length
  );
  if (!slice_group_flag) then (
  	slice_group !in_ir_file !group_list
  );
  if (!slice_vars_flag) then (
    slice_vars !in_ir_file !var_list
  );
  exit 0;;

  main ();;
