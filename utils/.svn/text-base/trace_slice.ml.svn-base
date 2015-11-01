(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   Functions needed to do dynamic slicing on straight-line IRs
    It provides auxiliary functionality for: 
      - Concretizing memory indices in an IR
      - Replacing Mem's with Temp's when memory indices concrete
      - Compute expression statistics
   
   @author Juan Caballero

TODO: 
  -Some of this functions do not belong here, they should be moved to dynslicer
*)

open Vine
open Vine_util
open Temu_trace
open Exectrace
module D = Debug.Make(struct let name = Sys.argv.(0) and default=`NoDebug end)

(* Compare two vars using the name *)
let varname_compare v1 v2 =
  let (_,name1,_) = v1 in
  let (_,name2,_) = v2 in
  Pervasives.compare name1 name2

(* Determine if a Vine.var is symbolic, i.e. is INPUT *)
let is_input_var vine_var =  
  let (_,var_str,var_type) = vine_var in
  if ((String.length var_str) < 5) then false
  (* else (((String.sub var_str 0 5) = "INPUT") && (var_type = REG_8)) *)
  else ((String.sub var_str 0 5) = "INPUT")

(* Determine if a Vine.var is an index, i.e. is idx_ *)
let is_index_var vine_var = 
  let (_,var_str,var_type) = vine_var in
  if ((String.length var_str) < 3) then false
  else (((String.sub var_str 0 3) = "idx") && (var_type = REG_32))

(* Determine if a Vine.var is a mem, i.e. is mem_ *)
let is_mem_arr_var vine_var =
  let (_,var_str,var_type) = vine_var in
  let is_array_type = 
    match var_type with 
      | Array _ -> true
      | _ -> false
  in
  if (not is_array_type) then false
  else if ((String.length var_str) < 7) then false
  else (((String.sub var_str 0 7) = "mem_arr"))

(* Split a list into a list of smaller lists *)
let split_list l size =
  let process_item (count,curr_l,all_l) item =
    if (count >= size) then (0,[item],curr_l :: all_l)
    else (count+1,item :: curr_l,all_l)
  in
  let (_,last_l,all_l) = List.fold_left process_item (0,[],[]) l in
  last_l :: all_l


(* Extract index from 'mem_at' variable. Otherwise return Int64.zero *)
let get_index lv =
  match lv with
    Temp(_,var_name,var_type) ->
    let token_list = Str.split (Str.regexp "_") var_name in
    if ((((List.nth token_list 0) = "mem") &&
      ((List.nth token_list 1) = "at")) && (var_type = REG_8))
      then (Int64.of_string (List.nth token_list 2))
      else 0L
    | Mem _ -> D.wprintf "Found mem lv: %s\n" (lval_to_string lv);
		failwith "There should not be any memory lvals"

(* Remove type from string representing variable *)
let varname_notype varname = 
  let re = Str.regexp ":" in
  let token_list = Str.split re varname in
    match (List.length token_list) with 
      1 -> List.hd token_list
      | 2 -> List.nth token_list 0
      | _ -> failwith "variable name with more than one semicolon"

(* Extract map of names to variables from declaration list *)
let create_var_map dl =
  let num_vars = List.length dl in
  let gamma = Hashtbl.create num_vars in
  let process_var var = 
  let (_,name,_) = var in
    Hashtbl.add gamma name var
  in
  let _ = List.iter process_var dl in
  gamma
  
(* Write IR program to file *)
let write_prog filename prog =
  D.dprintf "Writing IR to %s\n%!" filename;
  let out_ch = open_out filename in
  Vine.pp_program (output_string out_ch) prog;
  close_out out_ch

(** 
  Given a statement list, create an equivalent let expression 
  The process works on a reverse list and the already_reversed flag 
  indicates if the input list was already reversed. 
  If not reversed, it will be reversed before processing
    @param stmt_list an statement list
    @return let expression equivalent to input statement list
*)
let make_let_expr 
  ?(first_exp = Vine.Constant(Vine.Int(Vine.REG_1,1L)))
  stmt_list already_reversed = 

  let rev_stmt_list = 
    if (already_reversed) then stmt_list 
    else List.rev stmt_list
  in
  let rec les stmts acc =
    match stmts with
      [] -> acc
    | a :: b ->
      match a with
	Move(lhs,rhs) -> les b (Vine.Let(lhs,rhs,acc)) 
	| _ -> les b acc
	(* | _ -> failwith "Found something not Move or Let in SSA" *)
  in
  les rev_stmt_list first_exp


(**
  Remove (from IR) concrete initializers added by taintlog_to_trace with 
  the following exceptions:
  @param prog an ir program
  @return prog with input concrete initializers removed
*)
let remove_input_concrete_initializers prog =
let (dl,sl) = prog in
let process_statement l stmt =
  match stmt with
    | Move(Temp(var),exp) when (is_input_var var) -> 
	(match exp with 
	  | Constant(Int _) -> l
	  | _ -> stmt :: l)
    | Comment("initialize_input_symbols") -> l
    | _ -> stmt :: l
in
let sl' = List.fold_left process_statement [] sl in
let sl' = List.rev sl' in
(dl, sl')

(* Create integer FD from file_desc abstract type *)
let int_of_file_descr (fd : Unix.file_descr) =
  let obj = Obj.repr fd in
  if Obj.is_int obj then ( 
    let int_str = string_of_int (Obj.obj obj) in
    int_of_string int_str 
  )
  else failwith "int_of_file_descr: incorrect file descriptor"

(* Print STP expression to file *)
let stp_exp_to_file filename vc stp_exp =
  D.pdebug "Sending STP expression to file";
  let fd = Unix.openfile  
    filename [Unix.O_CREAT;Unix.O_TRUNC;Unix.O_WRONLY] 0o640 in
  let fd_int = int_of_file_descr fd in
  Libstp.vc_printExprFile vc stp_exp fd_int;
  Unix.close fd

(* Simplify expression using STP VC interface *)
let stp_simplify ?(print_stp_exp_flag = false) vc ctx e =
  let _ = Libstp.vc_push vc in
  D.pdebug "Converting Vine expression to STP";
  let stp_exp = Vine_stpvc.vine_to_stp vc ctx e in
  if print_stp_exp_flag then stp_exp_to_file "tmp.stp" vc stp_exp;
  D.pdebug "Converting STP expression back to Vine";
  let _ = Libstp.vc_pop vc in
  Vine_stpvc.stp_to_vine(stp_exp)

(* Print expression stats *)
let print_exp_stats vis e = 
  vis#reset_counters;
  vis#clear_lvals;
  ignore(exp_accept vis e);
  vis#print_stats;
  vis#print_lvals

(* Extract list of assert variables from statement list *)
let get_assert_vars ?(sort_vars=false) sl = 
  let assert_vis =
    object(self)
      inherit nop_vine_visitor

      val mutable var_list = []

      method get_assert_vars = var_list

      method visit_rlvalue rval = 
	match rval with 
	  Temp(var) -> 
	    var_list <- var :: var_list;
	    SkipChildren
	  | Mem _ -> failwith "get_assert_vars does not support Mem's" 

      method visit_stmt stmt = 
	match stmt with 
	  Assert(exp) -> DoChildren 
	  | _ -> SkipChildren
    end
  in
  let _ = List.map (stmt_accept assert_vis) sl in
  let var_l = assert_vis#get_assert_vars in
  if (sort_vars) then List.sort varname_compare var_l
  else var_l


(* Extract list of buffer variables from statement list 
XXX: Only the last variable with an index is kept *)
let get_buffer_vars sl buf_start buf_off buf_len = 
  (* Load all buffer position to hash table *)
  let buf_pos_tbl = Hashtbl.create buf_len in
  let already_seen = Hashtbl.create buf_len in
  let _ =
    for i = 0 to (buf_len-1)
    do
      let curr_index =
        Int32.add (Int32.add buf_start buf_off) (Int32.of_int i) in
      let index32 = Int64.of_int32 curr_index in
      Hashtbl.add buf_pos_tbl index32 1
    done
  in
  let reverse_sl = List.rev sl in
  let process_stmt l stmt = 
    match stmt with 
      Move(Temp(var),exp) -> 
	let index = get_index (Temp(var)) in 
	if ((index <> 0L) && (Hashtbl.mem buf_pos_tbl index) && 
	    (not (Hashtbl.mem already_seen index)))
	  then (Hashtbl.replace already_seen index true; var :: l)
	  else l
      | _ -> l
  in
  List.fold_left process_stmt [] reverse_sl


(** Exectrace filter: nop filter. Does nothing 
*)
class nop_filter : eh_filter = 
  object
    method apply prog insn_opt eh eh_num = 
    prog, insn_opt
  end

(** Exectrace filter: ignore instructions that operate on this origin 
*)
class origin_ignore_filter origin =
  object
    val _origin = origin
    val _cmt = Comment("Instruction removed by origin_ignore_filter")

    method apply (prog : Exectrace.trace_prog)  insn_opt 
      (eh : Temu_trace.instruction) (eh_num : int64) =
      let insn_uses_origin insn = 
	let op_l = (Array.to_list insn#operand) in
	let operand_uses_origin op =
	  let op_origin_l = Array.to_list op#origin in
	  List.exists (fun o -> o = _origin) op_origin_l
	in
	List.exists operand_uses_origin op_l
      in
      if (not (insn_uses_origin eh)) then prog, insn_opt
      else (
	match insn_opt with
	 | None -> prog,insn_opt
	 | Some(insn) ->
	    let insn_opt =
	      Some({
		label = insn.label;
		cmt = insn.cmt;
		asm_sl = [_cmt];
		asm_dl = [];
		setup_ir = [];
		tainted_eflags = false;
	      })
	    in
	    prog, insn_opt
      )

  end


(* Exectrace filter:
  Identifies:
    a) memory reads with tainted memory indices
    b) memory writes with tainted memory indices
    c) jumps on tainted eflags
  and replaces them with comments, so they can be removed in posprocessing. 
*)
class symbolic_lk_filter : eh_filter =
object(self)
  method apply prog insn_opt eh eh_num =
    match insn_opt with
     | None -> prog,insn_opt
     | Some(insn) ->
        let (src_operand,src_memregs) = 
	  try (eh#operand.(1),Array.to_list eh#memregs.(1))
	  with _ -> (
	    let op = new operand_v50 in
	    ((op : operand_v50 :> operand),[])
	  )
	in
        let (dst_operand,dst_memregs) = 
	  try (eh#operand.(0),Array.to_list eh#memregs.(0))
	  with _ -> (
	    let op = new operand_v50 in 
	    ((op : operand_v50 :> operand),[])
	  )
	in
        let is_mem op =
          match op#optype with
            | Temu_trace.TMemLoc -> true
            | _ -> false
        in
        let is_reg op =
          match op#optype with
            | Temu_trace.TRegister -> true
            | _ -> false
        in
        let is_symbolic_read = 
	  match eh#tp with
	    | TPMemReadIndex -> true
	    | TPUnknown ->
		((is_mem src_operand) && (src_operand#taintflag = 0L) &&
		  List.exists (fun memreg -> (memreg#taintflag <> 0L)) 
		    src_memregs)
	    | _ -> false
        in
        let is_symbolic_write =
	  match eh#tp with
	    | TPMemWriteIndex -> true
	    | TPUnknown ->
		((is_mem dst_operand) && (src_operand#taintflag = 0L) &&
		  (* (is_reg src_operand) && *)
		  List.exists (fun memreg -> (memreg#taintflag <> 0L)) 
		    dst_memregs)
	    | _ -> false
        in
	let is_symbolic_jump = 
	  let is_uncond_indirect_jump = 
	    let opcode = int_of_char eh#rawbytes.(0) in
	    let modrm = (((int_of_char eh#rawbytes.(1)) lsr 3) land 7) in 
	    (match (opcode,modrm) with 
	      (* (0xe9,_) | (0xea,_) | (0xeb,_) | (0xff,5) -> true *)
	      | (0xff,4) -> true
	      | _ -> false
	    )
	  in
	  ((is_uncond_indirect_jump) && 
	    (List.exists (fun memreg -> (memreg#taintflag <> 0L)) dst_memregs)) 
	in 
	if (is_symbolic_jump) then (
          let insn_opt = Some({insn with
            asm_sl = Comment("jmp with tainted index") :: insn.asm_sl})
          in
          prog, insn_opt
	)
        else if ((is_symbolic_read) && (is_symbolic_write)) then (
          let insn_opt = Some({insn with
            asm_sl = 
	      Comment("mem read+write with tainted index") :: insn.asm_sl})
          in
          prog, insn_opt
        )
        else if (is_symbolic_read) then (
          let insn_opt = Some({insn with
            asm_sl = Comment("mem read with tainted index") :: insn.asm_sl})
          in
          prog, insn_opt
        )
        else if (is_symbolic_write) then (
          let insn_opt = Some({insn with
            asm_sl = Comment("mem write with tainted index") :: insn.asm_sl})
          in
          prog, insn_opt
        )
        else prog, insn_opt
end


(** A visitor for translating an SSA'ed IR.
      It translates all Mems with concrete indeces to Temps.
      Memory reads with tainted memory indices are rewritten so they all 
	read from the same array. 
      Memory writes with tainted indices fail unless unsafe_flag is set 
	With unsafe_flag set they are incorrectly rewritten to use the 
	single array.
*)
class ssa_translator_vis ?(keep_mem_arr=true) unsafe_flag =
object(self)
  inherit Vine.nop_vine_visitor

  (* Maps <memory_index> -> Variable ID *)
  val already_seen = Hashtbl.create 1300

  val single_mem_var = 
    Vine.newvar "mem_arr" (Array(REG_8,(array_idx_type_to_size REG_32)))

  (* Flag to print memory write with tainted index warning only once *)
  val mutable seen_taint_memwrite = false

  (* Memory read *)
  method visit_rlvalue rlv = 
    match rlv with 
      | Mem(arr_var,index_exp,t) -> (
        (match index_exp with
          Constant (Int(t,index_val)) ->
            (* Check if index already seen *)
            let mem_var =
              try Hashtbl.find already_seen index_val
              with Not_found ->
                (* let stmt_str = stmt_to_string stmt in
		D.pwarn "Memory not initialized: %s\n" stmt_str;
                failwith "Failing" *)
                let index_str = Printf.sprintf "0x%08Lx" index_val in
                let name = "uninitialized_mem_read_" ^ index_str in
                Vine.newvar name REG_8
            in
            ChangeTo(Temp(mem_var))
          | _ ->
            (* Memory read with tainted index. Convert to single mem_arr var *)
            ChangeTo(Mem(single_mem_var,index_exp,t))
        )
	)
    | _ -> SkipChildren

  (* Memory writes *)
  method visit_stmt stmt = 
  match stmt with
    (* Memory write (old SSA method) *) 
    Move(Temp(lvar),Let(Mem(var,index_exp,t),e1,e2)) -> 
	(match index_exp with
	  Constant (Int(t,index_val)) ->
	    (* Check if index already seen *)
	    let mem_var =
		let index_str = Printf.sprintf "0x%08Lx" index_val in
		let name = "mem_at_" ^ index_str in
		let new_mem_var = Vine.newvar name REG_8 in
		let _ = Hashtbl.add already_seen index_val new_mem_var in
		new_mem_var
	    in
	    let sl = 
	      [ Move(Mem(single_mem_var,index_exp,REG_8),e1);
		Move(Temp(mem_var),e1)]
	    in
	    ChangeTo(Block([],sl))

	  | _ -> 
	    (* Memory write with tainted index *)
	    if (unsafe_flag) then (
	      if (not seen_taint_memwrite) then (
		D.pwarn "Found memory write with tainted index\n";
		D.pwarn "Resulting file is not correct. Use with care!\n";
		seen_taint_memwrite <- true;
	      ); 
	      ChangeTo(Move(Mem(single_mem_var,index_exp,t),e1))
	      (* SkipChildren *)
	    )
	    else failwith "Found memory write with tainted index. Stopping..."
	)

    (* Memory write (new SSA method) *)
    | Move(Mem(mem_var,index_exp,t),r_exp) -> 
        (match index_exp with
          Constant (Int(t,index_val)) ->
            (* Check if index already seen *)
            let mem_var =
                let index_str = Printf.sprintf "0x%08Lx" index_val in
                let name = "mem_at_" ^ index_str in
                let new_mem_var = Vine.newvar name REG_8 in
                let _ = Hashtbl.add already_seen index_val new_mem_var in
                new_mem_var
            in
            let sl = 
	      if keep_mem_arr then
		[ Move(Mem(single_mem_var,index_exp,REG_8),r_exp);
		  Move(Temp(mem_var),r_exp)]
	      else
		[ Move(Temp(mem_var),r_exp) ]
            in
              ChangeTo(Block([],sl))
          | _ -> 
            (* Memory write with tainted index *)
            if (unsafe_flag) then (
              if (not seen_taint_memwrite) then (
                D.pwarn "Found memory write with tainted index\n";
                D.pwarn "Resulting file is not correct. Use with care!\n";
                seen_taint_memwrite <- true;
              ); 
              ChangeTo(Move(Mem(single_mem_var,index_exp,t),r_exp))
              (* SkipChildren *)
            )
            else failwith "Found memory write with tainted index. Stopping..."
        )
    | _ -> DoChildren
end

(** A visitor for translating an IR with concrete indices and deendianized *)
class vine_translator_vis =
object(self)
  inherit Vine.nop_vine_visitor

  (* Maps <memory_index> -> Variable ID *)
  val already_seen = Hashtbl.create 1300

  method visit_alvalue lv =
    match lv with 
      Mem(var,index_exp,t) -> 
	let index_val =
	  match index_exp with
	    Constant (Int(t,index_val)) -> index_val
	    | _ ->
	      D.wprintf "Don't know how to handle index in: %s\n" 
		(lval_to_string lv);
	      failwith "Can only transform concrete indices"
	in
	(* Check if index already seen *)
	let mem_var =
	  try Hashtbl.find already_seen index_val
	  with Not_found ->
	    let name = "mem_at_" ^ (Int64.to_string index_val) in
	    let new_mem_var = Vine.newvar name REG_8 in
	    let _ = Hashtbl.add already_seen index_val new_mem_var in
	    new_mem_var
	in
	ChangeTo(Temp(mem_var))
      | _ -> DoChildren

  method visit_rlvalue lv = 
    match lv with 
      Mem(var,index_exp,t) ->
	let index_val =
	  match index_exp with
	    Constant (Int(t,index_val)) -> index_val
	    | _ ->
	      D.wprintf "Don't know how to handle index in: %s\n" 
		(lval_to_string lv);
	      failwith "Can only transform concrete indices"
	in
	(* Check if index already seen *)
	let mem_var =
	  try Hashtbl.find already_seen index_val
	  with Not_found -> 
 	    (* D.wprintf "Memory not initialized: %s\n" (lval_to_string lv);
	    failwith "Failing" *)
	    let index_str = Printf.sprintf "0x%08Lx" index_val in
	    let name = "uninitialized_mem_read_" ^ index_str in
	    Vine.newvar name REG_8
	in
	ChangeTo(Temp(mem_var))
	| _ -> DoChildren

end


(** A visitor to extract expression statistics *)
class stats_vis =
object(self)
  inherit Vine.nop_vine_visitor

  val mutable subexp_counter = 0
  val mutable binop_counter = 0
  val mutable unop_counter = 0
  val mutable constant_counter = 0
  val mutable lval_counter = 0
  val mutable name_counter = 0
  val mutable cast_counter = 0
  val mutable unknown_counter = 0
  val mutable let_counter = 0

  val lvals = Hashtbl.create 13
  val assigned_lvals = Hashtbl.create 13

  method reset_counters = 
    subexp_counter <- 0;
    binop_counter <- 0;
    unop_counter <- 0;
    constant_counter <- 0;
    lval_counter <- 0;
    name_counter <- 0;
    cast_counter <- 0;
    unknown_counter <- 0;
    let_counter <- 0

  method clear_lvals = Hashtbl.clear lvals

  method get_subexp_count = subexp_counter
  method get_binop_count = binop_counter
  method get_unop_count = unop_counter
  method get_constant_count = constant_counter
  method get_lval_count = lval_counter
  method get_name_count = name_counter
  method get_cast_count = cast_counter
  method get_unknown_count = unknown_counter
  method get_let_count = let_counter 

  method get_lvals = 
    let dummy_lv = Lval(Temp(0,"dummy",REG_8)) in 
    let keys = get_hash_keys lvals in
    let keys = List.sort Pervasives.compare keys in
    let process_key l curr_key = 
      let (prev_key,_) = try List.hd l with _ -> (dummy_lv,0) in
      if (prev_key <> curr_key) then (
	let appears_list =
	  try Hashtbl.find_all lvals curr_key
	  with Not_found -> []
	in
	let num_appearances = List.length appears_list in
	(curr_key,num_appearances) :: l
      )
      else l
    in
    List.fold_left process_key [] keys

  method inc_subexp = subexp_counter <- subexp_counter + 1
  method inc_binop = binop_counter <- binop_counter + 1
  method inc_unop = unop_counter <- unop_counter + 1
  method inc_constant = constant_counter <- constant_counter + 1
  method inc_lval = lval_counter <- lval_counter + 1
  method inc_name = name_counter <- name_counter + 1
  method inc_cast = cast_counter <- cast_counter + 1
  method inc_unknown = unknown_counter <- unknown_counter + 1
  method inc_let = let_counter <- let_counter + 1

  method print_stats = 
    Printf.printf "Stats:\n";
    Printf.printf "\tBinOps: %d\n" binop_counter;
    Printf.printf "\tUnOps: %d\n" unop_counter;
    Printf.printf "\tConstants: %d\n" constant_counter;
    Printf.printf "\tLvals: %d\n" lval_counter;
    Printf.printf "\tNames: %d\n" name_counter;
    Printf.printf "\tCasts: %d\n" cast_counter;
    Printf.printf "\tUnknowns: %d\n" unknown_counter;
    Printf.printf "\tLets: %d\n" let_counter;
    Printf.printf "\tTOTAL subexpressions: %d\n" subexp_counter;
    Printf.printf "\n"

  method print_lvals = 
    let lvals_list = self#get_lvals in
    Printf.printf "FreeLval in exp:\n";
    let process_pair (lv,num_appearances) = 
      Printf.printf "\t";
      pp_exp print_string lv;
      Printf.printf " (%d)\n" num_appearances;
    in 
    List.iter process_pair lvals_list;
    Printf.printf "\n"

  method visit_exp e = 
    self#inc_subexp;
    match e with 
      BinOp _ -> self#inc_binop; DoChildren
      | UnOp _ -> self#inc_unop; DoChildren
      | Constant _ -> self#inc_constant; DoChildren
      | Lval _ -> self#inc_lval; DoChildren
      | Name _ -> self#inc_name; DoChildren
      | Cast _ -> self#inc_cast; DoChildren
      | Unknown _ -> self#inc_unknown; DoChildren
      | Let _ -> self#inc_let; DoChildren

  method visit_binding ((l,r) as b) =
    ChangeDoChildrenPost(b, fun x -> Hashtbl.replace assigned_lvals l true; x)

  method visit_rlvalue rlv =
    let assigned = Hashtbl.mem assigned_lvals rlv in
    if (not assigned) then Hashtbl.add lvals (Lval(rlv)) true;
    DoChildren
end

(** A visitor for concretizing indices *)
class concrete_vis (concretize_fun_init) =
object(self)
  inherit Vine.nop_vine_visitor

  val concretize_fun = concretize_fun_init
  val mutable ignore_index = false

  method visit_alvalue lv =
    match lv with
      (* Memory write *) 
      Mem(var,exp,t) ->  
	  let concrete_index = concretize_fun exp in
	  let new_lval = Mem(var,concrete_index,t) in
	  ChangeTo(new_lval)
      | _ -> 
	  SkipChildren

  method visit_rlvalue lv =
    match lv with 
      Mem(var,exp,t) -> 
	  let concrete_index = concretize_fun exp in
	  let new_lval = Mem(var,concrete_index,t) in
	  ChangeTo(new_lval)
      | _ -> 
	  DoChildren

  method visit_stmt stmt =
    match stmt with
      (* If possible symbolic index set flag to verify index *)
      | Comment("mem read with tainted index")
      | Comment("mem write with tainted index") 
      | Comment("mem read+write with tainted index")
      | Comment("jmp with tainted index") ->
	  ignore_index <- true;
	  SkipChildren
      (* If find label, then stop verifying indeces *)
      | Label(s) when ((String.sub s 0 5) = "pc_0x") -> 
	  (* pp_stmt print_string stmt; *)
	  ignore_index <- false;
	  SkipChildren
      (* Constrain mem accesses might concretize index already *)
      | Comment("constrain_mem_accesses") ->
	  ignore_index <- false;
	  SkipChildren
      (* For the rest do children *)
      | _ -> 
	if (ignore_index) then SkipChildren else DoChildren
end

(** 
  Extract a declaration list from a statement list. 
    @param sl an statement list
    @return a declaration list matching the input statement list. 
*)
let get_dl_from_sl sl = 
  let freevis = object(self)
    inherit nop_vine_visitor

    val already_seen = Hashtbl.create 10000
    val mutable ctx = ([]:decl list)

    method get_ctx () = ctx

    method private extend_ctx lv =
      let declaration = 
	match lv with
	    Temp(v) -> v
	  | Mem(v,_,_) -> v
      in
      if (not (Hashtbl.mem already_seen declaration)) then (
	ctx <- declaration :: ctx;
	Hashtbl.add already_seen declaration true   
      )

    method get_dl () = List.rev ctx 

    method visit_alvalue lv = self#extend_ctx lv;
      DoChildren

    method visit_rlvalue lv = self#extend_ctx lv;
      DoChildren

    method visit_binding (l,r) = 
      self#extend_ctx l;
      DoChildren

  end
  in
  let _ = List.map (stmt_accept freevis) sl in
  freevis#get_dl ()

(* Convert a Vine expresion to a Vine program *)
let exp_to_prog ?(varname = "OUT") exp = 
  let vartype =  Vine_typecheck.infer_type None exp in
  let var = Vine.newvar varname vartype in
    let sl = [Move(Temp(var),exp)] in 
    let dl = get_dl_from_sl sl in 
    (dl,sl)


(** 
  Modifies given program in SSA'ed version replacing the memory writes 
  in the form of Let assignments with Temp's that encode the memory index 
  in the name. 
  XXX Make sure that the memory indices are concrete 
    @param prog_ssa program in SSA with memory writes as Let expressions
    @return program with memory accesses using Temp's 
*)
let translate_ssa ?(keep_mem_arr=true) ?(unsafe_flag=false) prog_ssa = 
  (* Create translation visitor *)
  let tvis = new ssa_translator_vis ~keep_mem_arr:keep_mem_arr unsafe_flag in

  (* Translate each statement *)
  let (dl,sl) = prog_ssa in
  let sl' = List.map (stmt_accept tvis) sl in 
  let dl' = get_dl_from_sl sl' in
  let prog = (dl',sl') in

  (* Descope the program *) 
  let prog = Vine_alphavary.descope_program prog in
  prog


(* Parse an ir_file *)
let get_ir_from_file 
  ?(flatten_ir_flag = true) 
  ?(parser_track_lines_flag = false) 
  ?(parser_coerce_flag = false) 
  ?(parser_typecheck_flag = true) 
  ?(parser_strip_nums_flag = true) 
  ir_file =

  (* Set flags for the IR parser *) 
  Vine_parser.flag_track_lines := parser_track_lines_flag;
  Vine_parser.flag_coerce := parser_coerce_flag;
  Vine_parser.flag_typecheck := parser_typecheck_flag;
  Vine_absyn.strip_nums := parser_strip_nums_flag;

  (* Parse the IR *)
  D.dprintf "Parsing IR from: %s\n" ir_file;
  let prog = Vine_parser.parse_file ir_file in
  
  (* Flatten the IR -> Remove scoping, such as blocks *)
  let prog = 
    if (flatten_ir_flag) then (
      D.pdebug "Flattening IR";
      Vine_alphavary.descope_program prog
    )
    else prog
  in prog


(* Get the Vine CFG from an IR *)
let get_cfg_from_ir 
  ?(print_cfg_flag = false)
  ?(do_dce_flag = false) 
  ?(coalesce_cfg_flag = true) 
  prog =

  (* Create the CFG *)
  D.pdebug "Creating CFG";
  let cfg = Vine_cfg.prog_to_cfg prog in

  (* Perform dead code elimination in CFG *)
  let _ = 
    if (do_dce_flag) then (
      D.pdebug "\nPerforming dead-code elimination";
      let _ = Vine_dataflow.do_dce ~globals:[] cfg in
      ()
    )
  in

  (* Coalesce the CFG *)
  let _ = 
    if (coalesce_cfg_flag) then (
      (* D.pdebug "Coalescing CFG"; *)
      D.dprintf "Coalescing CFG (%d nodes)\n" cfg#length;
      Vine_cfg.coalesce_bb cfg
    )
  in

  (* Print the CFG to dot format *)
  let _ = 
    if (print_cfg_flag) then (
      D.pdebug "Printing CFG as dot file";
      let fd = open_out "tmp.dot" in
      Vine_cfg.print_dot_cfg cfg "tmp" Vine_cfg.stmt_printer fd  
    ) 

  in cfg


(**
    Modifies the given program to have all memory indices concrete 
    XXX: the program should have been flattened before
    @param prog_noscope flattened program possibly with concrete initializers and complex expressions as memory indices 
    @return program with memory indices being concrete
*)
let make_concrete_indices ?(ignore_assert_failures_flag=true) prog_noscope = 
  let (dl,sl) = prog_noscope in

  (* Create concrete evaluator *)
  let evaluator = new Vine_ceval.concrete_evaluator prog_noscope in

  (* Create a visitor *)
  let val_to_const v =
    match v with
    | Vine_ceval.Int(t,v) ->
	Constant(Int(t,v))
    | _ -> failwith "Expected an int val"
  in
  let concretize_function exp = 
    val_to_const (evaluator#eval_exp exp) in
  let conc_vis = new concrete_vis concretize_function in 

  (* List reference to store concretized statements *)
  let concrete_index_stmt_list = ref [] in

  (* String reference to store the last seen pc label *)
  let last_pc_label = ref "" in

  (* Iterate through statements *)
  let rec step acc =
    let pc = evaluator#get_pc () in
    let ecode = evaluator#get_ecode () in
    let acc = true in
    let stmt_o =
      try
        Some(Vine_eval.pc_to_stmt ecode pc)
      with
        Not_found -> None
    in
    let halted =
      match stmt_o with
      | None -> true
      | Some(stmt) ->
          (* D.dprintf "Executing: %s" (stmt_to_string stmt); *) 
	  let halted = 
	    try evaluator#step () 
	    with Vine_eval.AssertFailure _ -> (
	      if (ignore_assert_failures_flag) then (
		D.wprintf "Found AssertFailure @ insn %s. Skipping...\n" 
		  !last_pc_label; 
		let curr_pc = evaluator#get_pc () in
		evaluator#set_pc (curr_pc + 1);
		false
	      )
	      else (
		D.wprintf "Found AssertFailure @ insn %s. Stopping...\n" 
		  !last_pc_label; 
		true
	      )
	    )
	  in
	  (* D.dprintf "Executed: %s" (stmt_to_string stmt); *)

	  (* visit statement to concretize memory indices *)
	  let s' = stmt_accept conc_vis stmt in
	  (* D.dprintf "Concretized: %s\n" (stmt_to_string s'); *)
	  let _ = 
	    match stmt with 
	      Label(s) when ((String.sub s 0 5) = "pc_0x") -> 
		  last_pc_label := s;
	      | _ -> ()
	  in
	  concrete_index_stmt_list := s' :: !concrete_index_stmt_list;
          halted
    in
    if halted then
      acc
    else
      step acc
  in
  ignore(step true);
  (* Remove global_return / halt *) 
  let remove_global_ret = function  
      s::rl -> rl
      | [] -> sl
  in 
  let new_sl = remove_global_ret !concrete_index_stmt_list in
  let new_sl = List.rev new_sl in
  (dl, new_sl)

(** Get last Lval in statement list *)
let get_last_lval ?(already_reversed_flag=false) sl = 
  let reverse_sl = 
    if (not already_reversed_flag) 
      then List.rev sl 
      else sl
  in
  let last_lval =
    let last_stmt = List.hd reverse_sl in
    match last_stmt with
      Move(Temp(var),_) -> Lval(Temp(var))
      | _ -> failwith "last stmt is not a Move with a Temp"
  in
  last_lval

(* Convert a program to a let expression *)
let letify_prog prog = 
  let (dl,sl) = prog in

  (* Get last Lval *)
  let reverse_sl = List.rev sl in
  let last_lval = get_last_lval ~already_reversed_flag:true reverse_sl in

  (* Make giant let expresion *)
  make_let_expr ~first_exp:last_lval reverse_sl true 


(** 
  Make let expression equivalent to statement list; 
  and call STP to simplify the let expression 
  XXX: the last expression in the let (the target of the simplification) 
  is the last Lval in the statement list
  @param ir_ssa program in SSA form, with no Mem's 
  @return simplified expression 
*)
let let_simplification 
  ?(print_stp_flag = false) 
  ?(vine_opt_simplify_flag = true)
  ?(print_stats_flag = false)
  vc ctx ir_ssa = 

  let (dl,sl) = ir_ssa in

  (* Get last Lval *)
  let reverse_sl = List.rev sl in
  let last_lval = get_last_lval ~already_reversed_flag:true reverse_sl in

  (* Make giant let expresion *)
  D.pdebug "Creating giant let expression";
  let let_exp = make_let_expr ~first_exp:last_lval reverse_sl true in 
  (* pp_exp print_string let_exp; *)

  (* Print the formula as STP to file *)
  let _ = 
    if (print_stp_flag) then (
      D.pdebug "Writing let expression as STP to file";
      let oc = open_out "tmp.stp" in
      let () = Stp.to_file oc let_exp in
      close_out oc
    )
  in

  (* Simplify let expresion with STP *)
  let simplified_exp = stp_simplify vc ctx let_exp in

  (* Do further simplification using Vine_opt *)
  let simplified_exp = 
    if (vine_opt_simplify_flag) then (
      D.pdebug "\nSimplifying with Vine_opt";
      Vine_opt.simplify simplified_exp
    )
    else simplified_exp
  in
  simplified_exp


(** A visitor for slicing *)
class slice_vis num_vars =
  object(self)
    inherit Vine.nop_vine_visitor

    (* Stores Lval's to slice for, with corresponding IDs *)
    val lv_to_slice_tbl = Hashtbl.create num_vars

    (* Slices indexed by ID *)
    val slice_tbl = Hashtbl.create num_vars

    (* Stores Lval's that we have already started slicing *) 
    val already_started_tbl = Hashtbl.create num_vars

    (* Contains current dependencies (lv -> id_list) *)
    val val_tbl = Hashtbl.create 1000

    (* Determines if an slice needs to keep all memory write *)
    val keep_mem_write_tbl = Hashtbl.create 1000

    (* Auxiliary hash table to avoid keeping duplicated dependencies *)
    val pair_tbl = Hashtbl.create 1000

    val mutable id_list = []

    val mutable slice_mem_flag = false

    method clear_ids = 
      id_list <- []

    method num_ids = 
      List.length id_list

    method init_var_for_slicing indx var = 
      Hashtbl.replace lv_to_slice_tbl (Temp(var)) indx

    method lv_needs_slicing lv = 
      Hashtbl.mem lv_to_slice_tbl lv

    method mem_needs_slicing = 
      slice_mem_flag

    method get_id_started_list = 
      let process_id _ id (already_added_to_group,l) =
	if ((already_added_to_group) && (id = 0)) then (true,l)
	else (
	  let l = id :: l in
	  if (id = 0) then (true,l) else (false,l))
      in 
      let (_,l) = Hashtbl.fold process_id already_started_tbl (false,[]) in
      l

    method get_var_started_list = 
      let process_lv lv id l = 
	match lv with 
	  Temp(var) -> var::l
	  | _ -> l
      in Hashtbl.fold process_lv already_started_tbl []

    method get_id_from_lv lv = 
      Hashtbl.find lv_to_slice_tbl lv

    method already_started_slice lv = 
      Hashtbl.mem already_started_tbl lv

    method add_to_already_started_slice lv = 
      Hashtbl.replace already_started_tbl lv (self#get_id_from_lv lv)

    method add_to_slice id stmt = 
      Hashtbl.add slice_tbl id stmt

    method add_to_all_slices (stmt : Vine.stmt) = 
      let process_id _ id already_added_to_group = 
	if ((already_added_to_group) && (id = 0)) then true
	else (
	  self#add_to_slice id stmt;
	  if (id = 0) then true else false)
      in ignore(Hashtbl.fold process_id lv_to_slice_tbl false); ()

    method add_to_started_slices stmt = 
      let process_id _ id already_added_to_group =
	if ((already_added_to_group) && (id = 0)) then true
	else (
	  self#add_to_slice id stmt;
	  if (id = 0) then true else false)
      in ignore(Hashtbl.fold process_id already_started_tbl false); ()

    method add_to_dependant_slices lval stmt =
      (* D.pdebug "In: add_to_dependant_slices"; *)
      let ol = Hashtbl.find_all val_tbl lval in
      let process_id id = 
	Hashtbl.add slice_tbl id stmt
      in
      List.iter process_id ol 

    method add_to_mem_dependant_slices stmt = 
      let add_stmt id b = Hashtbl.add slice_tbl id stmt in
      Hashtbl.iter add_stmt keep_mem_write_tbl

    method get_slice id = 
      Hashtbl.find_all slice_tbl id

    method print_id_list = 
      Printf.printf "Num_ids: %d\n\tOffsets: " self#num_ids;
      let process_id id =
	Printf.printf "%d " id
      in
      List.iter process_id id_list;
      Printf.printf "\n"

    method remove_val item = 
      (* D.pdebug "In: remove_val"; *)
      let ol = Hashtbl.find_all val_tbl item in
      let process_id id =
	Hashtbl.remove pair_tbl (item,id) 
      in
      List.iter process_id ol;
      Hashtbl.remove val_tbl item

    method is_lval_needed lval = 
      (* D.pdebug "In: is_lval_needed"; *)
      let ol = Hashtbl.find_all val_tbl lval in
      match ol with 
	[] -> false
	| _ -> true

    method lval_needed_ids lval = 
      (* D.pdebug "In: lval_needed"; *)
      Hashtbl.find_all val_tbl lval

    method add_rvals_to_id id exp = 
      (* D.pdebug "In: add_rval_to_id"; *)
      id_list <- [id];
      let _ = exp_accept self exp in
      ()

    method add_rvals_to_started_slices exp =
      let process_id _ id already_added_to_group =
	if ((already_added_to_group) && (id = 0)) then true
	else (
	  self#add_rvals_to_id id exp;
	  if (id = 0) then true else false)
      in ignore(Hashtbl.fold process_id already_started_tbl false);()

    method add_rvals_to_mem_dependant_slices exp = 
      let add_exp id b = self#add_rvals_to_id id exp in
      Hashtbl.iter add_exp keep_mem_write_tbl 

    method add_rvals lval exp = 
      (* D.pdebug "In: add_rvals"; *)
      id_list <- self#lval_needed_ids lval;
      match id_list with 
	[] -> ()
	| _ ->
	  ignore(exp_accept self exp);
	  self#remove_val lval

    method visit_rlvalue rval =
      match rval with 
	Temp _ -> 
	  let process_id id = 
	    if (not (Hashtbl.mem pair_tbl (rval,id))) then (
	      Hashtbl.add val_tbl rval id;
	      Hashtbl.replace pair_tbl (rval,id) true
	    )
	  in
	  List.iter process_id id_list;
	  SkipChildren 
	| Mem _ -> 
	  if (not slice_mem_flag) then slice_mem_flag <- true;
          let process_id id =
	    Hashtbl.replace keep_mem_write_tbl id true
          in
          List.iter process_id id_list;
	  DoChildren (* Adds indices to slices *)
  end

(* Slicing algorithm summary:
      Iterate on statement list from bottom to top
      For each Move statement
	1) Is lval new memory index?
	YES -> Explore stmt adding all rval's for the given offset
	NO -> 
	2) Is lval needed?
	NO -> goto next statement
	YES -> 
	3) Add statement to slices
	4) Explore statement adding all rval's for all lval offsets
	5) goto next statement
*)
(** Function for slicing a program
    @param add_control_deps_flag when true it adds control deps to slices
    @param keep_labels_flag when true it keeps the labels in the slices
    @param var_group optional list of variables belonging to a group. 
      The slice generated for the group is the union of the individual slices
    @param vis visitor that implements the slicing algorithm
    @param prog the program to get the slice from
    @param var_list the list of variables to slice 
    	(creates one slice per variable)
    @ return void the visitor can be queried for the slices
*)
let slice_prog 
  ?(add_control_deps_flag = false) 
  ?(already_reversed_flag = false)
  ?(early_exit_flag = false)
  ?(keep_labels_flag = false) 
  ?(var_group = []) 
  vis prog var_list = 

  (* Load variables in group with ID zero *)
  let load_group_lv curr_group_var = 
    vis#init_var_for_slicing 0 curr_group_var; 
  in
  let _ = List.iter load_group_lv var_group in

  (* Load variables to slice for into hash table. Assigns IDs to vars *)
  let load_lv curr_indx curr_var = 
    vis#init_var_for_slicing curr_indx curr_var;
    curr_indx + 1
  in
  let _ = List.fold_left load_lv 1 var_list in

  (* Reverse the statement list, we iterate bottom up *)
  let (_,sl) = prog in
  let sl =
    if (already_reversed_flag) then sl
    else List.rev sl
  in

  (* Iterate through statements *)
  let process_statement stmt =
    (* D.dprintf "At: %s\n" (stmt_to_string stmt); *)
    match stmt with 
      | Move(Mem (_,index_exp,_), val_exp) ->
	  if ((not early_exit_flag) &&  (vis#mem_needs_slicing)) then (
	    vis#add_rvals_to_mem_dependant_slices index_exp;
	    vis#add_rvals_to_mem_dependant_slices val_exp;
	    vis#add_to_mem_dependant_slices stmt
	  )

      | Move(Temp(var), val_exp) when (is_mem_arr_var var) ->
	  if ((not early_exit_flag) &&  (vis#mem_needs_slicing)) then (
	    vis#add_rvals_to_mem_dependant_slices val_exp;
	    vis#add_to_mem_dependant_slices stmt
	  )

      | Move(lv, exp) ->
	(* Check if first assignment of variable we are slicing for *)
	if ((vis#lv_needs_slicing lv) && (not (vis#already_started_slice lv)))
	then (
	  (* Found one of the variables we are slicing for *)
	  vis#add_to_already_started_slice lv;
	  D.dprintf "FOUND LVAL: %s\n" (lval_to_string lv);

	  let id = vis#get_id_from_lv lv in
	  vis#add_to_slice id stmt;
	  vis#add_rvals_to_id id exp; 
	  ()
	)
	else (
	  (* Not a new position, check if dependencies pending on the lval *)
	  if (vis#is_lval_needed lv) then (
	    (* D.pdebug "Lval needed\n"; *)
	    vis#add_to_dependant_slices lv stmt;
	    vis#add_rvals lv exp
	  )
	)
      | Assert(exp) -> 
	if (add_control_deps_flag) then (
	  vis#add_to_started_slices stmt;
	  vis#add_rvals_to_started_slices exp
	)

      | CJmp(e1,e2,e3) -> 
        if (add_control_deps_flag) then (
          vis#add_to_started_slices stmt;
	  vis#add_rvals_to_started_slices e1;
	  vis#add_rvals_to_started_slices e2;
	  vis#add_rvals_to_started_slices e3
        )

      | Label _ -> 
	if (keep_labels_flag) then (
	  vis#add_to_started_slices stmt
	)

      | Jmp _ | Special _ | ExpStmt _ | Comment _
      | Function _ | Call _ | Return _ | Block _ -> ()
      | _ -> ()
  in
  List.iter process_statement sl
  

(** 
  Convert an IR program to SSA, optionally replacing Mem's 
  @param ir_file program to convert to SSA, optionally replacing Mem's
  @return ssa program
*)
let ir_to_ssa 
  ?(keep_mem_arr=true)
  ?(translate_notation_flag=false) 
  ?(ignore_unsafe=false) 
  prog = 

  let prog_from_ssa = Ssa.trace_ssa prog in

  (* Translate notation *)
  let prog_from_ssa = 
    if (translate_notation_flag) then (
      D.pdebug "Translating SSA program";
      translate_ssa ~keep_mem_arr:keep_mem_arr ~unsafe_flag:ignore_unsafe prog_from_ssa 
    )
    else prog_from_ssa
  in
  prog_from_ssa


type processing_flags = {
  (* Processing *)
  include_all_insn_flag : bool;
  filter_unknowns_flag : bool;
  constrain_mems_flag : bool;
  filter_origin : int32;
  (* Post-processing *)
  flatten_ir_flag : bool;
  concretize_mem_indices_flag : bool;
  concretize_all_mem_indices_flag : bool;
  remove_concrete_inits_flag : bool;
  rename_asserts_flag : bool;
  no_asserts_flag : bool;
}

(* Create filters for disasm_trace *)
let disasm_filters pp =
  let tracker = new track_opval_filter in
  let filters =
    [if pp.include_all_insn_flag
      then new Exectrace.disasm_all
      else new Exectrace.disasm_tainted;
     new handle_outsw;
     if pp.filter_origin <> 0l 
       then new origin_ignore_filter pp.filter_origin
       else new nop_filter;
     if pp.filter_unknowns_flag
       then new unknowns_filter
       else new nop_filter;
     if pp.constrain_mems_flag
      then new constrain_mem_accesses []
      else new nop_filter;
     new Exectrace.make_straightline_filter;
     (tracker :> eh_filter);
     new Exectrace.initialize_operands_small tracker false;
    (* NOTE: initialize_input_symbols needs to appear AFTER 
      initialize_operands_small *)
     new initialize_input_symbols tracker;
     new Exectrace.break_dep_chains_filter tracker;
     new Exectrace.uniqify_labels;
     if (pp.concretize_mem_indices_flag && 
	  (not pp.concretize_all_mem_indices_flag))
       then new symbolic_lk_filter
       else new nop_filter;
     ]
  in
  filters


(* Post-process IR afte getting it from Exectrace *)
let post_process_ir pp prog = 

  (* Flatten the IR -> Remove scoping, such as blocks *)
  let prog =
    if (pp.flatten_ir_flag) then (
      D.pdebug "Flattening IR";
      Vine_alphavary.descope_program prog
    )
    else prog
  in

  (* Concretize indices *)
  let prog =
    if (pp.concretize_mem_indices_flag || pp.concretize_all_mem_indices_flag)
      then (
        D.pdebug "Concretizing memory indices";
        make_concrete_indices prog
        (* Exectrace.prop_constants prog true *) (* Slower *)
      )
      else prog
  in

  (* Convert all mem vars to REG_8 type (rather than REG_16, REG_32, REG_64
      This makes sure that mem's whose type annotations do not match 
      their declared type are rewritten *)
  let prog =
    if (true) then (
      D.pdebug "Coercing IR";
      let _ = Vine_memory2array.coerce_prog prog in
      prog
    )
    else prog
  in

  (* Remove concrete initializers *)
  let prog =
    if (pp.remove_concrete_inits_flag)
      then (
        D.pdebug "Removing concrete operand initializers";
        remove_input_concrete_initializers prog
      )
      else prog
  in

  (* Rename asserts *)
  let prog =
    if (pp.rename_asserts_flag) then (
      D.pdebug "Renaming asserts";
      create_assert_variable prog
    )
    else prog
  in

  (* Converts asserts to post-condition *)
  let prog =
    if (pp.no_asserts_flag) then (
      D.pdebug "Converting asserts to post-condition";
      let (prog,_) = asserts_to_post prog in
      prog
    )
    else
      prog
  in
  prog


(** 
  Generates an IR from the trace. The generated IR has optionally \
  concrete indices
  @param trace_file execution trace
  @return IR file 
*)
let get_ir_from_trace 
  ?(use_thunks_flag=false) (* Set to true by default if using asserts *)
  ?(remove_concrete_inits_flag=true)
  ?(flatten_ir_flag=true)
  ?(add_eflag_helpers_flag=false)
  ?(coerce_ir_flag=false)
  ?(include_all_insn_flag=false)
  ?(concretize_mem_indices_flag=true)
  ?(concretize_all_mem_indices_flag=false)
  ?(rename_asserts_flag=true)
  ?(filter_unknowns_flag=false)
  ?(filter_origin=0l)
  ?(no_asserts_flag=false)
  ?(constrain_mems_flag=true)
  ?(deend_flag=true)
  ?(stop_l=[])
  ?(stop_ctr=0L)
  trace_file = 

  let prog_flags = {
    include_all_insn_flag = include_all_insn_flag;
    filter_unknowns_flag = filter_unknowns_flag;
    filter_origin = filter_origin;
    constrain_mems_flag = constrain_mems_flag;
    flatten_ir_flag = flatten_ir_flag;
    concretize_mem_indices_flag = concretize_mem_indices_flag;
    concretize_all_mem_indices_flag = concretize_all_mem_indices_flag;
    remove_concrete_inits_flag = remove_concrete_inits_flag;
    rename_asserts_flag = rename_asserts_flag;
    no_asserts_flag = no_asserts_flag;
  }
  in

  (* Convert execution trace to IR *)
  (* Beware that the order of the filters matters (at least some of them) *)
  D.pdebug "Getting trace";
  let filters = disasm_filters prog_flags in

  let trace_prog, trace_insns =
    Exectrace.disasm_trace ~use_thunks:use_thunks_flag 
      ~stop_l:stop_l ~stop_ctr:stop_ctr trace_file filters 
  in
  let prog =
    Exectrace.trace_to_prog ~deend:deend_flag trace_prog trace_insns
  in
(*
  (* Write IR *) 
  let output_file = "tmp.intermediate" in
  write_prog output_file prog;
*)

  (* Post-process the IR *)
  let prog = post_process_ir prog_flags prog in
  prog

(* Get slices for a list of variables from a program *)
let get_slices_from_ssa_prog ?(early_exit=true) ?(keep_labels=false) 
    var_l ssa_prog =

  (* Create visitor for slicing *)
  let vis = new slice_vis (List.length var_l) in
  (* Slice *)
  let _ =
    slice_prog  ~early_exit_flag:early_exit
      ~keep_labels_flag:keep_labels vis ssa_prog var_l
  in
  let started_var_list = vis#get_var_started_list in
  (* Extract slices from slice visitor *)
  let process_var acc var =
    let id = vis#get_id_from_lv (Temp(var)) in
    let sl = vis#get_slice id in
    let dl' = get_dl_from_sl sl in
    let sliced_prog = (dl',sl) in
    (var,sliced_prog) :: acc
  in
  List.fold_left process_var [] started_var_list

(* Get formulas for a list of variables from a program 
   Returns a list of pairs (var,formula)
*)
let get_formulas_from_ssa_prog ?(early_exit=true) ?(keep_labels=false) 
    ?(write_slices=false) ?(write_formulas=false) vc var_l ssa_prog =

  (* Create visitor for slicing *)
  let vis = new slice_vis (List.length var_l) in
  (* Slice *)
  let _ =
    slice_prog  ~early_exit_flag:early_exit
      ~keep_labels_flag:keep_labels vis ssa_prog var_l
  in
  (* Get list of slices variables *)
  let started_var_list =
    List.sort varname_compare vis#get_var_started_list
  in
  (* Extract slices from slice visitor *)
  let process_var var acc =
    (* Get slice for variable *)
    let id = vis#get_id_from_lv (Temp(var)) in
    let sl = vis#get_slice id in
    let dl' = get_dl_from_sl sl in
    let sliced_prog = (dl',sl) in
    (* Get filename *)
    let (_,varname,_) = var in
    let formula_path =
      Printf.sprintf "%s.formula" varname
    in
    (* Write slice if requested *)
    if (write_slices) then (
      let slice_path = change_ext formula_path "slice" in
      write_prog slice_path sliced_prog
    );
    (* Simplify slice *)
    let ctx = Vine_stpvc.new_ctx vc dl' in
    let formula = let_simplification vc ctx sliced_prog in
    (var,formula) :: acc
  in
  List.fold_right process_var started_var_list []


