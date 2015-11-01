(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   Tool for the trouble-shooting project
   
   @author Zhenkai Liang
*)

open Vine
open Exectrace
module Trace=Temu_trace
module D = Debug.Make(struct let name = Sys.argv.(0) and default=`Debug end)


(*============== The following is not changed, copied from exectrace ==== *)
  let opcode rawbytes =
    let rec _opcode rawbytes idx =
      match (int_of_char rawbytes.(idx)) with
      | 0xf0 | 0xf2 | 0xf3 (* lock or rep prefix *)
      | 0x2e | 0x36 | 0x3e | 0x26 | 0x64 | 0x65 (* sgmt override
                                                   prefix *)
      | 0x66 | 0x67 (* opsize prefix *) 
          ->
          _opcode rawbytes (idx+1) (* skip prefix *)
      | _ ->
          int_of_char rawbytes.(idx),
          (if ((int_of_char rawbytes.(idx)) = 0x0f)  then
             int_of_char rawbytes.(idx+1)
           else
             ((int_of_char rawbytes.(idx+1)) lsr 3) land 7)
    in
    _opcode rawbytes 0


  let uses_esp rawbytes =
    match opcode rawbytes with
    | 0xe8, _ (* call variations *)
    | 0xff, 2
    | 0x9a, _
    | 0xff, 3
    | 0xc3, _ (* ret variations *)
    | 0xcb, _
    | 0xc2, _
    | 0xca, _
    | 0xff, 6 (* push *)
    | 0x50, _
    | 0x6a, _
    | 0x68, _
    | 0x0e, _
    | 0x16, _
    | 0x1e, _
    | 0x06, _
    | 0x0f, 0xa0
    | 0x0f, 0xa8 
    | 0x60, _ (* pusha *)
    | 0x9c, _ (* pushf *)
    | 0x8f, 0 (* pop *)
    | 0x58, _
    | 0x1f, _
    | 0x07, _
    | 0x17, _
    | 0x0f, 0xa1
    | 0x0f, 0xa9
    | 0x61, _ (* popa *)
    | 0x9d, _ (* popf *)
    | 0x0f, 0x34 (* sysenter *)
    | 0x0f, 0x35 (* sysexit *)
    | 0xc8, _ (* enter *)
    | 0xc9, _ (* leave *)
    | 0xcc, _ (* int *)
    | 0xcd, _
    | 0xce, _
    | 0xcf, _ (* iret *)
        -> true
    | _ -> false

let rvars_of_stmt s =
  let vis = object(self)
    inherit nop_vine_visitor

    val mutable rvars = VarSet.empty
    method get_rvars = rvars

    method visit_rlvalue lv =
      let v = 
        match lv with
        | Temp(v) -> v
        | Mem(v,_,_) -> v
      in
      rvars <- VarSet.add v rvars;
      DoChildren
  end
  in
  let _ = stmt_accept vis s in
  vis#get_rvars

let get_flags_from_eflags gamma =
  let cf_p = 0 in
  let pf_p = 2 in
  let af_p = 4 in
  let zf_p = 6 in
  let sf_p = 7 in
  let of_p = 11 in

  let (_,_,eflags_t) as eflags = Asmir.gamma_lookup gamma "EFLAGS" in

  let flag_assignment s pos =
    Move(Temp(Asmir.gamma_lookup gamma s),
         Cast(CAST_LOW,
              REG_1,
              BinOp(RSHIFT,
                    Lval(Temp(eflags)),
                    const_of_int eflags_t pos)
             )
        )
  in
  [flag_assignment "R_CF" cf_p;
   flag_assignment "R_PF" pf_p;
   flag_assignment "R_AF" af_p;
   flag_assignment "R_ZF" zf_p;
   flag_assignment "R_SF" sf_p;
   flag_assignment "R_OF" of_p;
  ]

let opvals_fold_left cb acc eh =
  let acc =
    Array.fold_left
      (fun acc op_ary ->
         Array.fold_left
           (cb true)
           acc
           op_ary
      )
      acc
      eh#memregs
  in
  let acc =
    List.fold_left
      (cb false)
      acc
      (List.rev (Array.to_list eh#operand))
  in
  if uses_esp eh#rawbytes then
    (cb true) acc eh#esp
  else
    acc

(* =================== end of blocks copied from exectrace ============= *)


(** initializes instruction operands concretely or symbolically.
    Needs a track_opval_filter object, which must execute BEFORE
    this one in the filter list given to disasm_trace *)
class my_initialize_operands_small
  (tracker:track_opval_filter) expected_asserts =
object (self)
  val tracker = tracker
  val expected_asserts = expected_asserts

  (* handle initialization of an operand byte tainted by
     an input that has NOT appeared earlier in the trace. *)
  method private init_sym_byte_first 
    prog eh_num opval opval_offset input_origin input_offset conc_val =
    
    let input_var = 
      tracker#input_vars_var
        input_origin input_offset
    in
    [Opval.byte_mov 
       prog.gamma 
       opval 
       opval_offset
       (Lval(Temp(input_var)))]

  (* handle initialization of an operand byte tainted by
     an input that HAS appeared earlier in the trace,
     and for which the propagation IS plausible. *)
  method private init_sym_byte_propped 
    prog eh_num opval opval_offset input_origin input_offset conc_val =
    (* initd this symbol and location. all ok *)

    (* XXX FIXME : break into separate filter? *)
    let movs =
      if expected_asserts then
        [Assert(BinOp(EQ, 
                      (Opval.byte_exp 
                         prog.gamma 
                         opval 
                         opval_offset),
                      conc_val))]
      else
        []
    in

    let movs = 
      (Comment(Printf.sprintf
                 "%s:%d Already initd input (%ld, %ld)"
                 (Opval.to_string opval)
                 opval_offset
                 input_origin
		 input_offset))
      :: movs
    in
    movs

  (* handle initialization of an operand byte tainted by
     an input that HAS appeared earlier in the trace,
     and for which the propagation is NOT plausible. *)      
  method private init_sym_byte_missed_prop 
    prog eh_num opval opval_offset input_origin input_offset conc_val =
    (* initd this symbol, but not this
       location. this probably means
       the trace is missing instructions that
       propagated tainted data.
    *)
    (D.wprintf
       "eh %Ld: Missed prop of inp(%ld, %ld) to %s:%d\n"
       eh_num
       input_origin
       input_offset
       (Opval.to_string opval)
       opval_offset);

    (* create a fresh symbol *)
    let name =
      Printf.sprintf "INPUT_missed_%lu_%04lu"
        input_origin
        input_offset
    in
    let symvar = newvar name Vine.REG_8 in

    (* assign the symbol the conc. val from trace,
       and assign the operand the symbol.*)
    let sl =
      [Comment("WARNING missed prop, using concrete init");
       Move(Temp(symvar), conc_val);
       (Opval.byte_mov 
          prog.gamma
          opval
          opval_offset
          (Lval(Temp(symvar))))]
    in

    [Vine.Block([symvar], sl)]

  (* initialize a single byte of a tainted operand *)
  method private init_sym_byte 
    prog eh_num opval opval_offset input_origin input_offset conc_val =

    if not (tracker#prev_input_vars_mem input_origin input_offset)
    then
      (* case: first time seeing this input origin and offset *)
      self#init_sym_byte_first
        prog eh_num opval opval_offset input_origin input_offset conc_val
    else
      if (tracker#prev_initd_locs_mem opval opval_offset) then 
        (* case: not first time. propagation check passes *)
        self#init_sym_byte_propped
          prog eh_num opval opval_offset input_origin input_offset conc_val
      else
        (* case: not first time. propagation check fails *)
        self#init_sym_byte_missed_prop
          prog eh_num opval opval_offset input_origin input_offset conc_val

  (* initialize a single byte of an untainted operand *)
  method private init_conc_byte prog eh_num opval opval_offset conc_val =
    (* untainted, init concretely *)
    [Opval.byte_mov 
         prog.gamma
         opval
         opval_offset
         conc_val]

  (* initialize a whole concrete operand *)
  method private init_conc_opval prog eh_num opval =
    let rhs = Opval.const opval in
    [Opval.mov prog.gamma opval rhs]

  (* initialize an operand *)
  method private initialize_operand prog eh_num is_mem_reg movs opval =      
    let isreg =
      match opval#optype with
      | Trace.TRegister -> true
      | _ -> false
    in
    let ismem =
      match opval#optype with
      | Trace.TMemLoc -> true
      | _ -> false
    in
    if not (ismem || isreg) then
      movs
    else
      (* case: whole opval is concrete *)
      let new_movs = 
        if opval#taintflag = 0L then
          self#init_conc_opval prog eh_num opval 
        else
          (* at least partially tainted. iterate through opval bytes *)
          Opval.byte_foldleft
            (fun movs opval offset ->
               let conc_val =
                 const_of_int64
                   REG_8
                   (Opval.byte_conc_val
                      opval
                      offset)
               in

               let new_movs =

		 (* modified by zhenkai: in this module, ignore taint info 
		    during initialization *)

(*                  if Opval.byte_tainted opval offset then *)
(*                    (\* symbolic byte *\) *)
(*                    self#init_sym_byte  *)
(*                      prog *)
(*                      eh_num *)
(*                      opval  *)
(*                      offset  *)
(*                      (opval#origin).(offset) *)
(*                      (opval#offset).(offset) *)
(*                      conc_val *)
(*                  else *)
                   (* concrete byte *)
                   self#init_conc_byte prog eh_num opval offset conc_val
               in
               List.rev_append new_movs movs
            )
            opval
            []
      in
      List.rev_append new_movs movs
            
  method apply prog insn_opt (eh:Trace.instruction) (eh_num:int64) = 
    match insn_opt with
    | None -> prog, insn_opt
    | Some(insn) ->

        (* create initializers *)
        let special_movs =
          [
            Move(Temp(Asmir.gamma_lookup prog.gamma "R_GDT"),
                 Constant(Int(REG_32, Trace.int64_of_uint32 eh#gdt)));
            Move(Temp(Asmir.gamma_lookup prog.gamma "R_LDT"),
                 Constant(Int(REG_32, Trace.int64_of_uint32 eh#ldt)));
            Move(Temp(Asmir.gamma_lookup prog.gamma "R_DFLAG"),
                 Constant(Int(REG_32, Trace.int64_of_uint32 eh#df)));
          ]
        in

        (* if eflags is untainted 
           and conditions are used, 
           initialize conditions *)
        let special_movs = 
          if ( not insn.tainted_eflags )
            &&
            ( 
              let flag_vars = 
                List.fold_left
                  (fun s v -> VarSet.add v s)
                  VarSet.empty
                  [Asmir.gamma_lookup prog.gamma "R_CF";
                   Asmir.gamma_lookup prog.gamma "R_PF";
                   Asmir.gamma_lookup prog.gamma "R_AF";
                   Asmir.gamma_lookup prog.gamma "R_ZF";
                   Asmir.gamma_lookup prog.gamma "R_SF";
                   Asmir.gamma_lookup prog.gamma "R_OF"]
              in
              let rvars = rvars_of_stmt (Block([], insn.asm_sl)) in
              not (VarSet.is_empty (VarSet.inter rvars flag_vars))
            ) then
              let eflag_inits = 
                (Move(Temp(Asmir.gamma_lookup prog.gamma "EFLAGS"),
                      Constant(Int(REG_32, Trace.int64_of_uint32
                                     eh#eflags))))
                :: (get_flags_from_eflags prog.gamma) in
              eflag_inits @ special_movs
          else
            special_movs
        in

        let movs =
          opvals_fold_left
            (self#initialize_operand prog eh_num)
            special_movs
            eh
        in

        let init_block = Block([], Comment("Initializers") :: movs) in

        (prog,
         Some({insn with setup_ir = init_block::(insn.setup_ir)}))

end
 

(** Take the output of disasm_trace and create an IR program.
    @param deend optional, deendianize all memory accesses.
    you MUST use this to deendianize the trace, rather than
    doing a separate deendianization pass. This uses info
    in trace_prog to make sure that memory variable names
    are consistent.
    @param trace_prog global info about the trace, generated by
    disasm_trace
    @param trace_insns list of processed instructions, generated
    by disasm_trace
*)
let my_trace_to_prog ?(deend = true) trace_prog trace_insns =
  (* paste together all the sl's *)
  let sl = 
    List.fold_left
      (fun sl trace_insn -> 
           trace_insn.setup_ir
         @
         [Label(trace_insn.label);
          Comment(trace_insn.cmt);
          Comment("Filter IRs:");]
         @
           [Comment("ASM IR:");
            Block(trace_insn.asm_dl, trace_insn.asm_sl)]
         @
           sl)
      []
      (List.rev trace_insns)
  in
  let dl = trace_prog.dl in

  (* add flag helpers *)
  let sl =
    if trace_prog.use_thunks then
      let helpers = Asmir.x86_eflags_helpers () in
      helpers @ sl
    else
      sl
  in

  (* add setup ir *)
  let sl = trace_prog.prog_setup_ir @ sl in
    
  (* deendianize all *)
  let dl, sl =
    if deend then
      List.fold_left
        (fun (dl, sl) (mem, arr) ->
           Vine_memory2array.coerce_program_variable
             mem
             arr
             (dl, sl)
        )
        (dl, sl)
        trace_prog.mems_arrays
    else
      dl, sl
  in
  (dl, sl)


(* end of modifiled exectrace components *)







let diverge = ref []

let usage () =
  Printf.fprintf stderr "Usage: %s trace inst_num log\n" Sys.argv.(0);
  exit 1 

(** Parse result.log and initialize diverge list *)
let init_log_file log column =
  let ic = open_in log in
  let re_d = 
    Str.regexp "Traces diverge at EIP:.*offset: \([0-9]*\).*offset: \([0-9]*\)"
  in
  let re_m = 
    Str.regexp "Traces merge at EIP:.*offset: \([0-9]*\).*offset: \([0-9]*\)" 
  in
  let firstdiverge = ref Int64.minus_one in
  let cv = ref true in
  let () = 
    try 
      while !cv do
	let line = input_line ic in
	  if Str.string_match re_d line 0 then
	    let offset1 = Int64.of_string (Str.matched_group column line) in
	    let line2 = input_line ic in
	    let _ = Str.string_match re_m line2 0 in
	    let offset2 = Int64.of_string (Str.matched_group column line2) in
	      diverge := (offset1, offset2)::!diverge;
	      if !firstdiverge = Int64.minus_one then firstdiverge := offset1
      done
    with
	_ -> ()
  in
    !firstdiverge

(** Remove a variable from the slice visitor's val_tbl *)
let remove_val vis s gamma =
  let var = Asmir.gamma_lookup gamma s in
  let lval = Temp(var) in
    vis#remove_val lval
      
(* Evaluator of current instruction *)
let cureval = ref []
(* A refernce to gamma, to be used in slice_vis without changing its ifc *)
let curgamma = ref (Hashtbl.create 1)

(* Given a memory index expression, calculate the value of the expression, 
   and convert the memory into a Temp variable of REG_8 *)
let get_mem_var exp =
  let evaluator = List.hd !cureval in
    (* run evaluator *)
  let _ = 
    try 
      evaluator#run () 
    with 
	Vine_eval.NoSuchLabel(_) -> Vine_ceval.Str ""
  in
  let result = evaluator#eval_exp exp in
  let memaddr = 
    match result with
	Vine_ceval.Int(_, value) -> value
      | _ -> 0L
  in
  let newname = Printf.sprintf "mem0x%Lx" memaddr in
    try 
      Hashtbl.find !curgamma newname 
    with 
	Not_found -> 
	  let var = newvar newname REG_8 in
	    Hashtbl.add !curgamma newname var;
	    var
	      
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
	| Mem (_, exp, _) -> 
	    (* 	  if (not slice_mem_flag) then slice_mem_flag <- true; *)
	    let process_id id =
	      Hashtbl.replace keep_mem_write_tbl id true
	    in
	    let newvar = get_mem_var exp in
	    let newrval = Temp(newvar) in
	    let process_id_2 id = 
	      if (not (Hashtbl.mem pair_tbl (newrval,id))) then (
		Hashtbl.add val_tbl newrval id;
		Hashtbl.replace pair_tbl (newrval,id) true
	      )
	    in
	      List.iter process_id_2 id_list;
	      List.iter process_id id_list;
	      DoChildren (* Adds indices to slices *)
		
    method val_tbl_is_empty =
      Hashtbl.length val_tbl = 0

    method print_lv_list =
      let print_info lv index =
	pp_lval print_string lv; Printf.printf "%d\n" index
      in
	Printf.printf "val_tbl (live variables):\n";
	Hashtbl.iter print_info val_tbl;
	Printf.printf "\n"
  end

let init_vis_varlist vis var_list =
  (* Load variables to slice for into hash table. Assigns IDs to vars *)
  let load_lv curr_indx curr_var = 
    vis#init_var_for_slicing curr_indx curr_var;
    curr_indx + 1
  in
    List.fold_left load_lv 1 var_list 

let process_statement stmt vis early_exit_flag add_control_deps_flag =
  (* D.dprintf "At: %s\n" (stmt_to_string stmt); *)
  let process_lv lv exp =
    if ((vis#lv_needs_slicing lv) && (not (vis#already_started_slice lv)))
    then (
      (* Found one of the variables we are slicing for *)
      vis#add_to_already_started_slice lv;
      D.dprintf "FOUND LVAL: %s\n" (lval_to_string lv);

      let id = vis#get_id_from_lv lv in
	vis#add_to_slice id stmt;
	vis#add_rvals_to_id id exp; 
	true
    )
    else (
      (* Not a new position, check if dependencies pending on the lval *)
      if (vis#is_lval_needed lv) then (
	(* D.pdebug "Lval needed\n"; *)
	vis#add_to_dependant_slices lv stmt;
	vis#add_rvals lv exp;
	true
      ) else false
    )
  in
    match stmt with 
      | Move(Mem (_,index_exp,_), val_exp) ->
	  let memvar = get_mem_var index_exp in
	  let memlv = Temp(memvar) in
	    ignore (process_lv memlv val_exp);
	    if ((not early_exit_flag) &&  (vis#mem_needs_slicing)) then (
	      vis#add_rvals_to_mem_dependant_slices index_exp;
	      vis#add_rvals_to_mem_dependant_slices val_exp;
	      vis#add_to_mem_dependant_slices stmt;
	      true
	    ) else false

      | Move(Temp(var), val_exp) when (Trace_slice.is_mem_arr_var var) ->
	  if ((not early_exit_flag) &&  (vis#mem_needs_slicing)) then (
	    vis#add_rvals_to_mem_dependant_slices val_exp;
	    vis#add_to_mem_dependant_slices stmt;
	    true
	  ) else false

      | Move(lv, exp) ->
	  (* Check if first assignment of variable we are slicing for *)
	  process_lv lv exp 
      | Assert(exp) -> 
	  if (add_control_deps_flag) then (
	    vis#add_to_started_slices stmt;
	    vis#add_rvals_to_started_slices exp;
	    true
	  ) else false

      | CJmp(e1,e2,e3) -> 
          if (add_control_deps_flag) then (
            vis#add_to_started_slices stmt;
	    vis#add_rvals_to_started_slices e1;
	    vis#add_rvals_to_started_slices e2;
	    vis#add_rvals_to_started_slices e3;
	    true 
          ) else false

      | Label _ 
      | Jmp _ | Special _ | ExpStmt _ | Comment _
      | Function _ | Call _ | Return _ | Block _ -> false
      | _ -> false

(** find the previous diverge basic block *)
let get_diverge_block insn_num =
  let (left, _) = 
    List.find (fun (a,b) -> insn_num >=a && insn_num <=b) !diverge
  in
    left

(** convert an tracefile into initialized ir *)      
let ir_from_trace  start_ctr stop_ctr gamma trace_file = 
  let tracker = new track_opval_filter in
  let filters = 
    [ new Exectrace.disasm_all;
      new my_initialize_operands_small tracker false
    ]
  in
  let trace_prog, trace_insns =
    Exectrace.disasm_trace ~start_ctr:start_ctr ~stop_ctr:stop_ctr 
      ~gammaparam:gamma ~use_thunks:false trace_file filters 
  in
  let prog =
    my_trace_to_prog ~deend:true trace_prog trace_insns
  in
  let prog =
      Vine_alphavary.descope_program prog
  in
    prog

let process_insn tracefile gamma vis i =
  let prog = ir_from_trace i i (Some gamma) tracefile in
    (*   let _ = pp_program print_string prog in *)
    (*   let _ = flush stdout in *)
  let (_, asm_sl) = prog in
    (* check whether stmt is the comment after setup ir *)
  let is_asm_ir_comment i stmt =
    match stmt with
	Comment(s) -> s = "ASM IR:"
      | _ -> false
  in
    (* check whether stmt is the comment of disassembled instruction *)
  let is_dis_comment stmt =
    match stmt with
	Comment(s) ->
	  let re = Str.regexp "^[0-9a-fA-F]+:.*" in
	    Str.string_match re s 0
      | _ -> false
  in
  let dis_comment = List.find is_dis_comment asm_sl in
  let dis_insn = 
    match dis_comment with
	Comment(s) -> s
      | _ -> ""
  in
  let evaluator = new Vine_ceval.concrete_evaluator prog in
  let exp = Lval(Temp(45, "T_32t0", REG_32)) in
  let _ = cureval := [evaluator] in
  let (j,_) = ExtList.List.findi is_asm_ir_comment asm_sl in
  let (_, asm_sl) = ExtList.List.split_nth j asm_sl in

  let hasdep = ref false in
  let _ = curgamma := gamma in
  let process_stmt stmt = 
    if process_statement stmt vis false false then
      hasdep := true
  in
  let print_stderr x = Printf.fprintf stderr "%s" x in
(*     Printf.printf "%s\n" dis_insn; *)
(*     List.iter (fun s -> pp_stmt print_string s) (List.rev asm_sl); *)
    List.iter process_stmt (List.rev asm_sl);
    remove_val vis "R_ESP" gamma;
    remove_val vis "R_EBP" gamma;
    if !hasdep then (
      Printf.printf "INSN#: %Ld\n" i;
      Printf.printf "%s\n" dis_insn;
      Printf.printf "\n";
      vis#print_lv_list;
      [ i ]
    ) else
      []
      
let rec get_branch_insn_from_block tifc insn_num =
  let is_branching_insn opcode =
    match opcode.(0) with
      | '\x70' | '\x71' | '\x72' | '\x73' | '\x74' | '\x75' | '\x76' | '\x77'
      | '\x78' | '\x79' | '\x7A' | '\x7B' | '\x7C' | '\x7D' | '\x7E' | '\x7F'
      | '\xE3' -> true
      | '\x0F' -> (
	  match opcode.(1) with
	    | '\x80' | '\x81' | '\x82' | '\x83' | '\x84' | '\x85' | '\x86' 
	    | '\x87' | '\x88' | '\x89' | '\x8A' | '\x8B' | '\x8C' | '\x8D' 
	    | '\x8E' | '\x8F' -> true
	    | _ -> false
	)
      | _ -> false
  in
  let _ = tifc#seek_instruction insn_num in
  let insn = tifc#read_instruction in
    if is_branching_insn insn#rawbytes then
      insn_num
    else
      get_branch_insn_from_block tifc (Int64.succ insn_num)

let get_condition_var gamma tifc insn_num =
  let _ = tifc#seek_instruction insn_num in
    (* need to make a copy of gamma, otherwise the name we get will be
       different, but it doesn't work now, FIXME *)
  let gammacopy = Hashtbl.copy gamma in
  let insn = tifc#read_instruction in
  let arch = Asmir.arch_i386 in (* FIXME *)
  let raw_ir =        
    Asmir.asm_bytes_to_vine gammacopy arch insn#address insn#rawbytes 
  in
  let asm_sl =
    match raw_ir with
      | [Vine.Block(asm_dl, 
                   (Label label)
                   :: (Comment cmt) 
                   :: asm_sl)] ->
          asm_sl
      | _ -> raise (Invalid_argument "trace_insn_of_eh") 
  in
  let is_cjmp stmt =
    match stmt with
	CJmp(_) -> true
      | _ -> false
  in
  let cjmpstmt = List.find is_cjmp (List.rev asm_sl) in
    match cjmpstmt with 
	CJmp(Lval(Temp(var)), _, _) -> var
      | _ -> failwith "Branching condition is not single variable"

let exitflag = ref false 

let handle_sigint i =
  exitflag := true

let get_dependent_insns tracefile gamma last first varlist =
  let result = ref [] in
  let vis = new slice_vis 1 in
  let _ = init_vis_varlist vis varlist in
  let i = ref last in
    while !i >= first && not !exitflag do
      if !i < first (* || vis#val_tbl_is_empty *)
      then 
	exitflag := true
      else 
	result := process_insn tracefile gamma vis !i @ !result;
      i := Int64.pred !i
    done;
    !result

let get_control_instruction di divergeregions =
  let is_diverging i =
    List.exists (fun (a,b) -> i >= a && i <= b) divergeregions 
  in
  let processing acc i =
    try
      let cp = get_diverge_block i in
	if not (List.mem cp acc) then
	  cp::acc
	else
	  acc 
    with
	Not_found -> acc
  in
    List.rev (List.fold_left processing [] di)

;;

let argc = Array.length Sys.argv in
  if argc < 4 then
    usage ()
  else 
    let _ = Sys.set_signal Sys.sigint (Sys.Signal_handle handle_sigint) in
    let tracefile = Sys.argv.(1) in
    let inst_num = Int64.of_string Sys.argv.(2) in
    let logfile = Sys.argv.(3) in
    let tifc = Trace.open_trace tracefile in
    let binst_num = get_branch_insn_from_block tifc inst_num in 
    let _ = Printf.printf "Found branching instruction at %Ld\n" binst_num in
    let gamma = Asmir.gamma_create Asmir.x86_mem Asmir.x86_regs in
(*   let gamma2 = Asmir.gamma_create Asmir.x86_mem Asmir.x86_regs in
     let condvar = get_condition_var gamma2 tifc binst_num in *)
    let condvar = (44, "T_1t0", REG_1) in
    let _ = pp_var print_string condvar in
    let varlist = [ condvar ] in
    let column = 
      if tracefile = "good.trace" then 1
      else 2
    in
    let firstdiverge = init_log_file logfile column in
    let print_pair (a,b) = Printf.printf "%Ld, %Ld\n" a b in
    let _ = List.iter print_pair !diverge in
    let dilist = get_dependent_insns tracefile gamma binst_num firstdiverge 
      varlist 
    in
    let cplist = get_control_instruction dilist !diverge 
    in
      List.iter (fun i -> Printf.printf "Diverge point: %Ld\n" i) cplist
     
 
