(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   This program analyzes an attack trace and output how attack propagates
   
   @author Zhenkai Liang
*)

module Trace = Temu_trace

type cmdlineargs_t = {
    mutable trace_file : string; 
    mutable tainttrace : string; 
    mutable start : int;
    mutable first : int; 
    mutable last : int;
    mutable count : bool;  
    mutable slience : bool; 
    mutable output : string; 
    mutable precise : bool; 
    mutable taintoffset : int32;
    mutable forward : bool; 
    mutable targetid: int32 list;
  };;
    
let parsecmdline = 
  let cmdlineargs = {
      trace_file = "";
      tainttrace = "";
      start = -1;
      forward = false;
      first = 0;
      last = 0;
      count = false; 
      slience = false;
      output = "";
      precise = false; 
      taintoffset = -1l;
      targetid = [];
    }
  in
  let arg_spec = [
      ("-start", 
      Arg.String (fun s -> cmdlineargs.start <- int_of_string s),
      "Line number of the instruction to start"); 

      ("-first", 
      Arg.String (fun s -> cmdlineargs.first <- int_of_string s),
      "Line number of first instruction"); 

      ("-forward", 
      Arg.Unit (fun s -> cmdlineargs.forward <- true),
      "Perform forward analysis of taint relation, output on stdout"); 

      ("-last", 
      Arg.String (fun s -> cmdlineargs.last <- int_of_string s),
      "Line number of last instruction"); 

      ("-count", 
      Arg.Unit (fun s -> cmdlineargs.count <- true),
      "Display line number"); 
      
      ("-o",
      Arg.String (fun s -> cmdlineargs.output <- s),
      "Output file name");

      ("-insttrace", 
      Arg.String (fun s -> cmdlineargs.trace_file <- s),
      "Name of instruction trace file"); 

      ("-tainttrace",
      Arg.String (fun s -> cmdlineargs.tainttrace <- s),
      "Name of taint trace file");

      ("-taintoffset", 
      Arg.String (fun s -> cmdlineargs.taintoffset <- Int32.of_string s),
      "Only process the instructions operated on taint offset"); 

      ("-targetid",
      Arg.Int (fun s -> cmdlineargs.targetid <- (Int32.of_int s)::cmdlineargs.targetid), 
      "");
    ] 
  in 
  let () =
    Arg.parse arg_spec (fun s -> ()) 
      "Usage: trace_reader [options] trace"
  in
    cmdlineargs

let string_of_optype optype =
  match optype with
      Trace.TRegister -> "R"
    | Trace.TMemLoc -> "M"
    | Trace.TImmediate -> "I"
    | Trace.TJump -> "J"
    | Trace.TFloatRegister -> "F"
    | _ -> ""


let format_operand inst index =
  let opr = inst#operand_v30.(index) in
  let format_base_operand opr_b = 
    Printf.sprintf "\t%s@0x%08Lx[0x%08lx]" (string_of_optype (opr_b#optype))
      (opr_b#opaddr) (opr_b#opvalue)
  in
  let format_taint_info opr_t = 
    let taint_source i = 
      if (Int64.logand opr_t#taintflag (Int64.of_int (1 lsl i))) <> 0L then
	Printf.sprintf "(%lx, %lu, %lx, %d ) " opr_t#origin.(i) 
	  opr_t#offset.(i) opr_t#srcid.(i) (int_of_char opr_t#newid.(i))
      else
	"()"
    in
      match opr_t#taintflag with
	  0L -> "\tT0"
	| _ -> (Printf.sprintf "\tT1 {%Lu " opr_t#taintflag)
	    ^(taint_source 0) ^ (taint_source 1) ^
	      (taint_source 2) ^ (taint_source 3) ^ "}"
  in
  match (opr#optype) with
      Trace.TRegister
    | Trace.TMemLoc
    | Trace.TImmediate
    | Trace.TJump
    | Trace.TFloatRegister 
    | Trace.TMemAddress -> 
	(format_base_operand opr) ^ (format_taint_info opr)
    | Trace.TNone -> ""


let print_proc_info procs =
  let single_mod_info () mi = 
    Printf.printf "\t%s\t0x%Lx\t%Ld\n" mi#name mi#base mi#size
  in
  let single_proc_info () pi =
    Printf.printf "%d\t%s\n" pi#pid pi#name;
    List.fold_left single_mod_info () pi#modules
  in
  let () = Printf.printf "=== Begin process info ===\n" in
  let () = List.fold_left single_proc_info () procs in 
  let () = Printf.printf "=== End process info ===\n" in
    flush stdout

let print_inst args inst count = 
  let () = if args.count then
      (Printf.printf "(%08d)" count; flush stdout)
    else ()
  in
  let argstr = (format_operand inst 2) ^ (format_operand inst 1) ^
    (format_operand inst 0) 
  in
  (*let _ = Libasmir.print_i386_rawbytes inst#address inst#rawbytes in*)
  let _ = Printf.printf "%s" argstr in
  let _ = Printf.printf " ESP: 0x%08lx" inst#esp#opvalue in
  let _ = Printf.printf "\n" in
(*   let ri i = *)
(*     int_of_char (inst#rawbytes).(i) *)
(*   in *)
(*   let _ = Printf.printf "%02X %02X %02X %02X\n" (ri 0) (ri 1) (ri 2) (ri 3) in *)
    flush stdout 


let output_inst inst someoc =
    match someoc with
	Some(oc) -> inst#serialize oc
      | None -> ()

let check_cond args count inst =
  let checktaint inst offset = 
    let oprs = inst#operand in
    let check_opr opr =
      match opr#optype with
	  Trace.TNone -> false
	| _ -> 
	    (Int64.logand opr#taintflag 1L <> 0L)&&(opr#offset.(0) = offset) ||
	    (Int64.logand opr#taintflag 2L <> 0L)&&(opr#offset.(1) = offset) ||
	    (Int64.logand opr#taintflag 4L <> 0L)&&(opr#offset.(2) = offset) ||
	    (Int64.logand opr#taintflag 8L <> 0L)&&(opr#offset.(3) = offset) 
    in
      List.exists check_opr (Array.to_list oprs)
  in
    if (args.last = 0 || count <= args.last) &&
      (args.first = 0 || count >= args.first) &&
      (args.taintoffset = -1l || checktaint inst args.taintoffset)
    then
      true
    else 
      false

let instSize = 1132L

let read_instruction trace n =
  let () = LargeFile.seek_in trace#channel 
    (Int64.add trace#insn_offset 
	(Int64.mul instSize (Int64.of_int (n-1))) )
  in
  let inst = new Trace.instruction_v30 in
    inst#unserialize (IO.input_channel trace#channel); inst

(* ====================== propagation graph ========================== *)

type vInfo = {
    (* predecessors of this vertex *)
    mutable pred : int32 list;
    (* successors of this vertex *)
    mutable succ : int32 list;
    mutable veip : int64; 
    mutable instno : int; 
    mutable destaddr : int64; 
    mutable rawbytes : char array; 
    mutable offset : int32;
  }

type depGraph = {
    vtable : (int32, vInfo) Hashtbl.t; 
  }

let addedge g vstart vend ip dest raw ino oft= 
  let istart = try Hashtbl.find g.vtable vstart 
    with Not_found -> 
      let tmp = 
	{pred=[];succ=[];veip=0L;instno=0;destaddr=0L;rawbytes=[||];offset=0l} 
      in
	Hashtbl.add g.vtable vstart tmp; tmp
  in
  let iend = try Hashtbl.find g.vtable vend
    with Not_found -> 
      let 
	  tmp = {pred=[];succ=[];veip=ip;instno=ino;destaddr=dest;rawbytes=raw;
	  offset=oft} 
      in
	Hashtbl.add g.vtable vend tmp; tmp
  in
    if not (List.mem vend istart.succ) 
    then (
	istart.succ <- vend::istart.succ;
	iend.pred <- vstart::istart.pred
      )

let addedge_noinfo g vstart vend =
  let istart = try Hashtbl.find g.vtable vstart 
    with Not_found -> 
      let tmp = 
	{pred=[];succ=[];veip=0L;instno=0;destaddr=0L;rawbytes=[||];offset=0l} 
      in
	Hashtbl.add g.vtable vstart tmp; tmp
  in
  let iend = try Hashtbl.find g.vtable vend
    with Not_found -> 
      let tmp = 
	{pred=[];succ=[];veip=0L;instno=0;destaddr=0L;rawbytes=[||];offset=0l} 
      in
	Hashtbl.add g.vtable vend tmp; tmp
  in
  let () = 
    if not (List.mem vend istart.succ) 
    then (
	istart.succ <- vend::istart.succ;
	iend.pred <- vstart::istart.pred
      )
  in
    (istart, iend)
    

let node_info vinfo ip ino dest raw  =
  if vinfo.destaddr <> Int64.neg 1L then 
    vinfo.destaddr <- dest; 
  vinfo.veip <- ip;
  vinfo.instno <- ino;
  vinfo.rawbytes <- raw; 
  ()
      
let iter_edges g f =
  let visit_succ vstart vinfo =
    List.iter (fun vend -> if Hashtbl.mem g.vtable vend then f vstart vend) 
      vinfo.succ
  in
    Hashtbl.iter visit_succ g.vtable

let pseudoStart = Int32.neg 100000l 
let pseudoEnd = Int32.neg 100001l 
let pseudoHelper = Int32.neg 100002l

let graph = {vtable = Hashtbl.create 10000;}

module G =
struct
  type t = depGraph

  module V =  struct
    type t = int32
    let hash = Hashtbl.hash
    let equal = (=)
    let compare = compare
  end

  module E = struct
    type t = V.t * V.t
    let src (x, y) = x
    let dst (x, y) = y
  end

  let iter_vertex f g = Hashtbl.iter (fun k v -> f k) g.vtable
  let iter_succ f g v = List.iter (fun k -> f k) (Hashtbl.find g.vtable v).succ
  let iter_edges_e f g =
    let func vstart vend = f (vstart, vend) in
      iter_edges g func 
  let graph_attributes g = []
  let default_vertex_attributes g = []
  let vertex_name v = 
    if (Int32.compare v Int32.zero > 0)
    then 
      Printf.sprintf "\"%lx\"" v
    else
      Printf.sprintf "\"I_%lx\"" (Int32.neg v)
  let vertex_attributes v = 
    let vinfo = Hashtbl.find graph.vtable v in
    let label v = 
      if v = pseudoStart then
	("START", `Box)
      else if v = pseudoEnd then
	("END", `Box)
      else if (Int32.compare v Int32.zero > 0) 
      then
	let s =
	  if vinfo.destaddr = (Int64.neg 1L) then `Diamond
	  else `Box
	in
(* 	Printf.sprintf "%lx: Target 0x%08Lx EIP: 0x%08Lx" v vinfo.destaddr *)
(* 	  vinfo.eip *)
	(Printf.sprintf "label-%lx" v, s)
      else 
	(Printf.sprintf "INIT_%ld" (Int32.neg v), `Ellipse)
    in
    let (l, s) = label v in
      [`Label(l);`Shape(s)]
  let default_edge_attributes g= []
  let edge_attributes e = []
  let get_subgraph v = None
end

module Components = Graph.Components.Make(G)

module Dot = Graph.Graphviz.Dot(G)

(* =================== propagation graph END ========================== *)

let nodelist = ref []

let build_relation inst n = 
  let opr = inst#operand_v30 in
  let is_new id =
    not (Hashtbl.mem graph.vtable id)
  in
  let process_byte i = 
    let byte_tainted taintflag i =
      let mask = Int64.shift_left 1L i in
	if Int64.logand taintflag mask <> 0L 
	then true
	else false
    in
    let _ = 
      (* The first appearance of a tainted var is dependent on input *)
      if (byte_tainted opr.(1)#taintflag i) && (is_new opr.(1)#srcid.(i)) 
      then 
	let targetaddr = match opr.(1)#optype with
	    Trace.TMemLoc -> Int64.add opr.(1)#opaddr (Int64.of_int i)
	  | _ -> opr.(1)#opaddr
	in
          (* opr.(1)#srcid.(i) depends on input opr.(1)#offset.(i) *)
          addedge graph (Int32.neg opr.(1)#offset.(i)) opr.(1)#srcid.(i) 
	    inst#address targetaddr inst#rawbytes n opr.(1)#offset.(i);
	  addedge graph pseudoStart (Int32.neg opr.(1)#offset.(i))
	    0L 0L [||] 0 0l
    in 
      (* destination var dependent on src var *)
      if (byte_tainted opr.(0)#taintflag i) 
        && (is_new opr.(0)#srcid.(i))
        && (byte_tainted opr.(1)#taintflag i)
      then 
        let targetaddr = match opr.(0)#optype with
            Trace.TMemLoc -> Int64.add opr.(0)#opaddr (Int64.of_int i)
          | _ -> opr.(0)#opaddr
        in
          (* opr.(0)#srcid.(i) depends on opr.(1)#srcid.(i) *)
          addedge graph opr.(1)#srcid.(i) opr.(0)#srcid.(i) inst#address
	    targetaddr inst#rawbytes n opr.(0)#offset.(i);
	  nodelist := opr.(0)#srcid.(i)::!nodelist
  in
    process_byte 0;
    process_byte 1;
    process_byte 2;
    process_byte 3



let buffer_start = ref 0L 
let buffer_id = ref 0l 

(* get the cfg of a function body *)
let get_func_cfg prog = 
  let (dl, sl) = prog in 
  let firstfunstmt sl = 
    let is_fun stmt =
      match stmt with 
	  Vine.Function(_) -> true
	| _ -> false 
    in
      List.find is_fun sl
  in
    Vine_cfg.func_to_cfg (firstfunstmt sl) 


(** Get ids logically related to the specified operation *)
let getlogical g ids = 
  (* find eip of instruction *)
  let geteip g v = 
    let vinfo = Hashtbl.find g.vtable v in
      vinfo.veip
  in
  let eip = 
      geteip g (List.hd ids) 
  in
  let label = Printf.sprintf "pc_0x%Lx" eip in
    (* get the function containing eip, convert it into IR prog*)
  let () = Printf.fprintf stderr "Finding function containing %s\n" label in
  let prog = Vine_parser.parse_file "loop.ir" in
  let printer = Printf.fprintf stderr "%s" in
  let cfg = Vine_cfg.prog_to_cfg prog in
(*       let cfg = get_func_cfg prog in *)
  let loop = 
    let rcfg = Vine_loop.get_reducible cfg in 
    let bb = cfg#find_label label in 
    let loops = Vine_loop.get_loops_from_bb rcfg bb  in
    let () = Printf.fprintf stderr "# of loops: %d\n" (List.length loops) in
    let () = List.iter (fun l -> Vine_loop.pp_loop printer l) loops in
      List.hd loops 
  in
  let get_label lset bb = 
    List.fold_left (fun lset stmt -> match stmt with  Vine.Label(s)-> s::lset | _ -> lset) lset (cfg#get_info bb)
  in
  let labelset = List.fold_left get_label [] (Vine_loop.get_loop_body loop) in
  let () = List.iter (fun s -> Printf.fprintf stderr "%s\n" s) labelset in
    (* labelset contains the loop body. Go through the trace again, and 
       and find out the loop containing the taint ID *)
  let nodearray = ExtArray.Array.of_list (List.rev !nodelist) in
    (* for each node in ids, if it is not in newids then look for previous
       ids in nodearry until the eip is out of label set, or the id in newids*)
  let newids = ref [] in
  let rec find_related_backward index = 
    let id = ExtArray.Array.get nodearray index in
    let lbl = Printf.sprintf "pc_0x%Lx" (geteip g id) in
      if List.mem lbl labelset && not (List.mem id !newids)
      then (
	newids := id::!newids;
	let vinfo = Hashtbl.find g.vtable id in
	  if vinfo.destaddr > 200L   (* not a register *)
	  then 
	    (  buffer_id := id; 
	       buffer_start := vinfo.destaddr
	    );
	  if index > 0 
	  then 
	    find_related_backward (index - 1)
      )
  in
  let rec find_related_forward index = 
    let id = ExtArray.Array.get nodearray index in
    let lbl = Printf.sprintf "pc_0x%Lx" (geteip g id) in
      if List.mem lbl labelset && not (List.mem id !newids)
      then (
	  newids := id::!newids;
	  if index > 0 
	  then 
	    find_related_forward (index + 1)
	)
  in
  let id_visitor id = 
    let index = ExtArray.Array.findi (fun v -> v = id) nodearray 
    in
      find_related_backward index;
      find_related_forward (index+1)
  in 
    List.iter id_visitor ids;
(*    List.iter (fun id -> Printf.fprintf stderr "%ld\n" id) !newids;
    Printf.fprintf stderr "========\n";
    List.iter (fun id -> Printf.fprintf stderr "%ld\n" id) ids; *)
(*     List.iter (fun id -> addedge g id pseudoEnd 0L 0L [||]) !newids; *)
    !newids


let get_buffer_offsets g ids =
  let l =
    try
      getlogical g ids
    with
	Not_found -> ids
  in
  let ol = 
    let get_offset id =
      let vinfo = Hashtbl.find g.vtable id in
	vinfo.offset
    in
    List.map get_offset l
  in
  let ul = ExtList.List.unique ol in
    List.sort compare ul

let offsets2ranges ol = 
  let accumulate_range acc offset =
    match acc with
	[] -> [(offset, 1l)]
      | (off, len)::tl -> 
	  if offset = Int32.add off len
	  then (
	    (* expand range *)
	  (off, Int32.succ len)::tl
	  )
	  else
	    (* new range *)
	    (offset, 1l)::acc
  in
  List.fold_left accumulate_range [] ol
  

(* let rec addLogicalEdges g ids =  *)
(*   if ids = [] then *)
(*     [] *)
(*   else  *)
(*     let l =  *)
(*       try  *)
(* 	getlogical g ids  *)
(*       with *)
(* 	  Not_found -> ids  *)
(*     in *)
(*     let ul = ExtList.List.unique l in *)
(*     let l = List.sort compare ul in *)
(*     let print_offset id = *)
(*       let vinfo = Hashtbl.find g.vtable id in *)
(* 	Printf.fprintf stderr "%ld " vinfo.offset  *)
(*     in *)
(*     let () = List.iter print_offset l in *)
(*     let () = Printf.fprintf stderr "\n" in *)
(*     let () =  *)
(*       List.iter (fun id -> addedge graph id pseudoEnd 0L 0L [||] 0 0l) l *)
(*     in *)
      (* Get the source of this operand, if the immediate source is 
      a register, continue to reach a memory address*)
(*     let getsource lst =  *)
(*       let addsource vset v = *)
(* 	let vinfo = Hashtbl.find g.vtable v in *)
(* 	  vinfo.pred @ vset *)
(*       in *)
(* 	List.fold_left addsource [] lst *)

(*     in *)
(*     let nl = getsource l in *)
(*       addLogicalEdges g nl *)
      


let process_inst_trace args =
  let trace= Trace.open_trace args.trace_file in 
    (* let () = print_proc_info trace#processes in *)
  let someoc = if (args.output <> "") then
    let out = open_out args.output in
      Some(IO.output_channel out)
    else
      None
  in
  let rec back_handle_inst trace2 n =
    if n <> 0 then 
      let inst_o =
	try
	  Some(read_instruction trace2 n)
	with
            IO.No_more_input -> None
      in
	match inst_o with
	    None -> ()
	  | Some(inst) ->
              if (check_cond args n inst)
              then (
		print_inst args inst n;
		output_inst inst someoc;
	      );
              back_handle_inst trace2 (n-1)
  in
  let rec forward_handle_inst trace2 n= 
    let inst_o = 
      try 
	Some(read_instruction trace2 n)
      with
	  IO.No_more_input -> None
    in 
      match inst_o with
	  None -> ()
	| Some(inst) -> 
	    let _ = build_relation inst n in
	      forward_handle_inst trace2 (n+1)
  in
  let find_function stackaddr id trace = 
    let vinfo = Hashtbl.find graph.vtable id in
    let instno = vinfo.instno in
    let rec find_function_from_trace stackaddr n trace =
      if n <> 0 then 
	let inst_o =
	  try
	    Some(read_instruction trace n)
	  with
              IO.No_more_input -> None
	in
	  match inst_o with
	      None -> (0L, 0L, 0)
	    | Some(inst) ->
		let eip = inst#address in
		let esp = (Trace.int64_of_uint32 inst#esp#opvalue) in
		  if (eip > 0x80000000L || esp < stackaddr)
		  then
		    find_function_from_trace stackaddr (n-1) trace
		  else
		    (eip, esp, n)
      else
	(0L, 0L, 0)
    in
    let (_, esp, n) = find_function_from_trace stackaddr instno trace in
    let (eip, _, n) = find_function_from_trace (Int64.add esp 8L)  n trace  in
      (eip, n)
  in
  let find_ra_address trace func_addr instno =
    let n = ref instno in
    let retval = ref 0l in
    let cond = ref true in
    let () =
      while !cond do 
	n := !n -1;
	if !n = 1 then cond := false;
	let inst = read_instruction trace !n in
	  if inst#address = func_addr
	  then (
	    retval := inst#esp#opvalue;
	    cond := false
	  )
      done
    in
      Trace.int64_of_uint32 !retval
  in
  let _ = if args.forward then (
    (* Build propagation graph *)
    forward_handle_inst trace 1;

    (* buffer_id contains the propagation id, by which we can find the
       instruction number. buffer start is an stack address *)
    let l = get_buffer_offsets graph args.targetid in
    let print_offset o = Printf.fprintf stdout "%ld " o in
    let () = List.iter print_offset l in
    let rs = offsets2ranges l in
    let print_range (off, len) =
      Printf.fprintf stderr "\tOffset: %ld - %ld\n" off 
        (Int32.pred (Int32.add off len))
    in
    let () = Printf.fprintf stderr "Vuln buffer composition:\n" in
    let () = List.iter print_range rs in    
    let () = Printf.fprintf stderr "Vulnerable buffer address 0x%08Lx\n" 
      !buffer_start in
    let (vulfuncaddr, instno) = 
      find_function !buffer_start !buffer_id trace in
      
    let () = Printf.fprintf stderr 
      "Vulnerable function contains address 0x%08Lx\n" vulfuncaddr 
    in

    let db = Sqlite3.db_open "vuln.db" in
    let get_func_start_addr vulfuncaddr = 
      (* find vulnerable function *)
      let condstr = Printf.sprintf 
	"start_address <= %Ld and end_address > %Ld" 
	vulfuncaddr vulfuncaddr 
      in
      let funcs = Vine_idadb.get_idafuncs_where db condstr in
      let (_, _, name, _, _, func_addr, _) = List.hd funcs in
      let () = Printf.fprintf stderr "Vulnerable function: %s@0x%Lx\n" 
	name func_addr in
	func_addr 
    in
    let func_addr = get_func_start_addr vulfuncaddr in
      (* find return address of the activation record *)
    let ra_addr = find_ra_address trace func_addr instno in
    let () = Printf.fprintf stderr "Vuln Func return address location: 0x%Lx\n"
      ra_addr 
    in
      (* find overflowed local buffer variable *)
    let get_retaddr_offset func_addr =
      let condstr = Printf.sprintf
	"function_address = %Ld and name like \"%%. r\"" func_addr in
      let vars = Vine_idadb.get_idavars_where db condstr in
      let (_, _, _, _, var_addr, _) = List.hd vars in
	var_addr
    in
    let ra_static_offset = get_retaddr_offset func_addr in 
    let offset = Int64.sub ra_static_offset (Int64.sub ra_addr !buffer_start) in
    let condstr = Printf.sprintf 
      "function_address=%Ld and start_offset<=%Ld order by start_offset DESC"
      func_addr offset
    in
    let vars = Vine_idadb.get_idavars_where db condstr in
    let (_, _, _, name, var_addr, _) = List.hd vars in
    let () = Printf.fprintf stderr "Vulnerable variable: %s@%Ld\n" 
      name var_addr 
    in
      
    let () = Printf.fprintf stderr "Overflow starts: %s@%Ld\n" 
      name offset 
    in
      (* find the bound of overflowed buffer *)
    let condstr = Printf.sprintf
      "function_address = %Ld and start_offset > %Ld order by start_offset" 
      func_addr offset
    in
    let vars = Vine_idadb.get_idavars_where db condstr in
    let (_, _, _, name, var_addr, _) = List.hd vars in
    let () = Printf.fprintf stderr "Buffer bound (next variable): %s@%Ld\n" 
      name var_addr 
    in
      ()
	(*     (\* addedge graph pseudoHelper pseudoEnd 0L 0L [||]; *\) *)
	(*     let () = addedge graph pseudoEnd pseudoStart 0L 0L [||] 0 0l in *)
	(*     let scclist = Components.scc_list graph in *)
	(*     let contain_start l = List.mem pseudoStart l in *)
	(*     let scc = List.find contain_start scclist in *)
	(*     let nodeset = Hashtbl.copy graph.vtable in *)
	(*     let rm v i =  *)
	(*       if not (List.mem v scc)  *)
	(*       then Hashtbl.remove graph.vtable v *)
	(*     in *)
	(*       (\* get a list of ranges of input offsets *\) *)
	(*     let getinputrange = *)
	(*       let rangelist = ref [] in *)
	(*       let istart = Hashtbl.find graph.vtable pseudoStart in *)
	(*       let ingraph v = List.mem v scc in *)
	(*       let ilist = List.filter ingraph istart.succ in *)
	(*       let plist = List.map (fun i -> Int32.neg i) ilist in *)
	(*       let slist = List.sort Int32.compare plist in *)
	(*       let sarray = Array.of_list slist in *)
	(*       let left = ref 0l in *)
	(*       let right = ref 0l in *)
	(*       let i = ref 0 in *)
	(*       let len = Array.length sarray in *)
	(* 	while !i < len - 1 do *)
	(* 	  left := sarray.(!i); *)
	(* 	  while (!i < len - 1) && (sarray.(!i+1) = Int32.succ sarray.(!i)) *)
	(* 	  do *)
	(* 	    i := !i + 1; *)
	(* 	  done; *)
	(* 	  right := sarray.(!i); *)
	(* 	  rangelist := (!left, !right)::!rangelist; *)
	(* 	  i := !i + 1; *)
	(* 	done; *)
	(* 	!rangelist *)
	(*     in *)
	(*       List.iter (fun p -> Printf.fprintf stderr  *)
	(* 	"Input bytes used in attack: %ld - %ld\n" (fst p) (snd p)) *)
	(* 	getinputrange; *)
	(*       Hashtbl.iter rm nodeset; *)
	(*       Hashtbl.remove graph.vtable pseudoEnd; *)
	(*       Hashtbl.remove graph.vtable pseudoHelper; *)
	(*       (\* 	showinput; *\) *)
	(*       Dot.output_graph stdout graph; *)
  )
in
let _ = if args.start <> -1 then
  let start = 
    if args.start <> 0 
    then args.start
    else 
      let st = Unix.LargeFile.stat args.trace_file in
      let instblk = Int64.sub st.Unix.LargeFile.st_size trace#insn_offset in
 	Int64.to_int (Int64.div instblk instSize)
  in
    back_handle_inst trace start
in
  Trace.close_trace trace
  


    

type propagation_t = {
  is_move: int32; 
  src_id: int32 array;
  dst_id: int32 array; 
}

type taint_record_t = {
  tr_dst_id: int32;
}

type insn_info_t = {
  eip: int32; 
  esp: int32;
  caller: int32; 
  callee: int32; 
  address_id: int32;
  mem_addr: int32;
  mem_val: int32; 
  raw_insn: char array; 
}

let process_taint_trace args print =  
  let record_size = 116L in
  let rec read_list acc f n =
    match n with
      | 0 -> acc
      | _ -> read_list ((f ()) :: acc) f (n-1)
  in
  let read_array f n =
    Array.of_list (List.rev (read_list [] f n))
  in
  let read_record ch = 
    let empty_prop = 
	{is_move = 0l; src_id = [||]; dst_id = [||]}
    in
    let read_prop channel =
      let is_move = IO.read_real_i32 channel in
      let srcarray = read_array (fun () -> IO.read_real_i32 channel) 12 in
      let dstarray = read_array (fun () -> IO.read_real_i32 channel) 4 in
	{is_move = is_move; src_id = srcarray; dst_id = dstarray}
    in
    let read_define channel =
      let read_taint_record channel =
	let dst_id = IO.read_real_i32 channel in
	  {tr_dst_id = dst_id}
      in
      let trarray = read_array (fun () -> read_taint_record channel) 4 in
      let _ = read_array (fun () -> IO.read_byte channel) 52 in
	trarray
    in
    let channel = IO.input_channel ch in
    let is_new = IO.read_real_i32 channel in
    let (prop, define) =
      if is_new = 0l 
      then
	(read_prop channel, [||])
      else
	(empty_prop, read_define channel)
    in
    let eip = IO.read_real_i32 channel in
    let esp = IO.read_real_i32 channel in
    let caller = IO.read_real_i32 channel in 
    let callee = IO.read_real_i32 channel in
    let address_id = IO.read_real_i32 channel in
    let mem_addr = IO.read_real_i32 channel in 
    let mem_val = IO.read_real_i32 channel in
    let rawinst = read_array
      (fun () -> char_of_int (IO.read_byte channel)) 16 in
    let insninfo = {eip=eip; esp=esp; caller=caller; callee=callee;
		    address_id=address_id; mem_addr=mem_addr;
		    mem_val=mem_val; raw_insn=rawinst;}
    in
      (is_new, prop, define, insninfo)
  in
  let seek_n ch n = 
    let offset = Int64.mul record_size (Int64.of_int (n-1)) in
      LargeFile.seek_in ch offset 
  in
  let read_record_n ch n =
    let () = seek_n ch n in
      read_record ch
  in
  let ic = open_in args.tainttrace in
  let print_trace ic =
    try
      for i = 1 to max_int do
(* 	let (is_new, prop, define, rawbytes) = read_record ic in *)
	let (is_new, prop, define, insninfo) = read_record_n ic i in
	let newflag = 
	  if is_new = 0l then "OLD"
	  else "NEW" 
	in
	let print_taint_record tr =
	  Printf.printf " [id=0x%08lx]"
	    tr.tr_dst_id
	in
	let print_non_zero id =
	  if id <> 0l then
	    Printf.printf "%lx+" id
	in
	  Printf.printf "(%s) eip=" newflag;
	  flush stdout;
	  (*Libasmir.print_i386_rawbytes (Trace.int64_of_uint32 insninfo.eip) *)
	    insninfo.raw_insn;
(* 	  Printf.printf "eip: 0x%lx, mem_addr: %ld, callee: %ld\n"  *)
(* 	    insninfo.eip insninfo.mem_addr insninfo.callee; *)
	  Printf.printf " [caller=0x%08lx callee=0x%08lx]" insninfo.caller
	    insninfo.callee;
	  if is_new <> 0l
	  then
	    Array.iter print_taint_record define
	  else (
	    Printf.printf " (%ld) SRC_ID{ " prop.is_move;
	    Array.iter print_non_zero prop.src_id;
	    Printf.printf "} -> DST_ID{";
	    Array.iter print_non_zero prop.dst_id;
	    Printf.printf "} [0x%08lx]=0x%08lx" insninfo.mem_addr insninfo.mem_val;
	  );
	  Printf.printf "\n";
	  flush stdout;
	    
      done
    with
	IO.No_more_input ->  close_in ic
  in
  let build_graph target =
    let find_inst_no target =
      let n = ref 0 in
      let control = ref true in
      let () =
	try
	  while !control do
	    n := !n + 1;
	    let (is_new, prop, define, insninfo) = read_record ic in
	    let contain_target dstarray tgt =
	      List.exists (fun dst -> dst = tgt)
		(Array.to_list dstarray)
	    in
	      if is_new = 0l && (contain_target prop.dst_id target)
	      then control := false
	  done
	with
	    IO.No_more_input -> n := -1
      in
	!n
    in
    let instno = find_inst_no target in
    let () = Printf.fprintf stderr "Found target %ld at trace line %d\n" 
      target instno
    in
    let visit_edge backward src dst instno insninfo =
      let eip = Trace.int64_of_uint32 insninfo.eip in
      let callee = Trace.int64_of_uint32 insninfo.callee in
      let address_id = insninfo.address_id in
      let rawinst = insninfo.raw_insn in
	if dst = target || (backward && Hashtbl.mem graph.vtable dst) ||
	  (not backward && Hashtbl.mem graph.vtable src)
	then (
	  if address_id <> 0l 
	  then (
	    let (istart, _) = addedge_noinfo graph address_id dst in
	      node_info istart 0L 0 (Int64.neg 1L) [||];
	      Printf.fprintf stderr "Added address id: 0x%lx\n" address_id;
	  );
	  let (_, iend) = addedge_noinfo graph src dst in
	    Printf.printf "label-%lx!" dst;
	    flush stdout;
	    (*Libasmir.print_i386_rawbytes eip rawinst;*)
	    Printf.printf " \\nCallee: 0x%Lx ESP: 0x%lx\\n[0x%lx]=0x%lx!\n"
	      callee insninfo.esp insninfo.mem_addr insninfo.mem_val;
	    flush stdout;
	    node_info iend eip instno callee rawinst
	)
    in
      for i = instno downto 1 do
	let (is_new, prop, define, insninfo) = read_record_n ic i
	in
	  if is_new = 0l
	  then (
	    (* regular propagation, adding edges from src to dst *)
	    if (prop.is_move <> 0l)
	    then (
	      for j = 0 to 3 do
		if (prop.dst_id.(j) <> 0l)
		then
		  visit_edge true prop.src_id.(j) prop.dst_id.(j)
		    i insninfo
	      done
	    )
	    else (
	      for j = 0 to 3 do
		if (prop.dst_id.(j) <> 0l)
		then
		  for k = 0 to 11 do
		    if (prop.src_id.(k) <> 0l)
		    then
		      visit_edge true prop.src_id.(k) prop.dst_id.(j)
			i insninfo
		  done
	      done
		
	    )
	  )
	  else 
	    for j = 0 to 3 do
	      if (define.(j).tr_dst_id<>0l) 
	      then
		visit_edge true (Int32.neg define.(j).tr_dst_id) 
		  define.(j).tr_dst_id i insninfo
	    done

      done;
      if args.forward then
	try
	  for i = instno+1 to max_int do
	    let (is_new, prop, define, insninfo) = read_record_n ic i in
	      if is_new = 0l
	      then (
		(* regular propagation, adding edges from src to dst *)
		if (prop.is_move <> 0l)
		then (
		  for j = 0 to 3 do
		    if (prop.dst_id.(j) <> 0l)
		    then
		      visit_edge false prop.src_id.(j) prop.dst_id.(j)
			i insninfo
		  done
		)
		else (
		  for j = 0 to 3 do
		    if (prop.dst_id.(j) <> 0l)
		    then
		      for k = 0 to 11 do
			if (prop.src_id.(k) <> 0l)
			  then
			  visit_edge false prop.src_id.(k) prop.dst_id.(j)
			    i insninfo
		      done
		  done
		    
		)
	      )
	  done
	with
	    IO.No_more_input ->  ()
  in
    if print 
    then
      print_trace ic
    else
      List.iter build_graph args.targetid

let cptgraph = {vtable = Hashtbl.create 10000}

let compact_graph graph cptgraph = 
  let process_node v vinfo = 
    let newid = Hashtbl.hash (vinfo.veip, vinfo.destaddr) in
    ()
  in
    Hashtbl.iter process_node graph.vtable
;;


(*============================= Main Body ==============================*)

let args = parsecmdline in
  if (args.trace_file <> "")
  then
    process_inst_trace args
  else if (args.tainttrace <> "")
  then (
      if (List.length args.targetid) > 0 
      then (
	process_taint_trace args false;
	Hashtbl.remove graph.vtable 0l;
	Dot.output_graph stdout graph;
      )
      else 
	process_taint_trace args true
  )
  else 
    raise (Arg.Bad "No trace file specified")

    







(* ------------------------- call history --------------------------*)

type funcInfo = {
    (* caller *)
    mutable parent : int;
    (* successors of this vertex *)
    mutable children : int list;
    name : string; 
    stackframe : int64; 
    lineno: char array; 
  }

type chGraph = {
    ftable : (int, funcInfo) Hashtbl.t; 
  }

let chg = { ftable = Hashtbl.create 10000; }

let getfuncid = 
  let id = ref 0 in
    id := !id + 1; !id

let addfunction g parentid nm stack lno =
  let funcid = getfuncid in 
  let parentinfo = Hashtbl.find chg.ftable parentid in
  let () = parentinfo.children <- funcid::parentinfo.children in
  let finfo = {parent = parentid; children = []; name = nm;
	       stackframe = stack; lineno = lno;} in
    Hashtbl.add g.ftable funcid finfo
    

module CH =
struct
  type t = chGraph

  module V =  struct
    type t = int
    let hash = Hashtbl.hash
    let equal = (=)
    let compare = compare
  end

  module E = struct
    type t = V.t * V.t
    let src (x, y) = x
    let dst (x, y) = y
  end

  let iter_vertex f g = Hashtbl.iter (fun k v -> f k) g.ftable
  let iter_edges_e f g =
    let visit_edge vstart vinfo =
      List.iter 
	(fun vend -> if Hashtbl.mem g.ftable vend then f (vstart, vend))
	vinfo.children
    in
      Hashtbl.iter visit_edge g.ftable
	

  let graph_attributes g = []
  let default_vertex_attributes g = []
  let vertex_name v = 
    let vinfo = Hashtbl.find chg.ftable v in
      vinfo.name
  let vertex_attributes v = 
      [`Label(vertex_name v);`Shape(`Box)]
  let default_edge_attributes g= []
  let edge_attributes e = []
  let get_subgraph v = None
end

let build_call_history inst lno =
  let rawbytes = inst#rawbytes in
    if ((int_of_char rawbytes.(0)) = 0xE8) then
      () (* function called *)

(* ------------------------- call history END --------------------------*)
