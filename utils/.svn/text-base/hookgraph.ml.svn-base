(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   This program analyzes an attack trace and output how attack propagates
   
   @author Zhenkai Liang
*)

let int64_of_uint32 x =
  Int64.logand 
    (Int64.of_int32 x) 
    0x00000000ffffffffL


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
(*       ("-start",  *)
(*       Arg.String (fun s -> cmdlineargs.start <- int_of_string s), *)
(*       "Line number of the instruction to start");  *)

(*       ("-first",  *)
(*       Arg.String (fun s -> cmdlineargs.first <- int_of_string s), *)
(*       "Line number of first instruction");  *)

(*       ("-forward",  *)
(*       Arg.Unit (fun s -> cmdlineargs.forward <- true), *)
(*       "Perform forward analysis of taint relation, output on stdout");  *)

(*       ("-last",  *)
(*       Arg.String (fun s -> cmdlineargs.last <- int_of_string s), *)
(*       "Line number of last instruction");  *)

(*       ("-count",  *)
(*       Arg.Unit (fun s -> cmdlineargs.count <- true), *)
(*       "Display line number");  *)
      
(*       ("-o", *)
(*       Arg.String (fun s -> cmdlineargs.output <- s), *)
(*       "Output file name"); *)

(*       ("-insttrace",  *)
(*       Arg.String (fun s -> cmdlineargs.trace_file <- s), *)
(*       "Name of instruction trace file");  *)

      ("-impacttrace",
      Arg.String (fun s -> cmdlineargs.tainttrace <- s),
      "\tName of taint trace file");

(*       ("-taintoffset",  *)
(*       Arg.String (fun s -> cmdlineargs.taintoffset <- Int32.of_string s), *)
(*       "Only process the instructions operated on taint offset");  *)

      ("-targetid",
      Arg.Int (fun s -> cmdlineargs.targetid <- (Int32.of_int s)::cmdlineargs.targetid), 
      "\tHook's Dependency ID");
    ] 
  in 
  let () =
    Arg.parse arg_spec (fun s -> ()) 
      "Usage: trace_reader [options] trace"
  in
    cmdlineargs


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
  }

type depGraph = {
    vtable : (int32, vInfo) Hashtbl.t; 
  }

let addedge g vstart vend ip dest raw ino = 
  let istart = try Hashtbl.find g.vtable vstart 
    with Not_found -> 
      let tmp = {pred=[];succ=[];veip=0L;instno=0;destaddr=0L;rawbytes=[||]} in
	Hashtbl.add g.vtable vstart tmp; tmp
  in
  let iend = try Hashtbl.find g.vtable vend
    with Not_found -> 
      let tmp = {pred=[];succ=[];veip=ip;instno=ino;destaddr=dest;rawbytes=raw} in
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
      let tmp = {pred=[];succ=[];veip=0L;instno=0;destaddr=0L;rawbytes=[||]} in
	Hashtbl.add g.vtable vstart tmp; tmp
  in
  let iend = try Hashtbl.find g.vtable vend
    with Not_found -> 
      let tmp = {pred=[];succ=[];veip=0L;instno=0;destaddr=0L;rawbytes=[||]} in
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
	  (*Libasmir.print_i386_rawbytes (int64_of_uint32 insninfo.eip) 
	    insninfo.raw_insn;*)
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
      let eip = int64_of_uint32 insninfo.eip in
      let callee = int64_of_uint32 insninfo.callee in
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
  if (args.tainttrace <> "")
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
      
      
