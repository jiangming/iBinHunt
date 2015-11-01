(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   Extract argument information of a call instruction.
   
   @author Zhenkai Liang
*)

module Trace=Temu_trace

let get_arg_location trace_iface insn_num arg_num =
  let inst_o =
    try
      let _ = trace_iface#seek_instruction insn_num in
	Some(trace_iface#read_instruction)
    with
        _ -> None
  in
  let espval = 
    match inst_o with
	None -> 0l
      | Some(inst) -> 
	  inst#esp#opvalue
  in
  let argloc = Int32.add espval  (Int32.of_int ((arg_num-1)*4))
  in
    Int64.of_int32 argloc

(** return value: 
    instruction number setting the arguemnt,
    operand value,
    operand taint flag,
    operand origin array,
    operand offset array
*)
let rec get_arg_info trace_iface insn_num argloc =
  if insn_num <= 0L then
    (0L, 0l, 0L, [||], [||])
  else 
    let inst_o =
      try
	let () = trace_iface#seek_instruction insn_num in
	  Some(trace_iface#read_instruction)
      with
        _ -> None
    in
    let inst_o =
      match inst_o with
	  None -> None
	| Some(inst) -> 
	    if inst#operand.(0)#optype = Trace.TMemLoc &&
	      inst#operand.(0)#opaddr = argloc
	    then
	      Some(inst)
	    else
	      None
    in
      match inst_o with
	| Some(inst) -> 
	    let opvalue = inst#operand.(1)#opvalue in
	      (insn_num, opvalue, inst#operand.(1)#taintflag, 
	      inst#operand.(1)#origin, inst#operand.(1)#offset)
	| None -> get_arg_info trace_iface (Int64.pred insn_num) argloc
	    
;;

let usage () = 
  Printf.fprintf stderr "%s: tracefile instruction_number argument_number\n" 
    Sys.argv.(0)
in
  if Array.length Sys.argv < 3 
  then
    usage ()
  else
    let tracefile = Sys.argv.(1) in
    let insn_num = Int64.of_string Sys.argv.(2) in
    let arg_num = int_of_string Sys.argv.(3) in
    let trace_iface = Trace.open_trace tracefile in
    let argloc = get_arg_location trace_iface insn_num arg_num in
    let (insn, value, taintflag, _, _) = 
      get_arg_info trace_iface insn_num argloc 
    in
      Printf.printf ("Argument %d of instruction %Ld set by instruction %Ld.\n" 
	  ^^ "Value: 0x%lX, taintflag: 0x%LX\n")
	arg_num insn_num insn value taintflag


