(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(**
   Converts ida and elf information into a set of functions, typechecks
   them, and returns the result. This file uses numerous heuristics
   and hacks, and could be planned out a lot better.

   Author: djb
*)

open Vine;;
open Vine_util;;

type funinfo_t = 
{
  name : string;
  start_address : int64;
  end_address : int64;
  is_extern : bool;
};;

(** where we put any instruction whose address is not within the range
    of any listed function *)
let unknown_addrs_function = {
  name = "unknown_addrs_function";
  start_address = 0L;
  end_address = 0L;
  is_extern = false;
};;

(** list of calls to a label potentially within the 
    same function *)
let calls_to_same_function = ref [];;

(** print a single inst line from the ida file as read in *)
let print_inst_item (addr, dl) =
	let (str:string) = List.fold_left (fun acc i ->
	  Printf.sprintf "%s %02x" acc i) "" dl in 
	  Printf.printf "0x%Lx%s\n%!" addr str

(** print a single function item *)
let print_funinfo item = 
  Printf.printf "%s %Lx - %Lx (%b)\n" item.name 
    item.start_address item.end_address item.is_extern 

(** print the list of read-in instruction information *)
let print_instrs instlist = 
  List.iter (fun x -> print_inst_item x) instlist

(** print the list of read-in function information *)
let print_functions fl = 
  List.iter (fun x ->  print_funinfo x) fl

(** print the assembly function table *)
let print_asm_fun_tbl tbl = 
  Hashtbl.iter (fun finfo insts ->
    print_funinfo finfo;
    print_instrs insts;
    Printf.printf "--------------------------\n%!") tbl

(** print the IR function table which maps funinfo_t -> ir list list *)
let print_ir_fun_tbl tbl = 
  Hashtbl.iter (fun finfo sll ->
    print_funinfo finfo;
    List.iter (fun sl -> 
      Vine.pp_program print_string ([], sl)) sll;
    Printf.printf "--------------------------\n%!") tbl



(** given an instruction address, and a list of function tuples
    (start, end, name), return the function tuple such that 
    start <= addr <= end 
    @param addr is an address
    @param funcs a list of funinfo_t's
    @return Some(function information) if address is within the range
    of a function in funcs else None
*)
let addr_to_function addr funcs : (funinfo_t option) = 
  try
    let x = 
    List.find (fun finfo -> 
      if( (finfo.start_address <= addr) && (addr < finfo.end_address))
      then true else false) funcs in
      Some(x)
  with
      Not_found -> None
;;

(** returns true iff there is no overlap in functions. fails otherwise 
    @param fl is a list of funinfo_t structures
    @return unit. Raises exception on failure.
*)
let check_function_overlap fl : unit = 
  (* XXX: this could be made linear instead of quadratic if given
     a sorted list of fns *)
  (* returns true iff there is no overlap *)
  let no_overlap f  = 
    List.for_all (fun f' ->
      (* we have: [f.start, f.end) [f'.start, f'.end). There is
	 overlap if any of the following two tests succeed:
	      1.  f.start <= f'.start <  f.end 
	      2.  f.start <= f'.end < f.end 
      *)
      if ((f.start_address <= f'.start_address) && 
	     (f'.start_address < f.end_address) && 
	     (f.name <> f'.name)) then (
	Printf.printf "%s and %s overlap (start)!\n%!" f.name f'.name; false)
      else ( 

	if ((f.start_address < f'.end_address) && 
	       (f'.end_address <= f.end_address) && 
	       (f.name <> f'.name)) then 
	  (Printf.printf "%s and %s overlap (end)!\n%!" f.name f'.name; false)
	else true) ) fl
  in
  let _ = List.for_all (fun finfo -> 
      if (no_overlap finfo) then true else
	failwith "Aborting due to overlap!") fl   in ()
;;

(** we first verify that none of the function ranges
    overlap, then return the sort. 
    @return funinfo_t list sorted by start addr. We remove duplicates.
*)
let sort_functions_by_start fl = 
  let () = check_function_overlap fl in
  let uniq = List.fold_left (fun acc x ->
    Vine_util.list_union [x] acc) [] fl 
  in 
  List.sort (fun f1 f2 -> 
               Int64.compare f1.start_address f2.start_address) fl 
      

(** sort the instruction list by instruction address *)
let sort_insts_by_addr instlist = 
  List.sort (fun (a, al) (b,bl) -> Int64.compare a b) instlist


(** reads in the function list from the IDA plugin file. 
    @param file the IDA pro plugin function information output filename.
    @return a list of funinfo_t's
 *)
let read_function_file file = 
  let scanbuf = Scanf.Scanning.from_file file in 
    (* throw away the first two lines *)
  let _ = Scanf.bscanf scanbuf "%[^\n]\n" (fun x -> x) in 
  let _ = Scanf.bscanf scanbuf "%[^\n]\n" (fun x -> x) in 
  let funcs = ref [] in 
  let read_one_line () = 
    try
      Scanf.bscanf scanbuf "0x%Lx 0x%Lx %[^\n]\n" 
	(fun x y z -> 
	  let finfo = 
	    {start_address = x;
	     end_address = y;
	     name = z;
	     is_extern = false; } in
	    funcs := finfo :: !funcs) ; true
    with
	End_of_file -> false
        | e -> prerr_string "Some sort of parsing error in
                  function file\n";
            raise e
  in
  while read_one_line () do
    ()
  done;
  !funcs
;;



(** read the inst file format. Anything more complicated that the
    parsing done here would probably merit it's own real parser. 
    @param file is the filename, i.e., getInstAddr.txt
    @return a pair list, where the first in the pair is the instruction
    address, and the second is a list of int's for the actual machine
    code. 
 *)
let read_inst_file file : ((int64 * int list) list) = 
  let scanbuf = Scanf.Scanning.from_file file in 
    (* throw away the first two lines *)
  let _ = Scanf.bscanf scanbuf "%[^\n]\n" (fun x -> x) in 
  let _ = Scanf.bscanf scanbuf "%[^\n]\n" (fun x -> x) in 
  let instrs = ref [] in 
  let read_one_line () = (
    (* first thing on line is the addr *)
    let addr = Scanf.bscanf scanbuf "%Li@ " (fun x -> x) in 
    let dlist = ref [] in 
    let read_one_int () = (
      Scanf.bscanf scanbuf "%x@ " (fun d -> dlist := d :: !dlist; true)
    )
    in 
      try
	while read_one_int () do
	  ()
	done; false
      with 
	  Scanf.Scan_failure _ -> 
	    Scanf.bscanf scanbuf "\n" ();
	    instrs := (addr, (List.rev !dlist))::!instrs; true
	| _ -> false
  ) in 
    try
      while read_one_line () do
	()
      done; failwith "Shouldn't get here"
    with
	End_of_file -> List.rev !instrs
    | e -> prerr_string "Some sort of parsing error in
                  inst file\n";
        raise e
;;



(** match each instruction to it's enclosing function.
    @param insts the list of instruction tuples (address, char array)
    @param funcs a list of funinfo_t's.
    @return a hashtbl mapping funinfo_t -> list of instruction tuples
    The table will have a key for all functions in the param funcs.
    This means, for example, for extern functions the list of
    instructions will be empty in the table.
*)
let match_addrs_to_functions insts funcs =
  let funcs = sort_functions_by_start funcs in 
  let asmfuntbl = Hashtbl.create (List.length funcs) in
    (* add all the functions to the hashtbl (so hashtbl.find below
       doesn't throw an exception) *)
  List.iter ( fun x -> Hashtbl.add asmfuntbl x []) funcs;

  (* sort insts *)
  let insts = sort_insts_by_addr insts in

  let rec insts_to_funcs insts funcs =
    match insts with
    | [] -> ()
    | (addr, al) :: insts_t ->
        match funcs with
        | f :: funcs_t when addr >= f.end_address ->
            (* move to next function *)
            insts_to_funcs insts funcs_t
        | _ ->
            let f =
              if 
                (* XXX working around ocaml quirk here *)
                ((funcs = []) || 
                  (match funcs with 
                   | f :: _ when addr < f.start_address -> true
                   | _ -> false)
                ) then (
                  Printf.eprintf "Warning: 0x%Lx doesn't seem" addr;
                  Printf.eprintf " to belong to a function. Adding to ";
                  Printf.eprintf " function %s\n%!" 
                    unknown_addrs_function.name;
                  if not (Hashtbl.mem asmfuntbl unknown_addrs_function) then
                    Hashtbl.add asmfuntbl unknown_addrs_function [];
                  unknown_addrs_function
                )
              else 
                List.hd funcs
            in
            (* add to function f *)
            let old_inst_list = Hashtbl.find asmfuntbl f in 
            let new_inst_list = (addr, al)::old_inst_list in 
	    Hashtbl.replace asmfuntbl f new_inst_list;

            (* move to next instr *)
            insts_to_funcs insts_t funcs
  in
  insts_to_funcs insts funcs;

  List.iter 
    (fun f -> 
       let l = Hashtbl.find asmfuntbl f in 
       let sl = List.rev l in 
       Hashtbl.replace asmfuntbl f sl) 
    funcs;

  if Hashtbl.mem asmfuntbl unknown_addrs_function then (
    let sl = (List.rev (Hashtbl.find asmfuntbl unknown_addrs_function)) in
    Hashtbl.replace asmfuntbl unknown_addrs_function sl);

  asmfuntbl

(*
    (* insert the instruction into the correct function. Note that at
       this point the inst list in the hashtbl will be in arbitrary
       order *)
    List.iter (fun (a, al) -> 
      let fopt = addr_to_function a funcs in  (* find function for inst *)
      let f = (match fopt with
	  Some(f') -> f' (* instruction maps to a function. normal case *)
	| None ->
	    (* instruction is not within the range of anything
	       in the funcs funinfo_t list. This can happen
	       because funinfo_t is incomplete, e.g., the IDA
	       pro plugin didn't give us *all* functions for
	       some reason.  *)
	    Printf.eprintf "Warning: 0x%Lx doesn't seem" a;
	    Printf.eprintf " to belong to a function. Adding to ";
	    Printf.eprintf " function %s\n%!" unknown_addrs_function.name;
	    if not (Hashtbl.mem asmfuntbl unknown_addrs_function) then
	      Hashtbl.add asmfuntbl unknown_addrs_function [];
	    unknown_addrs_function
      ) in
      let old_inst_list = Hashtbl.find asmfuntbl f in 
      let new_inst_list = (a,al)::old_inst_list in 
	Hashtbl.replace asmfuntbl f new_inst_list
    ) insts;

    (* At this point, insts for each instruction may be in arbitrary
       order.  Sort them by address *)
    List.iter (fun f -> 
      let l = Hashtbl.find asmfuntbl f in 
      let sl = sort_insts_by_addr l in 
	Hashtbl.replace asmfuntbl f sl) funcs;
    (* return the tbl *)
    asmfuntbl
*)
;;

(** Convert a list of (address, raw bytes array) to the vine IR.
    Remove last superflous jump (inserted by vex) on last translated
    instruction 
    @param el a list of tuples of (address, array of ints)
    @return a list of ir stmts
*)
let raw_bytes_to_vine el = 
  let rec _raw_bytes_to_vine el acc =
    match el with
    | (addr, bytes) :: ys -> 
        let bytes = List.map char_of_int bytes in
        let arr = Array.of_list bytes in
	let ir = Asmir.asm_bytes_to_vine addr arr in 
	_raw_bytes_to_vine ys (ir::acc)
    | [] -> List.rev acc
  in
  _raw_bytes_to_vine el []

(**
   @param asmtbl, such as that produced by match_addrs_to_functions
   @return irtbl which maps a funinfo_t to the list of IR instructions
   There will be an entry in irtbl for each entry in asmfuntbl.
*)
let asm_tbl_to_ir_tbl asmtbl =
  (*  let i = ref 0 in *)
  let irtbl = Hashtbl.create (Hashtbl.length asmtbl) in
  Hashtbl.iter (fun finfo insns ->
(*
                  (if ((!i mod 100) = 0) then 
                     Printf.printf "Disasmd %d hits %d missed %d\n%!" 
                       !i !Asmir.exp_cache_hits !Asmir.exp_cache_misses);
                  inc i;
*)
                  let stmts = raw_bytes_to_vine insns in
	          Hashtbl.add irtbl finfo stmts)
    asmtbl;
  irtbl
;;


(** @param instfile - IDA Pro plugin instruction file
    @param funcfile - IDA Pro plugin function fille
    @return an ir hashtbl from (start,end,name) -> ir inst list list.
    It's a list list because each asm instruction gets translated
    into a ir list, and we have a list of such asm statements.
*)
let ida_to_irtbl instfile funcfile = 
  let instrs = read_inst_file instfile in 
  let funcs = read_function_file funcfile in 
  let asmtbl = match_addrs_to_functions instrs funcs in 
  let irtbl = asm_tbl_to_ir_tbl asmtbl in 
    irtbl

(** Convert an IR hashtbl as described in comment of ida_to_irtbl to a
    list of functions. If a member in the IR table is declared extern,
    check to make sure there are no statements, but otherwise do not
    include it in the functions.
    @param irtbl a hashtbl from funinfo_t to ir list list 
    @return a list of function definitions.
*)
let irtbl_to_functions irtbl = 
    Hashtbl.fold (fun finfo irll acc -> 
      let irstmts = List.flatten irll in 
	match (finfo.is_extern, irstmts) with
	    true, [] -> (* an extern function with no irstmts, just
			  like we expect. Add decl. *)
	      acc
	  | true, _ ->  (* an extern function with ir stmts. Shouldn't
			   happen! *)
	      (*
		FIXME: In the case of smbd it actually looks pretty normal. --aij
	      prerr_endline "extern IR stmts:";
	      List.iter (Vine.pp_stmt prerr_string) irstmts;
	      prerr_endline "END extern IR stmts.";
	      failwith 
	      (Printf.sprintf "extern %s  has IR statements!"
		  finfo.name)
	      *)
	      acc
	  | false,  _ -> (* we don't distinguish between empty
			    static functions and static functions with
			    stmts like we do for extern functions *)
	      let f= Function(finfo.name, None, [], false, Some(Block([],
							      irstmts))) in 
		f::acc
    ) irtbl []
;;


(** 
    @param funcs is a list of functions. Assume this is unique, else
    we will make multiple declarations.
    @return a unique list of declarations
*)
let mk_fun_decls funcs = 
  List.map (fun finfo ->
    Function(finfo.name, None, [], finfo.is_extern, None)
  ) funcs
;;

(**
   @param fl is a list of functions
   @return fl with direct call-jmps replaced with Calls,
   and ret-jmps replaced with Rets
*)
let replace_calls_rets fl funcs =
  let callreplacer s = 
    match s with
	Jmp(Name(l)) as j ->  (
	  let addr = label_to_addr l in 
	    try
	      (* the call needs to be to the start of a function *)
	      let finf = List.find (fun x -> x.start_address = addr) funcs 
	      in Call(None, finf.name, [])
	    with
		Not_found ->  (* this could be a call to a block
				 within the same function, e.g.:
				 804ae03:  call   804ae08 <_fini+0xc>
				 804ae08:  pop    %ebx
				 804ae09:  add    $0x16e4,%ebx 
				 in this case, leave the jump
				 alone, but raise warning.
				 XXX: FIXME
			      *)
		  ( Printf.eprintf "Warning: call to non-function: %s\n"
		      (stmt_to_string s);
		    calls_to_same_function := j ::
		      !calls_to_same_function;
		    j)
	)
      | Jmp(_) -> 

	  (*Printf.eprintf "Warning: indirect call %s\n" *)(*pm*)
	    (stmt_to_string s);
	  Attr(s, ACall)

	  (* failwith (Printf.sprintf "Indirect call?: %s"
			       (stmt_to_string s)) *)
      | _ -> failwith "call not translated as jmp?"
  in
    (* replace returns with "return" in "replace_special_jumps" below *)
  let retreplacer s = Return(None)  in
    (* do the call/return replacements. *)
  let fl = List.map (fun x ->
    match x with
	Function(v,topt,args,false,Some(Block(dl,sl))) ->
	  let sl' = replace_special_jumps callreplacer retreplacer sl in 
	    Function(v,topt,args,false,Some(Block(dl,sl')))
      | Function(v,_,_,true, None) -> x
                    ) fl in
  fl 

(** Rename functions with duplicate names, if any. *)
let uniqify_funcs funcs =
  let rec find_free_name taken s i =
    let candidate = Printf.sprintf "%s___%d" s i in
    if Vine_util.StringSet.mem candidate taken then
      find_free_name taken s (i+1)
    else
      candidate
  in
  let funcs, symset = 
    List.fold_left 
      (fun (funcs, symnames) finfo ->
         let name = 
           if (Vine_util.StringSet.mem finfo.name symnames) then (
             let new_name = find_free_name symnames finfo.name 0 in
             Printf.printf "warning! renaming duplicate fnname %s -> %s\n" 
               finfo.name new_name;
             new_name
           ) else
             finfo.name
         in
         { finfo with name=name } :: funcs, 
         Vine_util.StringSet.add name symnames)
      ([], Vine_util.StringSet.empty)
      funcs
  in
  funcs

(** 
    @param instrs is a list of (address, array of instr int bytes)
    @param funcs is a list of funinfo_t's describing functions
    @return list of (loosely-typechecked) IR functions
*)
let to_irfunctions instrs funcs =
  let funcs = uniqify_funcs funcs in
  let asmtbl = match_addrs_to_functions instrs funcs in 
  let tbl = asm_tbl_to_ir_tbl asmtbl in 
  let fl = irtbl_to_functions tbl in 
    (* remove unknowns *)
  let fl = List.rev_map (fun s -> fst (Vine.remove_unknowns s))
    fl in 
    (* deendianize. *)
  let fl = List.rev_map (
     Vine.stmt_accept
       (new Vine_memory2array.memory2array_visitor
          (fst Asmir.x86_mem, Vine_memory2array.LittleEndian,
          (Vine.Temp(fst Asmir.x86_mem, snd Asmir.x86_mem))))) fl
  in
    (* flatten scope *)
  let fl = List.map (fun x -> 
    match x with 
	Function(_, _, _, false, _) -> Vine_alphavary.descope_function x
      | Function(_,_,_,true,None) -> x
      | _ -> failwith "Should only get functions here") fl in
    (* print out statements *)
    (*   let _ = List.iter (fun x -> *)
    (*     pp_program print_string ([], [x])) ida_fl in  *)

    (* replace calls with "Call( function)". Called during
       "remove_special_jumps" below *)

  let fl = replace_calls_rets fl funcs in

    (* in order to typecheck, we need to add a declaration for each
       function *)
  let fundecls = mk_fun_decls funcs in 
  let fl = fundecls @ fl in 
    (* registers are declared outside the function scope *)
  let dl = (Asmir.x86_mem :: Asmir.x86_regs) in 
    (* at this point we have a flattened, de-endianized, call/return
       replaced list of functions with "unknown"'s removed. 
       Now typecheck *)

  let () = Vine_typecheck.typecheck_jmp_targets := false in 
  let () =
    try Vine_typecheck.typecheck (dl, fl) 
    with TypeError s as e ->
      print_endline "TypeError in dissassembly:";
      print_endline s;
      (* raise e *)
      print_endline "FIXME: Ignoring type error..."
  in
  let () = Vine_typecheck.typecheck_jmp_targets := true in 
    (* assuming all is good, return the function list *)
    fl
;;

      
(** @param instfile - IDA Pro plugin instruction list file
    @param funcfile - IDA Pro plugin function list file
    @return (function information,Vine functions). Note we include in
    the list of functions the declarations for all functions, even
    those extern.
*)
let ida_to_irfunctions instfile funcfile =
  let instrs = read_inst_file instfile in 
  let funcs = read_function_file funcfile in 
  let fl = to_irfunctions instrs funcs in 
    (funcs, Asmir.x86_eflags_helpers() @ fl)
;;

(** print out x86 symbols. *)
let print_syms syms = 
  List.iter (fun (s,n,is_fun, is_dynamic) ->
    Printf.printf "Symbol %s %Lx (fun = %b dynamic = %b)\n%!"
      n s is_fun is_dynamic) syms
;;

(** remove symbols with the same start address from a symbol list
*)
let remove_duplicate_syms syms = 
  List.fold_left (fun acc (s,n,f,d) ->
    if (List.exists (fun (addr,_,_,_) -> s = addr) acc) then
      (
	Printf.eprintf "Removing duplicate symbol %s\n%!" n; acc
      ) else (
	(s,n,f,d)::acc
      )
  ) [] syms
;;

(** remove the '@' sign from any symbol name, replacing it with '_' *)
let fix_syms_atsigns =
  let regex = Str.regexp "[@\\.]" in
    List.map
      (fun (a,s,b,c) ->
	 let s' = Str.global_replace regex "_" s in
	   (a,s',b,c))
;;

(** takes in a list of symbol tuples
    (start,name,is_function,is_dynamic), and creates a list of sorted
    funinfo_t using heuristics. Note that one big difference between a
    symbol and a funinfo is symbols don't give the end address of
    functions, while here we use heuristics to figure it out.
    @param syms the symbol list in the above form
    @param last_addr the last address in the program
    @return list of function info tuples. We check for overlap in
    function address ranges before returning.
*)
let syms_to_funcs syms last_addr = 
  let syms = List.filter (fun (s,n,is_fun, is_dynamic) ->
    is_fun = true) syms in 
  let syms = remove_duplicate_syms syms in 
  let syms = fix_syms_atsigns syms in 
  let syms = List.sort (fun (s,_,_,_) (s',_,_,_) -> Int64.compare s s') syms
  in
  let rec create_end_addr lst = 
    match lst with
	(s,n,_, d)::(s',n',f',d')::ys ->
	  let top = {name = n; start_address = s; 
		     end_address = s'; is_extern = d; } in 

	  let tl = create_end_addr ((s',n',f',d')::ys)
	  in top::tl
      | (s,n,_,d)::[] -> [{name=n; start_address = s; 
			   end_address = last_addr; is_extern = d;}]
      | [] -> failwith "Unexpected empty symbol list!"
  in  
  let funcs = create_end_addr syms in 
(*   let _ = print_functions funcs in  *)
  let _ = check_function_overlap funcs in 
    funcs
;;

let weedout_known_bad_syms syms = 
  List.filter (fun (s,n,is_fun, is_dynamic) ->
		 if n = "gcc2_compiled." then false else true) syms

(*
let elf_to_irfunctions filename =
  let instrs = Asmir.raw_insts_of_file filename in 
  let instrs = List.sort (fun (a,_) (b,_) -> Int64.compare a b) instrs in 
  let syms = Asmir.vine_symbols_of_file filename in 
  let syms = weedout_known_bad_syms syms in 
  let () = print_syms syms in 
  let (last_instr,_) = Vine_util.list_last instrs in 
  let funcs = syms_to_funcs syms last_instr in
(*  let () = print_functions funcs in  *)
  let vinestmts =  to_irfunctions instrs funcs  in 
    (funcs, Asmir.x86_eflags_helpers() @ vinestmts)
*)  
;;

(** @param filename
    @return PMap of address to function name
*)
let read_imp_table filename =
  let ic = open_in filename in

  (* discard two lines *)
  let _ = input_line ic in
  let _ = input_line ic in

  let imp_table = ref PMap.empty in
  let add_entry fnname addr dll = 
    imp_table := PMap.add addr fnname !imp_table
  in
  (try
     while true do
       Scanf.fscanf ic "%s 0x%lx %s" add_entry
     done
   with
   | End_of_file -> ());
  !imp_table

(** 
    Uses import and export tables (obtained by parsing winedump
    output) to rewrite indirect jmps to an IAT slot to an actual
    call. If the corresponding function is in one of the provided
    export tables, then the actual disassembled IR function will be 
    called. Otherwise we will call an external function, which will
    be added to the function declarations.     

    @param fninfos list of fninfo structs
    @param stmts a stmt list
    @param winedump_filenames list of files containing winedump output
    @return (updated fninfos, updated stmts)
*)
let pe_link fninfos stmts winedump_filenames =
  let merge_pmaps large small =
    PMap.foldi
      PMap.add
      small (* iterate over the small one *)
      large (* adding to the large one *)
  in

  (* build import and export tables from provided
     winedump files *)
  let imp_table, exp_table = 
    List.fold_left
      (fun (imp_table_acc, exp_table_acc) winedump_filename ->
         let imp_table, exp_table = 
           Winedump.parse winedump_filename in
         (merge_pmaps imp_table_acc imp_table,
          merge_pmaps exp_table_acc exp_table))
      (PMap.empty, PMap.empty)
      winedump_filenames
  in

  Printf.printf "Import table:\n";
  PMap.iter 
    (fun isa (mod_name, ord, fnname_o) ->
       Printf.printf 
         "0x%Lx -> %s %d %s\n"
         isa
         mod_name
         ord
         (match fnname_o with Some(x) -> x | None -> "byordinal"))
    imp_table;
  Printf.printf "\n";
  
  Printf.printf "Export table:\n";
  PMap.iter 
    (fun (mod_name, ord) (addr, fnname) ->
       Printf.printf 
         "%s %d -> 0x%Lx %s\n"
         mod_name
         ord
         addr
         fnname)
    exp_table;
  Printf.printf "\n";

  (* go from address to function name *)
  (* XXX: naive slow implementation *)
  let addr_to_fnname addr =
    let fninfo = 
      List.find 
        (fun fninfo -> 
           fninfo.start_address = addr)
        fninfos
    in
    fninfo.name
  in

  let vis =
object (self)
  inherit nop_vine_visitor
  val mutable it_addr = 0L
  val mutable is_jmp = false
  val mutable ext_fnnames = StringSet.empty
  method get_ext_fnnames = ext_fnnames
  method visit_stmt stmt =
    match stmt with
      (* XXX: using asm comments to get indirect jmp target.
         this is ugly and fragile. should do some analysis to
         determine what address(es) could be used by the actual
         IR jmp *)
    | Comment(c) ->
        (try
           Scanf.sscanf
             c
             "%_Lx: call *%Lx%!"
             (fun a -> it_addr <- a; is_jmp <- false)
         with
         | Scanf.Scan_failure _
         | Failure _ ->
             ()
        );
        (try
           Scanf.sscanf
             c
             "%_Lx: jmp *%Lx%!"
             (fun a -> it_addr <- a; is_jmp <- true)
         with
         | Scanf.Scan_failure _
         | Failure _ ->
             ()
        );

        DoChildren
    | Jmp(e) when it_addr <> 0L ->
        (* look it up in the import table *)
        if not (PMap.mem it_addr imp_table) then (
          Printf.eprintf 
            "Warning: no import table entry for %Lx\n"
            it_addr;
          SkipChildren
        ) else (
          let (mod_name, ord, imp_fnname_o) =
            PMap.find it_addr imp_table in
          Printf.printf "call to: %s %d\n" mod_name, ord;

          (* figure out fn name *)
          let fnname = 
            if (PMap.mem (mod_name, ord) exp_table) then (
              (* it's in the export table. change to a call to that fn *)
              let (fn_addr, exp_fnname) = 
                PMap.find (mod_name, ord) exp_table in
              
              (* get the actual fnname we're already using *)
              let fnname = 
                try
                  addr_to_fnname fn_addr 
                with
                | Not_found ->
                    Printf.eprintf 
                      "Warning: exported function not in fn info: %s %s %Lx\n"
                      mod_name
                      exp_fnname
                      fn_addr;
                    let fnname = "notfoundXXX" in
                    ext_fnnames <- StringSet.add fnname ext_fnnames;
                    fnname
              in
              fnname
            ) else (
              (* not in export table, so make a call to external fn *)
              let fnname = 
                Printf.sprintf 
                  "%s_%d_%s"
                  mod_name
                  ord
                  (match imp_fnname_o with 
                   | Some(fnname) -> fnname 
                   | None -> "byordinal")
              in
              ext_fnnames <- StringSet.add fnname ext_fnnames; 
              fnname
            )
          in
          Printf.printf " -> %s\n" fnname;
          
          (* reset *)
          it_addr <- 0L;

          if is_jmp then
            (* we're changing a jmp to a call. maintain original
               control flow by inserting a ret immediately after
               the call. *)
            ChangeTo(
              Block([], 
                    [ Call(None, fnname, []);
                      Return(None) ]))
          else
            ChangeTo(Call(None, fnname, []))
        )
    | _ ->
        DoChildren
end
  in
  let stmts =
    List.map
      (stmt_accept vis)
      stmts
  in

  (* add external function decls to stmt list and fninfos *)
  let ext_fn_decls, ext_fn_infos = 
    List.fold_left
      (fun (decls, infos) fnname ->
         let decl = 
           Function(fnname, None, [], true, None)
         in
         let info =
           {
             name = fnname;
             start_address = 0L;
             end_address = 0L;
             is_extern = true
           }
         in
         (decl :: decls), (info :: infos))
      ([], [])
      (StringSet.elements (vis#get_ext_fnnames))
  in

  List.rev_append ext_fn_infos fninfos,
  List.rev_append ext_fn_decls stmts


(**
   @param filenames list of executables
   @return list of (addr, ir)
*)
let bins_to_irlist filenames =
  let binary_to_ir acc filename =
    let asmprog = Asmir.disassemble_program filename in
    let (dl, sl) = Asmir.asmprogram_to_vine asmprog in
    assert (dl = []);
    let rec foo sl acc =
      match sl with
      | (Comment _ as c) :: (Block(_, Label(l)::_) as b) :: tl ->
          let addr = label_to_addr l in
          foo tl ((addr,[c;b])::acc)
      | [] ->
          acc
      | _ -> failwith "ir didn't match in binary_to_ir"
    in
    foo sl acc
  in

  let tuples = 
    List.fold_left
      binary_to_ir
      []
      filenames
  in
  tuples

(**
   @param execfiles list of filenames
   @param fninfo list of functions, as from read_function_file
   @return mapping from address to IR list
*)
let bins_to_irtbl execfiles fninfo =
  let irlist = bins_to_irlist execfiles in
  let ir_tup_tbl = match_addrs_to_functions irlist fninfo in
  let irtbl = Hashtbl.create (Hashtbl.length ir_tup_tbl) in
  Hashtbl.iter
    (fun finfo tup_list -> 
       let (_, sl) = List.split tup_list in
       Hashtbl.add irtbl finfo sl)
    ir_tup_tbl;
  irtbl

