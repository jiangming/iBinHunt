(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_tovine.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@gs3102.sp.cs.cmu.edu>
*
*  Started on  Tue Apr 24 14:01:53 2007 David Brumley
*  Last update Thu Oct 25 11:29:35 2007 David Brumley
*)
(**)

open Vine;;
open Vine_util;;
open Vine_idadb;;
module List = ExtList.List
(* module D = Debug.Make(struct let name = "vine_tovine" end)  *)
module D = Debug.NoDebug;; 

let flag_is_elf = ref false
let flag_is_ida = ref false
let flag_idadb_fileid = ref 0
let flag_idadb_file = ref ""
let flag_elf_file = ref ""

(** if true, we enable some heuristics for deciding when a function is
    really dynamic. For example, functions ending in plt are
    considered dynamic and the corresponding code is not converted to
    the IR (because, for example, the code really is just implementing
    the call to the DLL/.so)
*)
let function_heuristic = ref true



let speclist = [
  ("-elf",
   Arg.Tuple([Arg.Set(flag_is_elf);
		Arg.Set_string(flag_elf_file)]),
   "<elf_file> Process an elf binary."
  );
  ("-ida", 
   Arg.Tuple [Arg.Set(flag_is_ida);
	      Arg.Set_string(flag_idadb_file);
	      Arg.Set_int(flag_idadb_fileid);
	     ],
   ("<idadb> <file_id> Process executable with file id <fileid>"^
   " in IDA database <idadb>.")
  );
]


type funinfo_t = 
{
  name : string;
  start_address : int64;
  end_address : int64;
  is_extern : bool;
  tails : (int64 * int64) list;
};;

(** where we put any instruction whose address is not within the range
    of any listed function *)
let unknown_addrs_function = {
  name = "unknown_addrs_function";
  start_address = 0L;
  end_address = 0L;
  is_extern = false;
  tails = [];
};;

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
	Printf.eprintf "%s (%Lx-%Lx) and %s (%Lx-%Lx) overlap!\n%!" 
	  f.name f.start_address f.end_address 
	  f'.name f'.start_address f'.end_address; 
	false)
      else ( 

	if ((f.start_address < f'.end_address) && 
	       (f'.end_address <= f.end_address) && 
	       (f.name <> f'.name)) then  (
	Printf.eprintf "%s (%Lx-%Lx) and %s (%Lx-%Lx) overlap!\n%!" 
	  f.name f.start_address f.end_address 
	  f'.name f'.start_address f'.end_address; 
	false)
	else true) ) fl
  in
  let _ = List.for_all (fun finfo -> 
      if (no_overlap finfo) then true else
	failwith "Aborting due to overlap!") fl   in ()
;;

(** print out x86 symbols. *)
let print_syms syms = 
  List.iter (fun (s,n,is_fun, is_dynamic) ->
    D.dprintf "Symbol %s %Lx (fun = %b dynamic = %b)\n%!"
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

(** returns true if s "looks" like it might be really a dynamic
    symbol, e.g., it ends in plt, etc *)
let heuristic_test finfo = 
  let last =
    try Str.last_chars finfo.name 3 
    with Invalid_argument _ -> ""
  in 
  let b1 = last = "plt" in
  let first = Str.first_chars finfo.name 1 in 
  let b2 = first = "_" in
  let b3 =  finfo.name = "atexit" || 
    finfo.name = "call_gmon_start" || 
    finfo.name = "frame_dummy" in
  (*let b4 =Int64.abs (Int64.sub finfo.end_address finfo.start_address) > 100000L*)
 let b4 =Int64.abs (Int64.sub finfo.end_address finfo.start_address) < 7L (*MingJiang *)
	 in 
    b1 || b2 || b3 || b4

(**  we look at the function symbol information and decide whether
     name is really a static function symbol or whether it should be 
     treated as a dynamic function symbol.  Dynamic functions (aka
     dynamically linked functions) do not have a corresponding
     IR. Thus, the more functions we consider dynamic, the smaller our
     IR is. 
*)
let do_function_heuristics finfos = 
  List.map (fun finfo -> 
	      if heuristic_test finfo then 
		  {finfo with is_extern = true}
	      else 
		finfo
	   ) finfos
      

(** remove the '@' sign from any symbol name, replacing it with '_' *)
let fix_syms_atsigns =
  let regex = Str.regexp "[@\\.]" in
    List.map
      (fun (a,s,b,c) ->
	 let s' = Str.global_replace regex "_" s in
	     (a,s',b,c)
      )
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

    XXX: We assume the last_addr is canonical, but this is not
    precise.  Different symbols may be for different segments, and we
    should take this into consideration. 
*)
let syms_to_funinfo syms last_addr = 
  let syms = List.filter (fun (s,n,is_fun, is_dynamic) ->
    is_fun = true) syms in 
  let syms = remove_duplicate_syms syms in 
  let syms = fix_syms_atsigns syms in 
  let syms = List.stable_sort 
    (fun (s,_,_,_) (s',_,_,_) -> Int64.compare s s') syms
  in

  let rec create_end_addr lst = 
    match lst with
	(s,n,_, d)::(s',n',f',d')::ys ->
	  let top = 
 	    if ( (Int64.sub s' s) > 0L) then  
	      {name = n; start_address = s;
	       end_address = (Int64.add s' (-1L)); is_extern = d; tails=[] } 
	    else
	      {name = n; start_address = s; 
	       end_address = s'; is_extern = d; tails=[]} 
	  in
	  let tl = create_end_addr ((s',n',f',d')::ys)
	  in top::tl
      | (s,n,_,d)::[] ->
	  [{name=n; start_address = s;
	    end_address = last_addr; is_extern = d; tails=[]}]
      | [] -> failwith "Unexpected empty symbol list!"
  in  
  let funcs = create_end_addr syms in 
  let _ = check_function_overlap funcs in 
    funcs
;;


let populate_function g instmap
    {name=name; is_extern=is_extern; start_address=saddr; end_address=eaddr; tails=tails}
    =
  let () = D.dprintf "populating %s %b %Ld (%Lx-%Lx)%!" name is_extern
    (Int64.sub eaddr saddr) saddr eaddr in
  let tr_range s e =
    List.map snd (Asmir.instmap_translate_address_range g instmap s e)
  in
  let st = tr_range saddr eaddr   in
  let tls = List.map (uncurry tr_range) tails in
  let alst = st :: [[ Return(None)]] :: tls in
  let sl =  List.flatten (List.flatten alst) in
    Function(name, None, [], false,
	     Some(Block([],sl)))

(** populate functions with IR statements.  We may decide during
    populating that some so-called function really isn't, so we return
    an updated list of function infos
*)
let populate_functions g  finfos instmap = 

  let finfos = 
    if !function_heuristic then
      do_function_heuristics finfos 
    else
      finfos
  in
    (* do not populate dynamic functions *)
  let finfos' = List.filter (fun finfo -> not finfo.is_extern) finfos in
  let fls = List.map (populate_function g instmap) finfos' in
    (fls, finfos)

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

    
let get_elf_funinfos filename = 
  let () = D.dprintf "Getting symbols%!" in
  let syms = Asmir.vine_symbols_of_file filename in
  let () = D.dprintf "...done.%!" in
  let syms =  List.stable_sort (fun (s,_,_,_) (s',_,_,_) -> 
			   Int64.compare s s')  syms in
  (* let () = if true then 
    print_syms syms else () 
  in *)
  let (s,_,_,_) = Vine_util.list_last syms in 
  let last_addr = Libasmir.get_last_segment_address filename s in
    syms_to_funinfo syms last_addr 


let from_elf do_deend filename = 
  let () = D.dprintf "Processing elf...\n%!" in 
  let funinfos = get_elf_funinfos filename in 
(*   let () = D.dprintf "Getting symbols%!" in *)
(*   let syms = Asmir.vine_symbols_of_file filename in *)
(*   let () = D.dprintf "...done.%!" in *)
(*   let syms =  List.stable_sort (fun (s,_,_,_) (s',_,_,_) ->  *)
(* 			   Int64.compare s s')  syms in *)
(*   let () = if true then  *)
(*     print_syms syms else ()  *)
(*   in  *)
(*   let (s,_,_,_) = Vine_util.list_last syms in  *)
(*   let last_addr = Libasmir.get_last_segment_address filename s in *)
(*   let funinfos = syms_to_funinfo syms last_addr in   *)
  let () = D.dprintf "Populating functions%!" in
  let g = Asmir.gamma_create Asmir.x86_mem  Asmir.x86_regs in
  let instmap = Libasmir.filename_to_instmap filename in 
  let (fsl,funinfos) = populate_functions g funinfos instmap in 
  let fdecls = mk_fun_decls funinfos in 
  let fsl = (Asmir.x86_eflags_helpers ()) @ fsl in 
  let dl = (Asmir.x86_mem :: Asmir.x86_regs) in 
  let prog = (dl,List.append fdecls fsl) in 
  let prog = 
    if do_deend then 
      Vine_memory2array.coerce_prog prog
    else
      prog
  in
  let (dl,sl) = Vine_alphavary.descope_program prog in 
  let prog = (dl,sl) in 
    (prog, funinfos)




let ida_to_funinfos filename fileid = 
  let db = Sqlite3.db_open filename in 
  let ifuncs = get_idafuncs_where db 
    (Printf.sprintf "file_id = %d" fileid) in 
  let finfos = List.map 
    (fun (id,file_id,name,tsig,flags,saddr,eaddr) ->
       {
	 name = name;
	 start_address = saddr;
	 end_address = Int64.sub eaddr 1L;
	 (* FIXME: Why doesn't this call heuristic_test? *)
	 is_extern = (try String.sub name 0 6 = "__imp_" with _ -> false);
	 tails = get_ftails_for_function db id
       };) ifuncs in
  let () = ignore(Sqlite3.db_close db) in 
    finfos
;;

let ida_address_range_to_ir filename fileid sa ea =
  let g = Asmir.gamma_create Asmir.x86_mem Asmir.x86_regs in 
  let instmap = Libasmir.sqlite3_fileid_to_instmap filename fileid in
  let dl = Asmir.x86_mem :: Asmir.x86_regs in 
  let alst = Asmir.instmap_translate_address_range g instmap
    sa ea in 
  let sl = List.fold_left 
    (fun acc (_, (sl:Vine.stmt list)) -> 
	 List.append acc sl
    ) [] alst 
  in
    (dl,sl)

let elf_address_range_to_ir filename sa ea =
  let g = Asmir.gamma_create Asmir.x86_mem Asmir.x86_regs in 
  let instmap = Libasmir.filename_to_instmap filename in 
  let dl = Asmir.x86_mem :: Asmir.x86_regs in 
  let alst = Asmir.instmap_translate_address_range g instmap
    sa ea in 
  let sl = List.fold_left 
    (fun acc (_, (sl:Vine.stmt list)) -> 
	 List.append acc sl
    ) [] alst 
  in
    (dl,sl)


let from_ida do_deend filename fileid = 
  let () = D.dprintf "Processing IDA DB...\n%!" in 
  let finfos = ida_to_funinfos filename fileid in 
  let g = Asmir.gamma_create Asmir.x86_mem  Asmir.x86_regs in
  let instmap = Libasmir.sqlite3_fileid_to_instmap filename fileid in
  let (fsl,finfos) = populate_functions g finfos instmap in 
  let fdecls = mk_fun_decls finfos in 
  let fsl = (Asmir.x86_eflags_helpers ()) @ fsl in 
  let dl = (Asmir.x86_mem :: Asmir.x86_regs) in 
  let prog = (dl,List.append fdecls fsl) in 
  let prog = 
    if do_deend then 
      Vine_memory2array.coerce_prog prog
    else
      prog
  in
  let (dl,sl) = Vine_alphavary.descope_program prog in 
  let prog = (dl,sl) in 
    (prog, finfos)
;;

let to_program do_deend =
  if !flag_is_elf then (
    from_elf do_deend !flag_elf_file
  ) else (
    if !flag_is_ida then (
      from_ida do_deend !flag_idadb_file !flag_idadb_fileid
    ) else (
      raise (Vine.VineError("Must supply either -elf or -ida"))
    )
  )

let address_range_to_ir sa ea =
  if !flag_is_elf then
    elf_address_range_to_ir !flag_elf_file sa ea
  else if !flag_is_ida then
    ida_address_range_to_ir !flag_idadb_file !flag_idadb_fileid sa ea
  else
    raise(Vine.VineError "address_range_to_ir: Must supply either -elf or -ida")

(** called every time we see a call to a non-function during
    call/return replacing. Could be used to keep track of how many
    calls to non-functions we see *)
let add_call_to_non_function stmt = 
  ()

(**
   @param prog - a program 
   @return fl with direct call-jmps replaced with Calls,
   and ret-jmps replaced with Rets
*)
let replace_calls_and_returns (dl, sl) funcs =
  let callreplacer s = 
    match s with
	Jmp(Name(l)) as j ->  (
	  let addr = label_to_addr l in 
	    try
	      (* the call needs to be to the start of a function *)
	      let finf = List.find (fun x -> x.start_address = addr) funcs 
	      in Call(None, Name(finf.name), [])
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
		  ( (*Printf.eprintf "Warning: call to non-function: %s\n"
		      (stmt_to_string s);*)
		    add_call_to_non_function j;
		    j)
	)
      | Jmp(e) -> 
	  (*Printf.eprintf "Warning: indirect call %s\n" 
	    (stmt_to_string s);*)
	  Call(None, e, [])

	  (* failwith (Printf.sprintf "Indirect call?: %s"
			       (stmt_to_string s)) *)
      | _ -> failwith "call not translated as jmp?"
  in
    (* replace returns with "return" in "replace_special_jumps" below *)
  let retreplacer s = Return(None)  in
    (* do the call/return replacements. *)
  let sl = List.map (fun x ->
    match x with
	Function(v,topt,args,false,Some(Block(dl,sl))) ->
	  let sl' = replace_special_jumps callreplacer retreplacer sl in 
	    Function(v,topt,args,false,Some(Block(dl,sl')))
      |Block(dl,sl) -> Block(dl, replace_special_jumps callreplacer
			       retreplacer sl) 
      | _ -> x
   ) sl in
  let sl = replace_special_jumps callreplacer retreplacer sl in 
    (dl,sl)

(*************************************************************************)
let eliminate_interprocedural_jumps (dl,sl) funinfos =
  D.wprintf "eliminate_interprocedural_jumps is broken and should probably be deprecated.";
  let do_one_stmt = function
      Function(v,topt,args,false,Some(Block(blkdl,blksl))) -> (
	let info = List.find (fun x -> x.name = v) funinfos in 
	let blksl = List.fold_left 
	  (fun acc s -> match s with
	       Jmp(Name(l)) -> (
		 try
		   let addr = label_to_addr l in 
		     if addr >= info.end_address || addr <
		       info.start_address then (
			 D.dprintf "Removing inter-procedural jump %s"
			   (stmt_to_string s);
			 acc
		       ) else
			 s::acc
		 with
		     _ -> s::acc
	       )
	     | _ -> s::acc
	  ) [] blksl in 
	let blksl = List.rev blksl in 
	  Function(v,topt,args,false,Some(Block(blkdl,blksl)))
      )
    | _ as s -> s
  in
  let sl = List.map (fun x -> 
		       try 
			 do_one_stmt x
		       with
			   Not_found -> x
		    ) sl in 
    (dl,sl)

let elf_function_to_ir_by_address filename = 
  let funinfos = get_elf_funinfos filename in 
    (fun addr -> let i = List.find (fun x -> x.start_address = addr) funinfos in
       (i, elf_address_range_to_ir filename i.start_address i.end_address) )

  
let ida_function_to_ir_by_address filename fileid = 
  let funinfos = ida_to_funinfos filename fileid in 
    (fun addr -> let i = List.find (fun x -> x.start_address = addr) funinfos in 
       (i, ida_address_range_to_ir filename fileid i.start_address i.end_address) )

			     
let function_to_ir_by_address () = 
  if !flag_is_elf then 
    elf_function_to_ir_by_address !flag_elf_file 
  else
    ida_function_to_ir_by_address !flag_idadb_file !flag_idadb_fileid


(** types of exectables supported *)
type exeType =  Elf of string | IdaDB of string * int 

(** common interface to executables. *)
class exe typ  =
object(self)

  val instmap = match typ with 
	Elf(filename) -> Libasmir.filename_to_instmap filename
      | IdaDB(filename,idx) -> Libasmir.sqlite3_fileid_to_instmap filename idx

  val funinfos = match typ with
      Elf(filename) -> get_elf_funinfos filename
    | IdaDB(filename,idx) -> ida_to_funinfos filename idx


  (* number of translated x86 instructions so far *)
  val mutable x86trans = 0L;

  (* typing context for translation *)
  val gamma = Asmir.gamma_create Asmir.x86_mem Asmir.x86_regs

  method get_funinfos = funinfos 

  method tr_address a = self#tr_range a a



  method tr_range s e = 
    let lst = Asmir.instmap_translate_address_range gamma instmap s e  in
      List.fold_left (fun acc (_,sl) -> 
			x86trans <- Int64.add x86trans 1L;
			List.append acc sl) [] lst

  method get_funinfo_by_name (name:string) = 
    List.find (fun x -> x.name = name) funinfos

  method get_funinfo_by_start_address addr = 
    List.find (fun x -> x.start_address = addr) funinfos

  method get_funinfo_by_any_address addr =
    List.find (fun x -> x.start_address <= addr && x.end_address >= addr) 
      funinfos 

  method tr_function =
    populate_function gamma instmap

  method base_program () =     
    if Libasmir.get_use_eflags_thunks () then
      (Asmir.x86_mem :: Asmir.x86_regs, Asmir.x86_eflags_helpers ())
    else
      (Asmir.x86_mem :: Asmir.x86_regs, [])

  method globals = Asmir.x86_mem :: Asmir.x86_regs

  method thunks () = 
    if Libasmir.get_use_eflags_thunks () then
      Asmir.x86_eflags_helpers () 
    else []

  method x86translated = x86trans

  method reset_translation_count () = x86trans <- 0L;
end

let get_cmdline_exe () = 
    if !flag_is_elf then 
      new exe (Elf(!flag_elf_file))
    else if !flag_is_ida then
      new exe (IdaDB(!flag_idadb_file, !flag_idadb_fileid))
    else
      raise (Invalid_argument ("unknown command line file type"))



(*pm*)
let ida_to_funinfos_flat filename fileid = 
  let db = Sqlite3.db_open filename in 
  let ifuncs = get_idafuncs_where db 
    (Printf.sprintf "file_id = %d" fileid) in
		 
  let (id,file_id,name,tsig,flags,saddr,eaddr) = List.hd ifuncs in
  
	let finfo= 
			{
			 name = "flat_start";
			 start_address = saddr;
			 end_address = Int64.sub eaddr 1L;
			 (* FIXME: Why doesn't this call heuristic_test? *)
			 is_extern = (try String.sub name 0 6 = "__imp_" with _ -> false);
			 tails = get_ftails_for_function db id
       }
	in
	
	let length = List.length ifuncs in	
	let (id,file_id,name,tsig,flags,saddr,eaddr) = List.nth ifuncs (length-1) in
	
	let finfo= 
			{
			 name = "flat_start";
			 start_address = finfo.start_address;
			 end_address = Int64.sub eaddr 1L;
			 is_extern = false;
			 tails = finfo.tails
       }
	in
	
	let ()= Printf.printf "pm: finfo.startaddr=%Ld, finfo.endaddr=%Ld\n"
						finfo.start_address
						finfo.end_address
	in
	
	let finfos=[finfo] in
  let () = ignore(Sqlite3.db_close db) in 
	let ()=Printf.printf "quit ida_to_fun\n" in 
    finfos
;;


let from_ida_flat do_deend filename fileid = 
  let () = D.dprintf "Processing IDA DB...\n%!" in 
  let finfos = ida_to_funinfos_flat filename fileid in 
  let g = Asmir.gamma_create Asmir.x86_mem  Asmir.x86_regs in
  let instmap = Libasmir.sqlite3_fileid_to_instmap filename fileid in
  (*let (fsl,finfos) = populate_functions g finfos instmap in*)
	let (fsl,_) = populate_functions g finfos instmap in 
  let fdecls = mk_fun_decls finfos in 
  let fsl = (Asmir.x86_eflags_helpers ()) @ fsl in 
  let dl = (Asmir.x86_mem :: Asmir.x86_regs) in 
  let prog = (dl,List.append fdecls fsl) in 
  let prog = 
    if do_deend then 
      Vine_memory2array.coerce_prog prog
    else
      prog
  in
  let (dl,sl) = Vine_alphavary.descope_program prog in 
  let prog = (dl,sl) in 
    (prog, finfos)
;;

(*pm end*)