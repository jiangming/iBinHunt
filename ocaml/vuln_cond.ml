(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
open Vine;;
open Printf;;
module Ida = Vine_idadisasm ;;
module List = ExtList.List;;

let label_is_addr l = 
  try
    let _ = label_to_addr l in
    true
  with
    VineError _ -> 
      false

module AddrSet = Set.Make(Int64);;

(** 
    Remove concrete initializers added by taintlog_to_trace.
    XXX makes assumptions about what initializer block looks like.
    @param prog an ir program
    @return prog with initialization blocks removed
*)
let remove_inits prog =
  let vis =
object (self)
  inherit nop_vine_visitor
  method visit_stmt s =
    match s with
    | Block(_, Comment("Initializers")::_) ->
        ChangeTo(Comment("Deleted Initializers"))
    | _ ->
        DoChildren
end
  in
  let (dl,sl) = prog in
  let sl = 
    List.map
      (stmt_accept vis)
      sl
  in
  (dl, sl)

(**
   Identify EIP where tainted data was misused.
   Assumes this is last instruction in execution trace,
   and that it is a tainted return address.
   Also identify instruction address in the program that
   overwrote the return address, or called an external
   function that overwrote the return address.
   XXX will not work if return address was overwritten by
   the kernel, since the overwrite won't appear in the execution
   trace.
   @param tracefile an execution tracefile from TEMU
   @param addrset set of addresses within the analyzed program.
*)
let identify_vuln tracefile addrset =
  (* build basic trace *)
  let prog, _ =
    Exectrace.taintlog_to_ir_trace tracefile [] in

  (* rewrite labels so all jmps are forwards *)
  let prog = Exectrace.rewrite_labels prog in

  (* rewrite all memory indexes to be concrete *)
  let prog = Exectrace.trace_to_conc_idx prog in

  (* remove initializers (they confuse following analysis) *)
  let prog = remove_inits prog in

  (* flatten and reverse sl. 
     going to do some searches from end of trace *)
  let (dl', sl) = Vine_alphavary.descope_program prog in 
  let sl = List.rev sl in

  (* find location of last RA. 
     assume that last expression reading from
     memory is fetching the RA. *)
  let ra_mov =
    List.find
      (fun s ->
         match s with
         | Move(lhs, rhs) ->
             let vars = freerefs_exp rhs in
             let mems = onlymems vars in
             if mems = [] then
               false
             else
               true
         | _ -> false)
      sl
  in
  let ra_mems = 
    match ra_mov with Move(_,rhs) ->
      let vars = freerefs_exp rhs in
      onlymems vars
  in

  (* find address of last instruction in trace.
     this is where misuse happened, since TEMU stops tracing
     when a violation is detected. *)
  let misuse_lbl =
    List.find
      (fun s -> 
         match s with
         | Label(l) when (label_is_addr l) ->
             true
         | _ -> false)
      sl
  in
  let misuse_addr =
    match misuse_lbl with Label(l) -> label_to_addr l
  in
  
  (* find where the RA was overwritten. 
     assume that the last write to that location was the
     illegitimate overwrite. should hold for RA's *)
  let overwrite_lbl =
    let found_overwrite = ref false in
    let found_actual_ovewrite_lbl = ref false in
    List.find
      (fun s ->
         match s with
         | Move(lhs, _) ->
             (if List.exists (fun v -> v = lhs) ra_mems then
                found_overwrite := true);
             false
         | Label(l) when !found_overwrite && (label_is_addr l) ->
             if (AddrSet.mem (label_to_addr l) addrset) then
               true
             else (
               if (not !found_actual_ovewrite_lbl) then (
                 printf "Overwrite occured at %s l\n" l;
                 found_actual_ovewrite_lbl := true);
               false
             )
         | _ -> false
      )
      sl
  in
  let overwrite_addr =
    match overwrite_lbl with Label(l) -> label_to_addr l
  in
  printf "overwrite addr: %Lx misuse addr: %Lx\n" 
    overwrite_addr misuse_addr;

  (misuse_addr, overwrite_addr)

(**
   Instrument a function to save location of its return address
   when called, and delete on return.
   @param sl a list of functions
   @param vuln_buf_fn function to instrument
   @return fl with new instrumentation functions,
   and vuln_buf_fn instrumented to call them.
*)
let add_ra_tracking sl vuln_buf_fn =
  let rewrite_vuln_fn_sl sl = 
    let vis =
object (self)
  inherit nop_vine_visitor
  method visit_stmt s =
    match s with
    | Return _ ->
        ChangeTo(
          Block([],
                [Call(None, "pop_ra_loc", []);
                 s;]))
    | _ ->
        DoChildren
end
    in
    (* save ra on entry. XXX is first statement canonical fn start? *)
    let sl = Call(None, "push_ra_loc", []) :: sl in

    (* pop saved ra when function returns *)
    let sl = List.map (stmt_accept vis) sl in
    sl
  in

  (* find vuln fn and add calls to tracking fns *)
  let sl = 
    List.map
      (function 
         | Function(v, t, d, e, Some(Block(dl, sl))) 
             when v = vuln_buf_fn ->
             let sl = rewrite_vuln_fn_sl sl in
             Function(vuln_buf_fn, t, d, e, Some(Block(dl, sl)))
         | x -> x
      )
      sl
  in

  (* tracking fn defs *)
  let push_ra_loc = 
    let dl = [] in
    let sl = 
      [
        (* ra_locs[num_ra_locs] = R_ESP *)
        Move(Mem("ra_locs", Array(REG_32, REG_32), 
                 Lval(Temp("num_ra_locs", REG_32))),
             Lval(Temp("R_ESP", REG_32)));

        (* num_ra_locs++ *)
        Move(Temp("num_ra_locs", REG_32), 
             BinOp(PLUS, 
                   Lval(Temp("num_ra_locs", REG_32)),
                   Constant(REG_32, Int(1L))));
      ] in
    Function("push_ra_loc", None, [], false, Some(Block(dl, sl)))
  in
  let pop_ra_loc =
    let dl = [] in
    let sl = 
      [
        (* num_ra_locs-- *)
        Move(Temp("num_ra_locs", REG_32), 
             BinOp(MINUS, 
                   Lval(Temp("num_ra_locs", REG_32)),
                   Constant(REG_32, Int(1L))));
      ]
    in
    Function("pop_ra_loc", None, [], false, Some(Block(dl, sl)))
  in
  let push_ra_loc_decl = 
    Function("push_ra_loc", None, [], false, None) in
  let pop_ra_loc_decl = 
    Function("pop_ra_loc", None, [], false, None) in
  push_ra_loc_decl::pop_ra_loc_decl::push_ra_loc::pop_ra_loc::sl

(** 
    Add instrumentation after function call at
    overwrite_addr to check whether a saved RA
    was overwritten, and
    if so, call function "exploited".
    @param sl function list
    @param overwrite_addr address containing
    a call to a function that may overwrite a
    saved return address.
    @return function list with an additional
    instrumentation function, and instrumentation
    added to call that function.
*)
let add_ra_check sl overwrite_addr =
  (* add call to check fn *)
  let vis = 
object(self)
  inherit nop_vine_visitor
  val mutable found_lbl = false
  method visit_stmt s =
    match s with
    | Label l when
        (label_is_addr l) && (label_to_addr l) = overwrite_addr
        ->
        found_lbl <- true;
          DoChildren
    | Call _ when found_lbl ->
        found_lbl <- false;
        ChangeTo(
          Block([],
                [s;
                 Call(None, "vuln_cond_check", []);]))
    | _ ->
        DoChildren
end
  in
  let sl = List.map (stmt_accept vis) sl in

  let vuln_cond_check =
    let dl = [("i", REG_32); ("loc", REG_32); ("exploitedvar", REG_1)] in
    let sl = 
      [
        (* i = 0 *)
        Move(Temp("i", REG_32), Constant(REG_32, Int(0L)));
        (* begin: *)
        Label("vcc_begin");
        (*   if (i < num_ra_locs) then goto next else goto done *)
        CJmp(BinOp(LT, 
                   Lval(Temp("i", REG_32)), 
                   Lval(Temp("num_ra_locs", REG_32))),
             Name("vcc_next"),
             Name("vcc_done"));
        (* next: *)
        Label("vcc_next");
        (*   loc = ra_locs[i] *)
        Move(Temp("loc", REG_32), 
             Lval(Mem("ra_locs", 
                      Array(REG_32, REG_32), 
                      Lval(Temp("i", REG_32)))));
        (*   i++ *)
        Move(Temp("i", REG_32),
             BinOp(PLUS, 
                   Lval(Temp("i", REG_32)), 
                   Constant(REG_32, Int(1L))));
        (*   exploitedvar = write_start <= loc <= write_end *)
        Move(Temp("exploitedvar", REG_1),
             BinOp(BITAND,
                   BinOp(LE,
                         Lval(Temp("write_start", REG_32)),
                         Lval(Temp("loc", REG_32))),
                   BinOp(LE,
                         Lval(Temp("loc", REG_32)),
                         Lval(Temp("write_end", REG_32)))));
        (* if (exploitedvar) then goto exploited else goto begin *)
        CJmp(Lval(Temp("exploitedvar", REG_1)),
             Name("vcc_exploited"),
             Name("vcc_begin"));
        (* exploited: *)
        Label("vcc_exploited");
        Call(None, "exploited", []);
        (* done: *)
        Label("vcc_done");
        (*   return *)
        Return(None);
      ]
    in
    Function("vuln_cond_check", None, [], false, Some(Block(dl, sl)))
  in
  let vuln_cond_check_decl =
    Function("vuln_cond_check", None, [], false, None) in
  vuln_cond_check_decl :: vuln_cond_check :: sl

(**
   Add special "exploited" function, to be called
   when an exploit is detected.
   @param sl function list
   @return sl with "exploited" function added
*)
let add_exploited_fn sl =
  let exploited =
    let dl = [] in
    let sl =
      [
        (* exploitedvar = 1 (global) *)
        Move(Temp("exploitedvar", REG_1), Constant(REG_1, Int(1L)));
        (*        Label("exploited"); *)
        Label(addr_to_label 0L); (* for chop end *)
        Special("exploited"); (* TM should return here *)
(*        Jmp(Lval(Temp("R_EAX", REG_32))); (* force no successors in chop *)*)
        (*   return *)
        Return(None);
      ]
    in
    Function("exploited", None, [], false, Some(Block(dl, sl)))
  in
  let exploited_decl = 
    Function("exploited", None, [], false, None) in
  exploited_decl :: exploited :: sl


(**
   Find the set of instruction addresses contained in
   the given stmt list.
   @param sl a statement list.
   @return set of instruction addresses in sl
*)
let sl_to_addrset sl =
  let addrset = ref AddrSet.empty in

  let vis =
object (self)
  inherit nop_vine_visitor
  method visit_stmt s =
    match s with
    | Label l when (label_is_addr l) ->
(*        printf "Adding 0x%Lx\n%!" (label_to_addr l);*)
        addrset := AddrSet.add (label_to_addr l) !addrset;
        DoChildren
    | _ ->
        DoChildren
end
  in
  List.iter (fun s -> let _ = stmt_accept vis s in ()) sl;
  !addrset

let flatten_fns fl =
  (* flatten each function *)
  let fl = 
    List.map
      (fun x ->
         match x with
	 | Function(v,topt,args,false,Some(Block(dl,sl))) ->
	     let dl', sl' = Vine_alphavary.descope_program (dl,sl) in
             let dl = List.rev_append dl dl' in
	     Function(v,topt,args,false,Some(Block(dl,sl')))
         | Function(v,_,_,true, None) -> x
         | _ -> x
      ) 
      fl
  in
  fl

(**
   @param fl a list of flattened functions
   @param tracefile execution trace file, where last instruction
   executed is a "ret" using an overwritten return address
   @param fninfo function info as returned from read_function_file
*)
let add_stack_vc fl tracefile fninfo =
  let (misuse_addr, overwrite_addr) = 
    identify_vuln tracefile (sl_to_addrset fl) in
  (*let overwrite_addr = 0x804a68eL in*) (* hack for  testing ghttpd *)
  (* let overwrite_addr = 0x804978CL in *) (* hack for  testing passlogd *)
  (*   let overwrite_addr = 0x8049AF7L in  (\* hack for  testing pptpd *\) *)
(*   let () = Printf.fprintf stderr "0x%08Lx 0x%08Lx\n" misuse_addr overwrite_addr *)
(*   in *)
  let vuln_buf_fn_o = Ida.addr_to_function misuse_addr fninfo in
  let vuln_buf_fn = 
    match vuln_buf_fn_o with Some(x) -> x | None -> raise Not_found in
  let fl = add_ra_tracking fl vuln_buf_fn.Ida.name in
  let fl = add_ra_check fl overwrite_addr in
  let fl = add_exploited_fn fl in
  (* re-flatten each function *)
  let fl = flatten_fns fl in
  fl
