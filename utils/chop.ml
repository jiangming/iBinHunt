(*
*  chop.ml. Computes a rough chop of a program, given start and end.
*  Currently only supports intra-procedural chopping
*)


open Vine;;
open Vine_util;;
open Vine_idadb;;
open Vine_cfg;;
open Utils_common;;

module D = Debug.Make(struct let name=Sys.argv.(0) and default=`Debug end)
open D;;

type args = {
  mutable outfile : out_channel;
  mutable outdot : string;
  mutable startlbl : string;
  mutable endlbl : string;
  mutable opts : string list;
  mutable no_chop_backedge : bool;
}

let version = "$Id$";;
let flag_dostats = ref false;;
let starttime = ref 0.0;;
let endtime = ref 0.0;;
let num_chop_stmts = ref 0L;;

let printstats () = 
  if !flag_dostats then (
    Printf.printf "Elapsed time: %f\n%!" (!endtime -. !starttime);
    Printf.printf "Number of chop stmts in chop: %Lu\n%!" !num_chop_stmts;
  )
  else () 
;;

let cfg_mem_id cfg n = 
  try
    (ignore(cfg#find n); true)
  with
      Not_found -> false
;;


let remove_last_jump cfg n =
  let stmts,last = list_partition_last (cfg#get_info n) in
    match last with
	Jmp _ -> cfg#set_info n stmts
      | CJmp _ -> cfg#set_info n stmts 
      | _ -> ()
;;

(* give a node n with two successors, we want it so it only goes to
   successor t. If t is not BB_Indirect, then n ends in either
   CJmp(c,t,some other node) or CJmp(c,some other node t). Change the
   former into Assert(c) and the latter into Assert(not c). 

   If t is BB_Indirect, then see if only one of the possible jump
   targets is indirect. If so, then fix up the statements in n to only
   go to the indirect. Else we have a CJmp with both targets being
   indirect, and we don't know what to do. 
*)
let replace_cjmp_with_assert cfg n t = 
  let sstmts,slast = list_partition_last (cfg#get_info n) in 
    if (cfg#get_id t) <> BB_Indirect then (
      let tlbl = 
	List.find (function Label _ -> true | _ -> false) (cfg#get_info t) 
      in 
	match tlbl,slast with
	    Label(l1), CJmp(c,Name(l2),_) when l1 = l2 -> 
	      cfg#set_info n (List.append sstmts [Assert(c)])
	  | Label(l1), CJmp(c,_,Name(l2)) when l1 = l2 ->
	      cfg#set_info n (List.append sstmts [Assert(UnOp(NOT,c))])
	  | _, CJmp _ -> failwith "neither cjmp label matched t's label"
	  | _,_ -> failwith "Expected cjmp"
    ) else (
      match slast with
	  CJmp(c,Name _, Name _) -> 
	    failwith "Indirect jump target, but both cjmp targets direct"
	| CJmp(c,_,Name _ ) -> 
	    cfg#set_info n (List.append sstmts [Assert(c)])
	| CJmp(c,Name _,_) ->
	    cfg#set_info n (List.append sstmts [Assert(UnOp(NOT,c))])
	| CJmp _ -> 
	    failwith "Which indirect branch corresponds to t?"
	| _ -> failwith "expected cjmp"
    )
;;

(** for each edge (a,b) in oldcfg, add the edge (a,b) in newcfg if
    b exists in newcfg (we are only called on nodes where a exists in
    newcfg). If b does not exist in newcfg, then we have to fix up the
    statements in a *)
let scc_add_newedges newcfg oldcfg n = 
  let ensure_edge dst = (
    if not(newcfg#has_edge n dst) then newcfg#add_edge n dst 
  ) in
  let () = 
    if cfg_mem_id newcfg BB_Indirect then () else
      newcfg#add_bb BB_Indirect [Comment("indirect jmp target")]
  in
  let nid = newcfg#get_id n in 
  let oldsucc = oldcfg#succ (oldcfg#find nid) in
    match oldsucc with
	[] -> () 
      | [x] -> (
	  let xid = oldcfg#get_id x in 
	    try
	      ensure_edge (newcfg#find xid)
	    with
		Not_found -> 
		  remove_last_jump newcfg n 
	)
      | [x;y] -> (
	  let (xid,yid) = oldcfg#get_id x, oldcfg#get_id y in 
	    match cfg_mem_id newcfg xid, cfg_mem_id newcfg yid with
		true,true -> (
		  ensure_edge (newcfg#find xid);
		  ensure_edge (newcfg#find yid)
		)
	      | true,false -> (
		  replace_cjmp_with_assert newcfg n (newcfg#find xid);
		  ensure_edge (newcfg#find xid)
		)
	      | false,true -> (
		  replace_cjmp_with_assert newcfg n (newcfg#find yid);
		  ensure_edge (newcfg#find yid)
		)
	      | false,false -> (
		  remove_last_jump newcfg n
		)
	)
      | _ -> failwith "Unexpected. CFG has node > 2."
;;


(* split a list of statements with stmt s into hd,s,tl *)
let split_block_at_stmt stmts stmt : (Vine.stmt list * Vine.stmt *
					  Vine.stmt list) = 
  let hd,tl,found = List.fold_left 
    (fun (hd,tl,found) s ->
       if found then (hd,s::tl,found) else (
	 if s = stmt then (hd,tl,true) else (s::hd,tl,found)
       )
    ) ([],[],false) stmts in
    (* make sure the label was really found *)
    assert(found); 
    (List.rev hd, stmt, List.rev tl)
;;

(* adds a canonical entry node.  Let s be the chop start with
   statement list hd@startlbl@tl. If s has no predecessors, we set s's
   statment list to be startlbl::tl, and add the edge (entry,s). 

   If s has predecessors, then there is a path from t -> s at this
   stage.  We split s into two blocks s_0 for those statements before
   startlbl, and leave s for the label and the remaining
   statements. We move all the incoming edges in s to s_0 and add the
   edge (s_0, s). We then add the edge (entry,s) to the graph.
*)
let make_canonical_entry cfg s startlbl  = 
  let entry =  (
    try cfg#find BB_Entry  with 
	Not_found -> cfg#create_bb BB_Entry [Comment("Entry")] )
  in
  let preds = cfg#pred s in 
  let hd,lbl,tl = split_block_at_stmt (cfg#get_info s) (Label(startlbl)) in 
  let () = cfg#set_info s (lbl::tl) in 
    (match preds with
	 [] -> ()
       | _ -> 
	   let () = pwarn ("Chop start is in a loop."^
			     " Adding edge (start,s) where s is the block"^
			     " containing startlbl (but may not begin"^
			     " with startlbl).\n"^
			     " This may not be what you want") in 
	   let newlab = newlab "chop_start" in 
	   let jmp = Jmp(Name(newlab)) in 
	   let s_0 = cfg#create_bb (cfg#newid) (List.append hd [jmp]) in 
	   let () = List.iter 
	     (fun p -> cfg#remove_edge p s; cfg#add_edge p s_0) preds in 
	     cfg#add_edge s_0 s
    );
    cfg#add_edge entry s 
;;

(* adds a canonical exit node.  Let t be the terminal node with
   statements hd@[endlbl]@tl. If t is terminal, then we set
   t's statements to be hd@[endlbl], and add the edge [t,exit].

   If t is not terminal, that means there is a path t->s.  We create a
   new node t_0, and set t's statement list to be
   hd@[endlbl]@[CJmp(true,t_0, exit)] essentially. We then add the
   remaining tl statements to t_0, and move the successors of old t to
   t_0. *)
let make_canonical_exit cfg t endlbl = 
  let exitbb,exitlbl = (
    try 
      let exitbb = cfg#find BB_Exit  in 
      let exitstmts = cfg#get_info exitbb in 
	match List.hd (List.rev exitstmts) with
	    Label(l) -> exitbb,l
	  | _ -> 
	      let lab = newlab "exit_label" in
	      let () =  cfg#set_info exitbb (Label(lab)::exitstmts) in 
		exitbb,lab
    with
	Not_found -> (
	  let newlab = newlab "exit_label" in 
	  let bb = cfg#create_bb BB_Exit [Label(newlab);Comment("Exit")] in 
	    bb,newlab
	)
  )
  in
  let succ = cfg#succ t in 
  let hd,lbl,tl = split_block_at_stmt (cfg#get_info t) (Label(endlbl)) in 
    ( match succ with
	  [] -> cfg#set_info t (List.append hd [lbl])
	| _ -> 
	    let hd,lbl,tl = split_block_at_stmt (cfg#get_info t) (Label(endlbl))
	    in
	    let t_0 = cfg#create_bb (cfg#newid) (lbl::tl) in
	    let cjmp = CJmp(exp_true,Name(endlbl),Name(exitlbl)) in  
	    let tstmts = List.append hd [cjmp] in 
	      cfg#set_info t tstmts;
	      List.iter (fun bb -> cfg#remove_edge t bb; 
			   cfg#add_edge t_0 bb) succ;
	      cfg#add_edge t t_0
    );
    cfg#add_edge t exitbb


(* calculate the CFG SCC chop *)
let cfg_scc cfg startlbl endlbl  = 
  let s,t = (cfg#find_label startlbl, cfg#find_label endlbl) in 
  let remove_backedge = 
    if cfg#has_edge t s then 
      fun () -> () 
    else (
      cfg#add_edge t s;
      fun () -> cfg#remove_edge t s 
    ) 
  in
  let (_,scc) = Component.scc cfg in
    (* make sure we really have a cycle *)
  let () = assert(scc (cfg#get_id s) = scc (cfg#get_id t)) in 
  let group = scc (cfg#get_id s) in
  let newcfg = empty_cfg 8 cfg#get_iter_labels_function cfg#vardecls in
  let addifgroup v =
    if scc (cfg#get_id v) = group then (
      newcfg#add_bb (cfg#get_id v) (cfg#get_info v)
    ) else ()
  in
  let () = cfg#iter_bb addifgroup in
  let () = remove_backedge ()  in 
  let () = newcfg#iter_bb (fun bb -> 
	try scc_add_newedges newcfg cfg bb
	with Not_found -> () (* newcfg adds some default nodes that may not
				exist in oldcfg, like BB_INDIRECT *)
	) in
  let s = newcfg#find_label startlbl in 
  let t = newcfg#find_label endlbl in 
    make_canonical_entry newcfg s startlbl;
    make_canonical_exit newcfg t endlbl;
    remove_unreachable newcfg;
    newcfg    
;;    

(* function to ensure there is no chop backedge. Let s be the node
   with startlbl, and t be the node with endlbl.  We remove all
   statements before startlbl in s. By adding edge (start,s), we then
   know that there is no backedge to s.  We remove all statements
   after endlbl in t.  We then add an edge (t,exit). There can be 
   no cycle from s to t, and we know that statements inside the block
   do not need fixing since t now ends in a label, thus cannot be a
   cjmp or jmp. 
*)
let remove_chop_backedge cfg startlbl endlbl = 
  let s,t = cfg#find_label startlbl, cfg#find_label endlbl in 
  let shd,slbl,stl = split_block_at_stmt (cfg#get_info s) (Label(startlbl)) in 
  let thd,tlbl,ttl = split_block_at_stmt (cfg#get_info t) (Label(endlbl)) in 
  let entrybb = cfg#find BB_Entry in 
  let exitbb = cfg#find BB_Exit in 
    cfg#set_info s (slbl::stl);
    cfg#set_info t (List.append thd [tlbl]);
    List.iter (fun bb -> cfg#remove_edge entrybb bb) (cfg#succ entrybb);
    List.iter (fun bb -> cfg#remove_edge bb exitbb) (cfg#pred exitbb);
    cfg#add_edge entrybb s;
    cfg#add_edge t exitbb
;;
    

let doit args (dl,sl) =
  let cfg = prog_to_cfg (dl,sl) in 
  let () = if args.no_chop_backedge then 
    remove_chop_backedge cfg args.startlbl args.endlbl 
  in
  let cfg = cfg_scc cfg args.startlbl args.endlbl in 
  let cfg = optimize_cfg cfg dl args.opts in 
  let () = if args.outdot <> "" then  
    Vine_graphviz.VineStmtsDot.output_graph (open_out args.outdot) cfg
  in
  let () = Vine_cfg.remove_unreachable cfg in 
  let (dl,sl) = Vine_cfg.normal_cfg_to_prog cfg in
(*  let (dl,sl) = use_only_one_mem (dl,sl) in  *)
  let () = num_chop_stmts := if !flag_dostats then count_stmts sl else 0L in 
  let ft = Format.formatter_of_out_channel (args.outfile) in 
  let pp = new Vine_pp.pp ft in 
    pp#format_program (dl,sl)
;;


let check_program args (dl,sl) = 
  let (dl,sl) = 
    match sl with
	[Function(_,_,_,_,Some(Block(dl',sl')))] -> (List.append dl dl', sl')
      | _ -> 
	  if List.exists (function Function _ -> true | _ -> false) sl
	  then  (
	    failwith "Multiple functions not currently supported"
	  ) else (dl,sl) 
  in
  let foundstart,foundend = (ref false,ref false) in 
    List.iter 
      (function 
	   Label(l) when l = args.startlbl -> foundstart := true
	 | Label(l) when l = args.endlbl -> foundend := true
	 | _ -> ()) sl;
    if not !foundstart then 
      failwith "Could not find specified start label";
    if not !foundend then
      failwith "Could not find specified end label";
    (dl,sl)
;;	    

let usage = "chop [options]*\n" in 
let infile = ref "" in 
let infile_set = ref false in 
let args = {outfile = stdout;
	    outdot = "";
	    startlbl = "";
	    endlbl = "";
	    opts = [];
	    no_chop_backedge = false;
	   }
in
let arg_name s = 
  infile := s; 
  infile_set := true 
in
let check_args () = 
  if not !infile_set then (
    Printf.eprintf "Must supply input file\n%!";
    exit(-1)
  ) else ();
  if args.startlbl = "" then  (
    Printf.eprintf "Must supply start of chop\n%!";
    exit(-1)
  ) else ();
  if args.endlbl = "" then  (
    Printf.eprintf "Must supply start of chop\n%!";
    exit(-1)
  ) else ();
in
let print_version () = Printf.printf "Chop version %s\n%!" version in
let main argc argv = 
  let speclist = [
    ("-start",
     Arg.String(fun s -> args.startlbl <- s),
     "<label> sets start of chop to <label>"
    );
    ("-end",
     Arg.String(fun s -> args.endlbl <- s),
     "<label> sets end of chop to <label>"
    );
    ("-o",
     Arg.String (fun x -> args.outfile <- open_out x),
     "<file> sets output file to <file> (default is stdout)"
    );
    ("-dot",
     Arg.String(fun s -> args.outdot <- s),
     "<file> output dot to <file>"
    );
    ("-version",
     Arg.Unit (fun () -> print_version (); exit(0)),
     "print version and exit"
    );
    ("-stats",
     Arg.Set (flag_dostats),
     "print statistics"
    );
    ("no_chop_backedge",
     Arg.Unit (fun () -> args.no_chop_backedge <- true),
     "remove backedge from chop start to end"
    );
  ] @ opts_speclist in 
  let () = Arg.parse speclist arg_name usage in 
  let () = args.opts <- !opt_flags in 
  let () = check_args () in
  let (dl,sl) = Vine_parser.parse_file !infile in 
    starttime := Unix.gettimeofday ();
    doit args (check_program args (dl,sl));
    endtime := Unix.gettimeofday ();
    printstats ()
in
  main (Array.length Sys.argv) Sys.argv;;
