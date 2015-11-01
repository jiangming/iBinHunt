(*
*  common_utils.ml
*  Common things in the command line
*)
open Vine_dataflow;;
open Vine_cfg;;
open Vine;;
open ExtList.List;;
open Vine_util;;

module D = Debug.Make(struct let name = "utils_common" and default=`Debug end);;
open D;;

let opt_flags = ref [];;

let opts_speclist = [
    ("-Ogvn", 
     Arg.Unit (fun () -> opt_flags :=  "gvn" :: !opt_flags),
     " perform global value numbering optimization"
    );
    ("-Odc",
     Arg.Unit (fun () -> opt_flags := "deadcode" :: !opt_flags),
     " perform dead code elimination"
    );
    ("-Oc",
     Arg.Unit (fun () -> opt_flags := "constprop" :: !opt_flags),
     " perform constant propoagation and folding"
    );
    ("-O",
     Arg.Unit (fun () -> opt_flags := "default" :: !opt_flags),
     " perform default optimizations, which may include deadcode, gvn, etc."
    );
];;

let optimize_cfg cfg globals  optlst =
  match optlst with [] -> cfg
    | _ -> (
	let () = Vine_cfg.coalesce_bb cfg in 
	let ssacfg = Ssa.cfg2ssa cfg in 
	let rec doit  = function
	    [] -> ()
	  | "gvn"::ys ->  (
	      SsaDataflow.do_gvn ssacfg;
	      doit ys
	    )
	  | "deadcode"::ys -> (
	      ignore(SsaDataflow.do_dce ~globals:[] ssacfg);
	      doit ys
	    )
	  | "constprop"::ys -> (
	      ignore(SsaDataflow.constant_propagation_and_folding ssacfg
		       (fun x -> x));
	      doit ys
	    )
	  | "default"::ys -> (
	      ignore(SsaDataflow.simplify_graph ssacfg ~globals:[] (-1));
	      doit ys
	    )
	| _ -> (failwith "invalid optimization specified.")
	in
	  doit optlst;
	  let cfg = Ssa.to_vine ssacfg in 
	  let () = cfg#iter_bb 
	    (fun bb -> 
	       let stmts = cfg#get_info bb in
	       let stmts = Vine_opt.coalesce_stmts stmts 1 in 
		 cfg#set_info bb stmts
	    ) in
	    cfg
      )
;;


let mk_collect_restore mem dl = 
  let rec bytes_of_type (t:typ) : int64 = 
    match t with
	REG_1 -> 1L
      | REG_8 -> 1L
      | REG_16 -> 2L
      | REG_32 -> 4L
      | REG_64 -> 8L
      | TMem _ -> bytes_of_type Vine.addr_t
      | TAttr(t',_) -> bytes_of_type t'
      | _ -> failwith "unhandled type"
  in
  let collect,idx  = List.fold_left 
    (fun (stmts,cntr) var ->
       let i,s,t = var in 
       let mv = Move(Mem(mem, Constant(Int(REG_32,cntr)), t),Lval(Temp(var)))
       in
       let cntr = Int64.add cntr  (bytes_of_type t) in 
	 (mv::stmts,cntr)
    ) ([],0L) dl
  in
  let restore,_  = List.fold_left 
    (fun (stmts,cntr) ((i,s,t) as var) -> 
       let mv = Move(Temp(var), Lval(Mem(mem, Constant(Int(REG_32,cntr)), t))) 
       in
       let cntr = Int64.add cntr  (bytes_of_type t) in 
	 (mv::stmts,cntr)
    ) ([],0L) dl
  in collect,restore,idx
;;

let x86_globals_to_args ((_,_,memtyp) as mem) (glbldl,sl) = 
  let collect,restore,retidx = mk_collect_restore mem glbldl in 
  let funs,rest = partition (function Function(_,_,_,_,Some _) -> true 
			       | _ -> false) sl in
  let ret_mem = Return(Some(Lval(Temp(mem)))) in 
  let ret_val_mem t = Mem(mem,Constant(Int(addr_t, retidx)), t) in
  let rewrite_ret = function 
      None -> Block([], List.append collect [ret_mem])
      | Some(e) -> 
	  let t = Vine_typecheck.infer_type None e in 
	  let mv = Move(ret_val_mem t, e) in
	    Block([], collect @ [mv;ret_mem])
  in
  let rewrite_call ret e el = 
    let c = Call(Some(Temp(mem)), e, (Lval(Temp(mem)))::el) in 
      match ret with
	  None ->
	    Block([], ( List.rev (c::collect)) @ restore)
	| Some(Mem((_,_,t),_,_) as tmp) 
	| Some(Temp(_,_,t) as tmp) ->
	    let mv = Move(tmp, Lval(ret_val_mem t)) in 
	      Block([], ( List.rev (c::collect)) @ (mv::restore))
  in
  let vis = 
object(self)
  inherit nop_vine_visitor
    
  val mutable has_return = false

  method visit_stmt s = 
    let f x = 
      match x with 
	  Function(a,_,args, d,Some(Block(dl,sl))) ->
	    let hd = List.append restore sl in 
	    let tl = if not has_return then [ret_mem] else []
	    in 
	    let sl = List.append hd tl in 
	      has_return <- false;
	      Function(a,Some(memtyp),mem::args,d,Some(Block(glbldl@dl,sl)))
	| Function(a,_,args,e,None) ->
	    has_return <- true;
	    Function(a,Some(memtyp), mem::args, e, None)
	| _ -> s
    in
      match s with
	  Function _ -> 
	    has_return <- false;
	    ChangeDoChildrenPost(s, f)
	| Return(r) -> 
	    has_return <- true;
	    ChangeTo (rewrite_ret r)
	|Call(r,e,el) -> 
	   ChangeTo (rewrite_call r e el)
	| _ -> DoChildren
end
  in
  let rest = match rest with
    | [] -> []
    |  _ -> 
	let r = List.map (stmt_accept vis) rest in
	  [Block(glbldl, restore @ r @ collect)] 
  in
  let funs = List.map (stmt_accept vis) funs in 
    rest @ funs @ [Return(Some(Lval(Temp(mem))))]


let count_stmts sl = 
  let rec sc sl cntr = 
    match sl with
	Block(_,sl)::ys -> sc (List.append sl ys) (Int64.add cntr 1L)
      | Function(_,_,_,_,Some(Block(_,sl)))::ys -> 
	  sc (List.append sl ys) (Int64.add cntr 1L)
      | Label _ :: ys ->
	  sc ys cntr
      | Comment _ :: ys ->
	  sc ys cntr
      | x::ys -> sc ys (Int64.add cntr 1L )
      | [] -> cntr
  in 
    (* since counting may be expensive, only count if we are 
       collecting statistics *)
    sc sl 0L
;;
	
      

let use_only_one_mem (dl,sl) = 
  let () = pwarn ("Don't use this module!"^
    " it is a temporary hack for oakland designed to work in a"^
    " specific case") in
  let is_mem_type t = 
    let t = unwind_type t in 
      match t with
	  TMem _ -> true
	| _ -> false
  in
  let mem = newvar "mem" (TMem(addr_t, Little)) in 
  let make_only_one_mem sl = 
    let vis = object(self)
      inherit nop_vine_visitor
	
      method visit_alvalue lv = 
	match lv with
	    Temp((_,_,t)) when is_mem_type t -> ChangeTo(Temp(mem))
	  | Mem((_,_,t),e,t') when is_mem_type t -> 
	      ChangeDoChildrenPost(Mem(mem,e,t'), id)
	  | _ -> DoChildren

      method visit_rlvalue lv = 
	match lv with
	    Temp((_,_,t)) when is_mem_type t -> ChangeTo(Temp(mem))
	  | Mem((_,_,t),e,t') when is_mem_type t ->
	      ChangeDoChildrenPost(Mem(mem,e,t'), id)
	  | _ -> DoChildren
    end
    in
      List.map(stmt_accept vis) sl
  in
  let remove_let_mem_assignments sl = 
    let vis = object(self)
      inherit nop_vine_visitor

      val mutable newstmts = []

      method get_newstmts = newstmts

      method reset_newstmts () = newstmts <- []

      method visit_exp e = 
	match e with
	    Let(Mem(a,b,c) as mem,rhs,e') ->
	      newstmts <- Move(mem,rhs)::newstmts;
	      ChangeDoChildrenPost(e', id)
	  | _ -> DoChildren
    end
    in
    let sll = List.map 
      (fun s -> 
	 let () = vis#reset_newstmts () in 
	 let s = stmt_accept vis s in 
	 let newstmts = vis#get_newstmts in 
	   match s with
	     | Move(Temp(_,_,t),Lval(Temp(_,_,t'))) 
		 when is_mem_type t && is_mem_type t' -> newstmts
	     |  _ -> List.rev (s::newstmts)
      ) sl in 
      List.flatten sll
  in
  let verify_no_mem_assignments sl = 
    let vis = object(self)
      inherit nop_vine_visitor 
      method visit_alvalue lv = 
	match lv with
	    Temp((_,_,t)) when is_mem_type t -> failwith "Memory Temp found"
	  | _ -> DoChildren
	      
      method visit_rlvalue lv =
	match lv with
	    Temp((_,_,t)) when is_mem_type t -> failwith "Mem temp found"
	  | _ -> DoChildren
    end
    in
      List.iter (fun s -> ignore(stmt_accept vis s)) sl 
  in
    let sl = make_only_one_mem sl in 
    let sl = remove_let_mem_assignments sl in
    let () = verify_no_mem_assignments sl in
    let dl = List.filter (function (_,_,t) when is_mem_type t -> false
			    | _ -> true) dl in 
      (mem::dl, sl)
	     

(*   let remove_aweful_let_hack sl =  *)
(*     let vis = object(self) *)
(*       inherit nop_vine_visitor *)
	
(*       method visit_stmt s = *)
(* 	match s with *)
(* 	    Move(Temp(mx), Let(Mem(my,e,t), e1, Lval(Temp(mz)))) *)
(* 	      when (mx = my) && (my = mz) -> *)
(* 		ChangeTo(Move(Mem(my,e,t), e1)) *)
(* 	  | _ -> SkipChildren *)
(*     end *)
(*     in *)
(*       List.map (stmt_accept vis) sl  *)
(*   in *)
    
    
