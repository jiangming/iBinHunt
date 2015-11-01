(*
*  vine_ssa_dataflow.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Fri Jul  6 10:36:10 2007 David Brumley
*  Last update Tue Jul 10 17:38:07 2007 David Brumley
*)

open Ssa
open Dataflow

module G = Vine_cfg.MakeG(struct type t = Ssa.stmt list end);;

module ConstantProp =
struct

  module Debug = Debug.Make(struct let name = "ConstantProp" end)

  module G = G

  type cptype = Unknown | NonConst | Const of value

  type t = Top | Ht of (var, cptype) Hashtbl.t

  let cpmeet v1 v2 = 
    match v1,v2 with
	Unknown, Unknown ->  Unknown
      | Unknown,Const c -> v2
      | Const(c), Unknown -> v1
      | Const(c1), Const(c2)  when c1 = c2 -> v1
      | _ -> NonConst

  let lookup ht k = 
    try 
      Hashtbl.find ht k 
    with
	Not_found -> Unknown

  let t_to_ht t = 
    match t with
	Top -> Hashtbl.create 7
      | Ht(h1) -> h1

  let meet v1 v2 = 
    let (h1:(var,cptype) Hashtbl.t) = t_to_ht v1 in 
    let (h2:(var,cptype) Hashtbl.t) = t_to_ht v2 in 
      Hashtbl.iter 
	(fun k v1 ->
	   let v2 = lookup h2 k in
	   let nv = cpmeet v1 v2 in 
	     Hashtbl.replace h2 k nv
	) h1; Ht(h2)

  let is_scalar (_,_,t) = 
    match (Vine.unwind_type t) with
	Vine.Array _ -> false
      | _ -> true

  let stmt_transfer ht stmt = 
    match stmt with
	Jmp _ 
      | CJmp _ 
      | Label _
      | Comment _
      | Return _
      | Call _ -> ()
      | Move(x, Val(v)) when is_scalar x -> (
	  match v with
	      Int(i,t) ->
		Hashtbl.replace ht x (Const(v))
	    | Lval(variable) ->
		Hashtbl.replace ht x (lookup ht variable)
	    | _ -> ()
	)
      | Move _ -> ()

  let transfer_function graph node t  = 
    let stmts = graph#get_info (graph#find node) in 
    let ht = t_to_ht t in 
    let f = stmt_transfer ht in 
      List.iter (f) stmts;
      Ht(ht)

  let eq = (=)


  let s0 = Vine_cfg.BB_Entry

  let init = Ht(Hashtbl.create 7)

  let dir = Dataflow.Forward

  let top = Top

end

module CP = Make(ConstantProp);;

let constant_propagation graph = 
  let (in_f,out_f)  = CP.worklist_iterate graph in
    (in_f,out_f)


let constant_prop_and_fold do_simplify graph =
  let (in_f, _) = constant_propagation graph in 
  let vis = object(self)
    inherit nop_ssa_visitor

    val mutable ctx = Hashtbl.create 7
      
    method set_ctx c = ctx <- c

    method get_ctx  = ctx

    method visit_value v =
      match v with
	  Lval(v') ->  (
	    let cp_value = ConstantProp.lookup ctx v' in
	      match cp_value with
		  ConstantProp.Unknown 
		| ConstantProp.NonConst -> Vine.DoChildren
		| ConstantProp.Const(c) -> 
		    ConstantProp.Debug.dprintf "Replacing %s with %s"
		      (Vine.var_to_string v')
		      (Ssa.value_to_string c);
		    Vine.ChangeTo(c)
	  )
	| _ -> Vine.SkipChildren
		    
  end
  in
    graph#iter_bb 
      (fun bb -> 
	 let () = ConstantProp.Debug.dprintf "BLOCK %s"
	   (Vine_cfg.bbid_to_string (graph#get_id bb)) in
	 let stmts = graph#get_info bb in 
	 let intbl = in_f (graph#get_id bb) in 
	 let ht = ConstantProp.t_to_ht intbl in
	 let stmts' = List.map
	   (fun s -> 
	      vis#set_ctx ht;
	      let s' = stmt_accept vis s in 
		ConstantProp.stmt_transfer (vis#get_ctx) s;
		s'
	   ) stmts 
	 in
	   graph#set_info bb stmts'
      ) 



module DeadCode = 
struct

  type site = (Ssa.stmt list Vine_cfg.bb) * Ssa.stmt

  module Debug = Debug.Make(struct let name = "DeadCode" end)

  let def = function
      Move(lv, e) -> Some(lv)
    | _ -> None

  let use f s = 
    let vis =  object(self)
      inherit nop_ssa_visitor
      
      val mutable ctx = []
	
      method get_ctx = ctx
	
      method visit_rvar v = f v;
	Vine.DoChildren
    end
    in 
     ignore(Ssa.stmt_accept vis s)


(** in SSA, a variable is live at its definition site iff its list of
    uses is not empty. Therefore, calculating live variables is really
    just a matter of calculating whether or not a variable has any
    uses. (p445  ML Tiger book ) *)      
  let do_dce ?(globals=[]) graph = 
    let (usesites:(Ssa.var, site list) Hashtbl.t) = 
      Hashtbl.create 57 in 
    let (defsites:(Ssa.var, site) Hashtbl.t) = Hashtbl.create 57 in
    let remove_stmt (bb, stmt) = 
      let () = Debug.dprintf "Removing from %s dead stmt: %s"
	(Vine_cfg.bbid_to_string (graph#get_id bb))
	(Ssa.stmt_to_string stmt)
      in
      let stmts = graph#get_info bb in 
      let stmts' = List.filter (fun s -> s <> stmt) stmts in 
	graph#set_info bb stmts'
    in
    let calculate () = 
      graph#iter_bb 
	(fun bb -> 
	   let stmts = graph#get_info bb in 
	     List.iter
	       (fun s -> 
		  let site = (bb, s) in 
		  let f arg =  (
		    let oldsites = (
		      try Hashtbl.find usesites arg with Not_found -> []
		    ) in 
		      Hashtbl.replace usesites arg 
			(Vine_util.list_union oldsites [site])
		  ) in
		    (* add definition site *)
		    (match (def s) with
			 None -> ()
		       | Some(v) -> Hashtbl.add defsites v site
		    );
		    (* for each use of a variable [v] in s, f v will
		       be calculated, thus adding the variable to our
		       current use site. *)
		    use f s;
	       ) stmts
	)
    in
      (* at this point defsites should contain all definition sites,
	 and usesites should list all use sites *)
    let has_dead_code = ref true in 
      while (!has_dead_code) do
	let () = calculate () in 
	let deaddefs = Hashtbl.fold 
	  (fun k v acc -> if Hashtbl.mem usesites k then acc else
	     v::acc) defsites [] in 
	  (match deaddefs with
	      [] -> has_dead_code := false
	    | _ -> 
		List.iter (fun x -> remove_stmt x) deaddefs;
		Hashtbl.clear defsites;
		Hashtbl.clear usesites
	  )
      done
end

