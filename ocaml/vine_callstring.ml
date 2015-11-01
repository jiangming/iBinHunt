(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_callstring.ml
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Mon Apr 23 16:28:45 2007 David Brumley
*  Last update Fri Jul 27 17:16:07 2007 David Brumley
*)
(**)

open ExtList
module M = PMap 

module D = Debug.Make(struct let name = "Vine_callstrings" and default=`Debug end)
open D

let default_edge_id = 0

let fst (a,b,c) = a
let snd (a,b,c) = b
let third (a,b,c) = c

type vinfo = int * string * Vine.stmt 

module CGV = 
  struct
    type t = vinfo
    let label x = x
  end

module CGE = 
  struct
    type t = int
    let compare = compare
    let default = default_edge_id
  end

module G = Graph.Persistent.Digraph.AbstractLabeled (CGV) (CGE)


module DotGraph = 
struct
  type t = G.t
  module V = G.V
  module E = G.E
  let iter_vertex = G.iter_vertex
  let iter_edges_e = G.iter_edges_e
  let graph_attributes g = []
  let default_vertex_attributes g = []
  let vertex_name v =  string_of_int (fst (V.label v)) 
  let vertex_attributes v = [`Label (snd (V.label v))]
  let default_edge_attributes g = []
  let edge_attributes e = [`Label (string_of_int (E.label e))]
  let get_subgraph v = None
end



module Dot = Graph.Graphviz.Dot(DotGraph);;

module Component = Graph.Components.Make(G);; 

module Dfs = Graph.Traverse.Dfs(G);;

type vertex = G.vertex 
type edge = G.edge
and edge_label = int
and funmap_t = (Vine.var, Vine.stmt) Symbols.t
and csg = {graph: G.t;
	   root: vertex;
	   next_vertex_id: int;
	   decls : Vine.decl list;
	  }


let label_of v = G.V.label v 
let succ csg  = G.succ csg.graph     
let is_empty csg = G.is_empty csg.graph 
let nb_vertex csg = G.nb_vertex csg.graph
let nb_edges csg = G.nb_edges csg.graph
let in_degree csg = G.in_degree csg.graph
let mem_vertex csg = G.mem_vertex csg.graph
let mem_edge csg = G.mem_edge csg.graph
let mem_edge_e csg = G.mem_edge csg.graph
let find_edge csg = G.find_edge csg.graph
let succ csg = G.succ csg.graph
let pred csg = G.pred csg.graph
let succ_e csg = G.succ_e csg.graph
let pred_e csg = G.pred_e csg.graph
let iter_vertex f csg = G.iter_vertex f csg.graph
let iter_edges f csg = G.iter_edges f csg.graph
let fold_vertex f csg = G.fold_vertex f csg.graph
let fold_edges f csg = G.fold_edges f csg.graph
let iter_edges_e f csg = G.iter_edges_e f csg.graph
let fold_edges_e f csg = G.fold_edges_e f csg.graph
let iter_succ f csg = G.iter_succ f csg.graph
let iter_pred f csg = G.iter_pred f csg.graph
let fold_succ f csg = G.fold_succ f csg.graph
let fold_pred f csg = G.fold_pred f csg.graph
let iter_succ_e f csg = G.iter_succ_e f csg.graph
let fold_succ_e f csg = G.fold_succ_e f csg.graph
let iter_pred_e f csg = G.iter_pred_e f csg.graph
let fold_pred_e f csg = G.fold_pred_e f csg.graph

let output_dot g outc =
  Dot.output_graph outc g.graph

let get_root csg = 
  csg.root

(*pm*)
let fix_name n =
	let n2 = 
	if ( String.contains n '@')
	then (
		let left_index = String.index n '@' in
		String.sub n 1 (left_index-1)
	)
	else n
	in
	if ( (String.contains n2 '(') && (String.contains n2 ')') )
	then (
		let left_index = String.rindex n2 '(' in
		String.sub n2 0 left_index
	)
	else n2
;;
(*pm end*)
    

let mk_csg (dl,sl) root = 
  let (callmap,fmap) = Vine_callgraph.mk_callmap sl in
	
	let ()=Printf.printf "pm:after Vine_callgraph.mk_callmap sl\n" in 
	
  let vertex_num = ref 0 in 
  let mk_vertex (name:string) = (
		(*pm*)
		let name=fix_name name in
		(*pm*)
    let v = !vertex_num in
		let ()=Printf.printf "pm:before M.find: name=%s\n" name in
		
    let s = M.find name fmap in
		let ()=Printf.printf "pm:after M.find: name=%s\n" name in 
      vertex_num := !vertex_num + 1;
      G.V.create (v, name, s)
  ) in 
    (* current_name is the name (string) of the callee. callstack is
       the current callstack, where each member of the callstack is a
       vertex *)
  let rec process_blk callstack (g,id) current_name = (
		(*pm*)
		let current_name = fix_name current_name in
		(*pm end*)
    match callstack with
	c::cs ->  (
	  let current_vertex = mk_vertex current_name in 
	  let edge = G.E.create c id current_vertex in 
	    (* add edge from caller -> callee *)
	  let g = G.add_edge_e g edge in
	    dprintf "mk_csg: %d vertices, %d edges" (G.nb_vertex g) (G.nb_edges g);
	    (* check if the current_name already exists in the
	       callstack, indicating a recursive call *)
	    if List.exists (fun v -> snd (G.V.label v) = current_name) callstack
	    then (
	      (* a recursive call cycle has been found, do not look at
	      calls since this would be enumerating a cycle*)
	      (g, id+1)
	    ) else (
	      (* no cycle, continue for each call *)
	      let calls = M.find current_name callmap in
	      let callstack = current_vertex::callstack in
	      let (g,_) = List.fold_left (process_blk callstack) (g,0) calls in
		(g, id+1)
	    )
  )
      | [] -> failwith "callstack cannot be empty"
  )
  in
	
	let ()=Printf.printf "pm: before mk_vertex\n" in
  let rootv = mk_vertex root in
	let ()=Printf.printf "pm: after mk_vertex\n" in
	 
  let g = G.add_vertex G.empty rootv in
  let callstack = [rootv] in 
  let calls = M.find root callmap in
	
	let ()=Printf.printf "pm: before List.fold_left (process_blk callstack) (g,0) calls\n" in
  let (g,_) = List.fold_left (process_blk callstack) (g,0) calls
  in
	let ()=Printf.printf "pm: after List.fold_left (process_blk callstack) (g,0) calls\n" in
    {graph = g;
     next_vertex_id = !vertex_num;
     root = rootv;
     decls = dl;
    }

let chop csg (a:vertex) (b:vertex) (voutside:vertex) =
  let has_a_b_edge = G.mem_edge csg.graph a b in
  let g = if not has_a_b_edge then 
    G.add_edge csg.graph b a 
  else 
    csg.graph 
  in 
  let (_,scc) = Component.scc g in 
  let group = scc a in 
  let addifgroup v newg = 
    if scc v = group then
      ( (* let g = G.add_vertex g v in  *)
	  G.fold_succ (fun v' newg ->
			 if scc v' = group then (
			   let e = G.find_edge g v v' in 
			     G.add_edge_e newg e
			 ) else (
			   G.add_edge newg v voutside
			 )
		      ) g v newg
      ) else newg 
  in
  let newg = G.fold_vertex addifgroup g G.empty in 
  let newg = if has_a_b_edge then G.remove_edge newg b a else newg in
    {graph = newg;
     root = csg.root;
     next_vertex_id = csg.next_vertex_id;
     decls = csg.decls;
    }


let int_to_vertex csg num = 
  let ret = ref None in 
    iter_vertex (fun x -> let (a,b,c) = label_of x in 
		   if a = num then ret := Some(x)) csg;
    match !ret with
	None -> raise Not_found
      | Some(x) -> x

let name_to_vertices csg name = 
  fold_vertex (fun v acc -> 
		 let (a,b,c) = label_of v in 
		   if b = name then v::acc else acc
	      ) csg []


let add_vertex csg =  function
    Vine.Function(v, _, _, _, _) as f ->
      let vnum = csg.next_vertex_id in
      let vertex = G.V.create (vnum, v, f) in 
      let g = G.add_vertex csg.graph vertex in 
	(vertex, {graph = g;
		  root = csg.root;
		  next_vertex_id = csg.next_vertex_id + 1;
		  decls = csg.decls;
		 })
  | _ -> raise 
      (Invalid_argument "callstring verticex must correspond to functions")



let mk_edge_e v1 id v2  = G.E.create  v1 id v2

let add_edge csg v1 v2 = 
  {graph = G.add_edge csg.graph v1 v2;
   root = csg.root;
   next_vertex_id = csg.next_vertex_id;
   decls = csg.decls;
  }

let remove_edge csg v1 v2 = 
  { graph = G.remove_edge csg.graph v1 v2;
    root = csg.root;
    next_vertex_id = csg.next_vertex_id;
    decls = csg.decls;
  }

let remove_vertex csg v = 
  {graph = G.remove_vertex csg.graph v;
   root = csg.root;
   next_vertex_id = csg.next_vertex_id;
   decls = csg.decls;
  }

let add_edge_e csg edge = 
  {graph = G.add_edge_e csg.graph edge;
   root = csg.root;
   next_vertex_id = csg.next_vertex_id;
   decls = csg.decls;
  }



let get_decls csg = 
  csg.decls

let context_name n i = 
  n^"_"^(string_of_int i)

let prune_unreachable csg = 
  let reachable = ref [] in 
  let () = Dfs.prefix_component 
    (fun v -> reachable := v::!reachable) csg.graph csg.root in
  let newgraph = fold_vertex (fun v g ->
				if List.mem v !reachable then 
				  g
				else
				  remove_vertex g v) csg csg in
    {graph = newgraph.graph;
     root = csg.root;
     next_vertex_id = csg.next_vertex_id;
     decls = csg.decls
    }

let csg_to_context_program csg  = 
  let rename_function i = function
      Vine.Function(v, a, b,c, d) ->
	let v' = context_name v i in
	  Vine.Function(v', a, b, c, d)
    | _ -> failwith "Callstring graph contained non-function vertex"
  in
    (* rewrite a single call to name to name+succid *)
  let fix_call name succid = function
     Vine.Call(lvopt, Vine.Name(v), el) when v = name ->
       let v' = context_name v succid in
	 Vine.Call(lvopt, Vine.Name(v'), el)
    | Vine.Call(lvopt, Vine.Name(v), el) when v <> name ->
	failwith "Call but to wrong function"
    | Vine.Call _ -> failwith "Indirect calls not supported"
    | _ -> failwith "Expected to be rewriting a call. got something else"
  in
    (* rewrite a single stmt. We pass in the current statement, and
       the rewrite_info list.  If the list is empty, that means we've
       rewritten everything, so we just add s to the list of rewritten
       statements.  If the list is non-empty, we check the current
       statement number against the
       to-be-rewritten-call-statement-number, and if the same, we
       rewrite the call. *)
  let rewrite_stmt s = function
      ([], index, sl) -> (* we've process everything *)
	([], index+1, s::sl) 
    | ((num,n,succid)::lst as l, index, sl) -> 
	if index = num then (
	  let c' = fix_call n succid s in
	    (lst, index+1, c'::sl)
	)  else (
	  (l,index+1, s::sl)
	)
  in
    (* rewrite calls in a function. We pass in a list containing
       statement numbers to be rewritten (as rewrite_info list...see
       below for format), and a Function. We rewrite each statement in
       the function as the identity if its not in the rewrite
       list, else rewrite it. Note that lst is sorted by statement
       number, so we can do this in linear time. *)
  let rewrite_function_stmts lst = function
      Vine.Function(a,b,c,d,Some(Vine.Block(blkdl, blksl))) as f ->
	let (x,_,sl) = List.fold_left (fun acc s -> 
				       rewrite_stmt s acc
				    ) (lst,0,[]) blksl in

	  (* make sure we've processed everything *)
	let () = assert ( List.length x = 0) in
	  if List.length lst = 0 then f else (
	    let sl = List.rev sl in 
	    let f = Vine.Function(a,b,c,d,Some(Vine.Block(blkdl, sl)))
	    in 
	      f
	  )
    | Vine.Function(a,b,c,true,None) as f -> f
    | _ -> failwith "Expected to be rewriting a function"
  in
  let sl = G.fold_vertex
    (fun v acc ->
       let (i,s,f) = G.V.label v in
       let f = rename_function i f in
	 (* rewrite_info (edge_id, successor name, successor id) is:
	     - the edge id. If Foo() calls Bar() at statement i, then
	    the edge id for edge Foo->Bar should be i.
	    - the successor nodes name. Foo at statement i should have
	    Call(...,name,...)
	    - The successor nodes id. We will rewrite
	    Call(...,name,...) to Call(...,name^id,...)
	 *)
       let rewrite_info = G.fold_succ_e (fun edge acc ->
					   let eid = G.E.label edge in
					   let succ = G.E.dst edge in
					   let (id,s,_) = G.V.label
					     succ in
					     (eid,s,id)::acc
					) csg.graph v [] in
       let rewrite_info = List.stable_sort 
	 (fun (e1,s1,id1) (e2,s2,id2) -> compare e1 e2) rewrite_info in
       let newf = rewrite_function_stmts rewrite_info f in
	 newf::acc
    ) csg.graph [] in
    (csg.decls,sl)



let csg_to_chopped_program csg outside_stmt do_opt =
  let jmp_target_name = "$csg_jmp_out" in 
  let real_end_name  = "$real_end" in 
  let rename_function i = function
      Vine.Function(v, a, b,c, d) ->
	let v' = context_name v i in
	  Vine.Function(v', a, b, c, d)
    | _ -> failwith "Callstring graph contained non-function vertex"
  in
    (* rewrite a single call to name to name+succid *)
  let fix_call name succid = function
     Vine.Call(lvopt, Vine.Name(v), el) when v = name ->
       let v' = context_name v succid in
	 Vine.Call(lvopt, Vine.Name(v'), el)
    | Vine.Call(lvopt, Vine.Name(v), el) when v <> name ->
	failwith "Call but to wrong function"
    | Vine.Call _ ->
	failwith "Indirect calls not supported yet"

    | _ -> failwith "Expected to be rewriting a call. got something else"
  in
    (* rewrite a single stmt. We pass in the current statement, and
       the rewrite_info list.  If the list is empty, that means we've
       rewritten everything, so we just add s to the list of rewritten
       statements.  If the list is non-empty, we check the current
       statement number against the
       to-be-rewritten-call-statement-number, and if the same, we
       rewrite the call. *)
  let rewrite_stmt s = function
      ([], index, sl) -> (* we've process everything *)
	([], index+1, s::sl) 
    | ((num,n,succid)::lst as l, index, sl) -> 
	if index = num then (
	  let c' = fix_call n succid s in
	  let jmp = Vine.Jmp(Vine.Name(jmp_target_name)) in 
	    (lst, index+1, jmp::c'::sl)
	)  else (
	  (l,index+1, s::sl)
	)
  in
    (* rewrite calls in a function. We pass in a list containing
       statement numbers to be rewritten (as rewrite_info list...see
       below for format), and a Function. We rewrite each statement in
       the function as the identity if its not in the rewrite
       list, else rewrite it. Note that lst is sorted by statement
       number, so we can do this in linear time. *)
  let rewrite_function_stmts lst = function
      Vine.Function(a,b,c,d,Some(Vine.Block(blkdl, blksl))) as f ->
	let (x,_,sl) = List.fold_left (fun acc s -> 
				       rewrite_stmt s acc
				    ) (lst,0,[]) blksl in

	  (* make sure we've processed everything *)
	let () = assert ( List.length x = 0) in
	  if List.length lst = 0 then f else (
	    let stmts_at_end = 	  
	      [Vine.Jmp(Vine.Name(real_end_name));
	       (* it seems we need a label called CFG_CHOP_OUTSIDE for the
		  CFG chop code to work out *)
	       Vine.Label("CFG_CHOP_OUTSIDE");
	       Vine.Label(jmp_target_name);
	       outside_stmt;
	       Vine.Label(real_end_name);(List.hd sl)] in 
	    let sl = List.tl sl in 
	    let sl = List.append (List.rev stmts_at_end) sl in 
	    let sl = List.rev sl in 
	    let f = Vine.Function(a,b,c,d,Some(Vine.Block(blkdl, sl))) in 
	    let cfg = Vine_cfg.func_to_cfg f in
	    let endblock = cfg#find_label jmp_target_name in
	    let eid = cfg#get_id endblock in
	    let chop = Vine_cfg.chop cfg Vine_cfg.BB_Entry eid eid in 
	    let () = Vine_cfg.remove_chop_trailing_edges chop eid "CFG_CHOP_OUTSIDE" in 
	    let () = if do_opt then
	      (let glbls = csg.decls in 
		 ignore(Vine_dataflow.do_dce ~globals:glbls chop )
	      )
	       else 
		 () 
	    in 
	    let (dl,sl) = Vine_cfg.cfg_to_prog chop Vine_cfg.BB_Entry eid in
	      Vine.Function(a,b,c,d,Some(Vine.Block(dl,sl))) 
	  )
    | Vine.Function(a,b,c,true,None) as f -> f
    | _ -> failwith "Expected to be rewriting a function"
  in
  let sl = G.fold_vertex
    (fun v acc ->
       let (i,s,f) = G.V.label v in
       let f = rename_function i f in
	 (* rewrite_info (edge_id, successor name, successor id) is:
	     - the edge id. If Foo() calls Bar() at statement i, then
	    the edge id for edge Foo->Bar should be i.
	    - the successor nodes name. Foo at statement i should have
	    Call(...,name,...)
	    - The successor nodes id. We will rewrite
	    Call(...,name,...) to Call(...,name^id,...)
	 *)
       let rewrite_info = G.fold_succ_e (fun edge acc ->
					   let eid = G.E.label edge in
					   let succ = G.E.dst edge in
					   let (id,s,_) = G.V.label
					     succ in
					     (eid,s,id)::acc
					) csg.graph v [] in
       let rewrite_info = List.stable_sort 
	 (fun (e1,s1,id1) (e2,s2,id2) -> compare e1 e2) rewrite_info in
       let newf = rewrite_function_stmts rewrite_info f in
	 newf::acc
    ) csg.graph [] in
    (csg.decls,sl)


let standard_multichop prog root startname endaddrs = 
  let chopendfun = Vine_chop.std_chop_end_fun in
  let chopendlbls = List.map (fun x -> Vine.Label(Vine.addr_to_label x))
    endaddrs in 
  let marker = Vine.Label(Vine_chop.std_chop_call_end_marker) in
	
	let ()=Printf.printf "pm: before prepare_chop_program\n" in 
  let (dl,sl) = 
    Vine_chop.prepare_chop_program prog chopendlbls marker chopendfun in
		
	let ()=Printf.printf "pm: aftere prepare_chop_program\n" in
	
  let prog = (dl, Vine_chop.std_chop_outside_fun::sl) in
  
	let ()=Printf.printf "pm: before mk_csg\n" in
	let g = mk_csg prog root in 
	let ()=Printf.printf "pm: after mk_csg\n" in
	
  let svl = name_to_vertices g startname in
 (* let () = assert (List.length svl = 1) in*)(*pm*) 
  let sv = List.hd svl in 
  let evl = name_to_vertices g Vine_chop.std_chop_end_name in 
  let outsidedummy = Vine.Function("$outside_chop_dummy", 
			      None, [], true, None) in
  let (ov, g) = add_vertex g outsidedummy in
  let dummy = Vine.Function("$chop_end_dummy", None, [], true, None) in 
  let (ev,g) = add_vertex g dummy in
  let g = List.fold_left (fun g v ->add_edge g v ev) g evl in
	
	let ()=Printf.printf "pm: before chop\n" in
  let chop = chop g sv ev ov in 
	let ()=Printf.printf "pm: after chop\n" in
	
  let chop = remove_vertex chop ev in 
  let chop = remove_vertex chop ov in 
    chop

let csg_to_program csg = 
  let sl = fold_vertex (fun v acc ->
			  let (_,_,f) = label_of v in 
			    if List.mem f acc then acc else f::acc)
    csg [] in 
  let dl = csg.decls in 
    (dl,sl)
