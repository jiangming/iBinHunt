open Vine;;

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


let mk_callmap sl tbl = 
  let num_fun = (Hashtbl.length tbl) in
  let h1 = Hashtbl.create num_fun in
  let h2 = Hashtbl.create num_fun in
  let () = List.iter (fun stmt ->
      match stmt with 
	  Vine.Function(v,_,_,_,Some(Vine.Block(blkdl,blksl))) as f-> (
		Printf.printf "Found %s\n" v;
	    	let (calls,_,_) = 
			List.fold_left 
				( fun (acc,num, prev) s -> match (prev, s) with
					| (Vine.Jmp(Vine.Name(targ)), Vine.Special("call")) -> 
						let targ_int64 = (Int64.of_string (String.sub targ 3 ((String.length targ) - 3) )) in
						
	 					( ( (Hashtbl.find tbl targ_int64),num)::acc , num+1 ,s)
					| _ -> 
			 		  	(acc,num+1,s)
				) ([],0,Comment("")) blksl 
		in
		Hashtbl.add h1 v calls;
		Hashtbl.add h2 v f
	  )
	 | Vine.Function(v,_,_,true,None) as f ->
		( Printf.printf "Adding external function %s to cmap and fmap\n" v;
	      Hashtbl.add h1 v [];
	     Hashtbl.add h2 v f )
	 | _ -> ()
      ) sl in
  (h1, h2)




(*tbl is a mapping of function start_address to function name *)
let create_callgraph (dl,sl) tbl = 
  let (cmap,fmap)  = mk_callmap sl tbl in 
  let vertex_id = ref 0 in 
    (* get a vertex, adding if necessary to the graph for name. Return
       the new augmented graph, the new name_2_vertex mapping, and the
       vertex.  Maintain invariant that a vertex for name is in g iff
       the name is in the hashtbl name_2_vertex *)

  let cg_tbl = Hashtbl.create (Hashtbl.length tbl) in
  let get_vertex g name_2_vertex name = (
    try 
      let v = Hashtbl.find name_2_vertex name in 
	(g,name_2_vertex, v)
	  
    with Not_found -> 
	let () = Printf.printf "%s not found in get_vertex, adding to graph\n" name in
      let id = !vertex_id in 
      let () = vertex_id := !vertex_id + 1 in 
      let s = Hashtbl.find fmap name in 
      let v = G.V.create (id,name,s) in 
      let g = G.add_vertex g v in
      let () = Hashtbl.add cg_tbl name id in
      let () = Hashtbl.add name_2_vertex name v in 
	(g,name_2_vertex, v)
  ) in
 let () = Printf.printf "Starting to populate graph:\n" in
    (* populate graph *)
  let (g,name_2_vertex)  = List.fold_left 
    (fun (g,name_2_vertex) s ->
       match s with
	   Vine.Function(name,_,_,_,_) ->  (
	 let () = Printf.printf "Finding all calls from %s!\n" name in
	     let (g,name_2_vertex, srcvertex) = 
	       get_vertex g name_2_vertex name in 
            
	     let calledlst = (
	try Hashtbl.find cmap name
	with Not_found -> 
		(let () = Printf.printf "%s not found in cmap (in List.fold_left)\n" name in
		[] )
	) in 
	       List.fold_left 
		 ( fun (g,name_2_vertex) (dstname,_) -> 
		     let (g,name_2_vertex, dstvertex) = 
		       get_vertex g name_2_vertex dstname in
			(Printf.printf "Adding edge %s to %s\n" name dstname;
		       (G.add_edge g srcvertex dstvertex, name_2_vertex)
			)
		 ) (g,name_2_vertex) calledlst
	   )
	 | _ -> (g,name_2_vertex)
    ) (G.empty, (Hashtbl.create 0)) sl in
  
   
   ( {graph = g;
     next_vertex_id = !vertex_id;
     decls = dl;
    },
	cg_tbl
   )
    

