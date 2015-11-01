(**
  Counts the number of paths in the graph

   This requires a patched ocamlgraph-0.99. (dot_ast is missing in the Makefile)
*)



module Unit =
struct
  type t = unit
  let default = ()
  let compare () () = 0
end

module V =
struct
  include String
    
  let equal = (=)
  let hash = Hashtbl.hash
end

(*
module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(Unit)
module B = Graph.Builder.P(G)
*)
module G = Graph.Imperative.Digraph.ConcreteLabeled(V)(Unit)
module B = Graph.Builder.I(G)
module Dot_ast = Graph.Dot_ast

(* from ocamlgraph's dot_test.ml *)
module DotInput = 
  Graph.Dot.Parse
    (B)
    (struct 
      let node (id,_) _ = match id with
        | Graph.Dot_ast.Ident s
        | Graph.Dot_ast.Number s
        | Graph.Dot_ast.String s
        | Graph.Dot_ast.Html s -> s
      let edge _ = ()
    end)


module G' =
struct
  type t = G.t
  module V = G.V
  type vertex = V.t
  let pred = G.succ
  let succ = G.pred
  let fold_vertex = G.fold_vertex
  let iter_succ = G.iter_pred
end

module PC = Pathcount.Make2(G)
module NP = Vine_cfg.NodePartition.Make(G)
module RNP = Vine_cfg.NodePartition.Make(G')
module Dom = Dominator.Make(G)

(* breaks backedges using the dominators *)
let break_dom_backedges g s0 =
  let {Dom.dom=dom} = Dom.compute_all g s0 in
    G.iter_edges
      (fun u v ->
	 if dom v u then (
	   Printf.printf "Removing %s -> %s\n" u v;
	   G.remove_edge g u v)
      )
      g
  


(* breaks backedges in the DFS tree *)
let break_backedges g s0 =
  let visited = Hashtbl.create (G.nb_vertex g) in
  let rec vis v =
    Hashtbl.add visited v false;
    G.iter_succ
      (fun v' ->
	 try
	   if Hashtbl.find visited v'
	   then ()
	   else (Printf.printf "Removing %s->%s\n" v v';
		 G.remove_edge g v v')
	 with Not_found ->
	   vis v'
      )
      g v;
    Hashtbl.replace visited v true
  in
    vis s0

let () = Printf.printf "Parsing file\n%!"

let g = DotInput.parse Sys.argv.(1)

let src = Sys.argv.(2)
let dst = Sys.argv.(3)

let () = Printf.printf "Parsed file with %d vertices and %d edges\n%!" (G.nb_vertex g) (G.nb_edges g)

let () = print_endline "removing unreachable nodes"
let () = NP.iter_unreachable (G.remove_vertex g) g src
let () = print_endline "removing reverse-unreachable nodes"
let () = RNP.iter_unreachable (G.remove_vertex g) g dst
let () = print_endline "copying"
let g' = G.copy g
let () = print_endline "breaking dom backedges"
let () = break_dom_backedges g' src
let () = print_endline "breaking backedges"
let () = break_backedges g' src
let () = Printf.printf "g' with %d vertices and %d edges\n%!" (G.nb_vertex g') (G.nb_edges g')

module G1 =
struct
  include G
  let s0 = src
end
module WC = Walkcount.Make(G1)

let () = print_endline "counting walks..."
let walks = WC.count_walks_nounreachable g' src dst
let () = Printf.printf "Counted %d walks from %s to %s\n%!" walks src dst


let count = PC.count_paths g src dst
let () = Printf.printf "Counted %d paths from %s to %s\n" count src dst
