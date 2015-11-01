(**
   Functions for counting the number of paths in a graph.

   The definition of "path" used here is a walk with no repeating vertices.
   (AKA, a "simple path" for those who use the older definition where a path
   could repeat vertices. See {!Walkcount} if you do want repeating vertices.)
   http://mathworld.wolfram.com/Path.html

   TODO: Add optimizations for when there is a subgraph with a single entry and
   exit.
*)

module type G =
sig
  type t
  type vertex
  val fold_succ : (vertex -> 'a -> 'a) -> t -> vertex -> 'a -> 'a
  val remove_vertex : t -> vertex -> t
end

(** Implementation for persistent graphs *)
module Make(G:G) =
struct
  (** [count_paths g src dst] will count the number of paths in [g] from
      [src] to [dst] *)
  let rec count_paths g src dst =
    if src = dst then 1
    else
      let g' = G.remove_vertex g src in
	G.fold_succ (fun s n -> n + count_paths g' s dst) g src 0
end



module type G2 =
sig
  type t
  module V : Graph.Sig.COMPARABLE
  val fold_succ : (V.t -> 'a -> 'a) -> t -> V.t -> 'a -> 'a
end

(** Implementation for mutable graphs *)
module Make2(G:G2) =
struct
  module H = Hashtbl.Make(G.V)

  (** [count_paths g src dst] will count the number of paths in [g] from
      [src] to [dst] *)
  let count_paths g src dst =
    let h = H.create 1000 in
    let rec paths s =
      if G.V.equal s dst then 1
      else
	let () = H.add h s () in
	let res =
	  G.fold_succ
	    (fun s n -> if H.mem h s then n else n + paths s)
	    g s 0
	in
	let () = H.remove h s in
	  res
    in
      paths src
end
