(**
   Functions for counting the number of walks in a graph.
   http://mathworld.wolfram.com/Walk.html

   To count the number of paths instead (walks with no repeating vertices), see
   {!Pathcount}

   @note This was written as a quick hack. It should probably be made to use
   the polymorphic version of dataflow so we can specify different start and
   end nodes.
*)

module type G =
sig
  type t
  module V : Graph.Sig.COMPARABLE
  val pred : t -> V.t -> V.t list
  val succ : t -> V.t -> V.t list
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
  val fold_vertex : (V.t -> 'a -> 'a) -> t -> 'a -> 'a
  val nb_vertex : t -> int
  val s0 : V.t
end


module Make(G:G with type V.t = string) =
struct
  module DF_Problem =
  struct
    module G = G
    module L =
    struct
      type t = int
      let top = 0
      let meet = (+)
      let equal = (=)
    end
      
    let transfer_function _g _v l = l

    let s0 = G.s0
    let init = 1
    let dir = Dataflow.Forward
  end

  module D = Dataflow.Make(DF_Problem)

  let count_walks g src =
    assert(G.V.equal src DF_Problem.s0);
    fst(D.topological_worklist_iterate g)


      
  module H = Hashtbl.Make(G.V)
  let count_walks_nounreachable g src =
    let size = G.nb_vertex g in
    let h = H.create size in
    let visited = H.create size in
    let add v n =
      try
	let c = H.find h v in
	  H.replace h v (c+n)
      with Not_found ->
	H.add h v n
    in
    let find = H.find h in
    let rec visit v =
      let n = find v in
	Printf.printf "%s: %n\n" v n;
	if H.mem visited v
	then failwith("Revisiting node "^v^" there must be a loop.")
	else
	H.add visited v ();
	G.iter_succ (fun s -> add s n) g v;
	G.iter_succ
	  (fun s ->
	     if not(H.mem visited s) && List.for_all (H.mem visited) (G.pred g s)
	     then visit s
	     else ()
	  )
	  g v
    in
    let () = H.add h src 1 in
    let () = visit src in
      H.find h

end
