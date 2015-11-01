(*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*)
(*
*  vine_callstrings.mli
*
*  Made by (David Brumley)
*  Login   <dbrumley@rtfm.ece.cmu.edu>
*
*  Started on  Fri May  4 19:01:26 2007 David Brumley
*  Last update Thu Jun 28 09:45:32 2007 David Brumley
*)

(** 
    Our callstring graph (csg) library.  Our callstrings graph is
    defined as a directed, root graph:

    - There is a distinguished root vertex.
    - Any calls the root vertex makes become unique vertices in the
    callstring graph. vertices are distinguished by their calling
    context, which in our implementation, is just a number.
    For example, if root calls a, b, a, then there are
    three children off the root with context numbers 1, 2, and 3
    (assuming calling context 0 for the root).
    - For each vertex, we recursively compute the calling context up
    to recursion.  Any recursion becomes a single cycle in the graph.
    For example, if A calls B calls C calls A, then there are 3 unique
    nodes in the graph, and edges (A,B), (B,C), (C,A).
    - In our graph, each edge is labeled with the statement number in
    the source vertex which makes the call to the destination vertex.
    So if A calls B at line 10, then the edge is (A,B) with label 10.

    Our implementation of the callstring graph is completely
    functional.

    FIXME: Make this ascribe to Graph.Sig.G so that the graph algorithms
    can be used on it.

    @author David Brumley
*)


(** the type of a callstring vertex *)
type vertex 

(** information carried at each vertex.  given vinfo (i,s,f), i a
    unique calling context id, s is the name of the function, and f is
    the function corresponding to the callstring vertex *)
type vinfo = int * Vine.label * Vine.stmt

(** an edge *)
type edge 
(** callstring edges are labeled with the statement number in the
    function which makes the call. 
*)
type edge_label = int

(** the default edge id. By default is 0. If you create an edge
    without specifying a label id, this id is used. *)
val default_edge_id : int

(** the type of our callstring graph *)
type csg

(** the callstring graph keeps track of the global variable
    declarations in the program *)
val get_decls : csg -> Vine.decl list 

(** get the root vertex in the callstring graph *)
val get_root : csg -> vertex

(** [output_dot csg oc] output the callstring graph [csg] as a dot
    file to channel [oc] *)
val output_dot : csg -> out_channel -> unit

(** create a new callstring graph from a program. [mk_csg root prog]
    returns a new callstring graph rooted at [root] for program [prog].
    Note the csg keeps track of the program decls in case you later
    want to output the csg back as a program.

    The input program should be de-scoped.
*)
val mk_csg : Vine.program -> Vine.label -> csg



(** [csg_to_context_program csg] outputs a vine program where
    functions are duplicated and renamed by their calling context.
    Calls are rewritten appropriate to call the appropriate calling
    context version of the function.
*)
val csg_to_context_program: csg -> Vine.program

(** [csg_to_chopped_program csg s b] is used to calculate the program
    corresponding to a csg chop. For any node [v] in [csg], suppose
    [v] calls [u] at line 10, and [w] at line 12, then has 20 more
    statements.  This would calculate a control-flow chop of the
    function at [v] such that statement [s] is called if we are past a
    point for executing [u] or [v]. In essence, it is a chop of the
    function for the vertex such that it only reaches its callsites,
    and does not execute beyond that.

    The [b] parameter determines whether optimizations such as dead
    code elimination are performed.

    Note that functions in the output program are duplicated in a
    context-sensitive way (up to recursion), and calls are
    appropriately updated.
    
    Unless you are making a signature, you probably don't want to use
    this function.
*)
val csg_to_chopped_program : csg -> Vine.stmt -> bool -> Vine.program 

(** [context_name s i] yields a unique vertex name composed of [s] and
   [i]. This is the name {csg_to_chopped_program} would give a
    function named [s] with vertex context [id]. *)
val context_name : string -> int -> string

(** convert a csg back to the program. This is a shortcut for
    iterating over all vertices and accumulating the function
    definitions at each node, and getting the csg global decls *)
val csg_to_program : csg -> Vine.program 

(** [int_to_vertex csg i] returns the vertex numbered [i].  This is
    useful only when you know the calling context id. 
    @raise Not_found if [i] is not a valid calling context id
*)
val int_to_vertex : csg -> int -> vertex

(** [name_to_vertices csg foo] returns all the verticies for functions
    named [foo] *)
val name_to_vertices : csg -> string -> vertex list

(** [add_vertex csg s] adds a vertex corresponding to function [s] to
    the csg. We do not recompute the calltree or look at whom [s] may
    be calling.....the node is simply added. 
    @return a new csg and the newly created vertex 
    @raise Invalid_argument if [s] is not a Vine.Function.
*)
val add_vertex : csg -> Vine.stmt -> (vertex * csg)

(** [add_edge csg v1 v2] adds edge (v1,v2) with default label
    {default_edge_id}. Returns a new csg with the edge added.
*)
val add_edge : csg -> vertex -> vertex -> csg

(** create a labeled edge. *)
val mk_edge_e : vertex -> edge_label -> vertex -> edge
(** add a labeled edge, returning the new csg *)
val add_edge_e : csg -> edge -> csg

(** remove an edge *)
val remove_edge : csg -> vertex -> vertex -> csg

(** remove a vertex and all its edges, returning the updated csg *)
val remove_vertex : csg -> vertex -> csg

(** remove any nodes not reachable from the csg root *)
val prune_unreachable : csg -> csg

(** [chop csg v1 v2 v3] creates a chop of the program consisting of
    any path reachable from [v1] to [v2] in the program. This may not
    work if there is no path at all from [v1] to [v2]...though it
    may.  Any edge going out the chop will end up at [v3].
*)
val chop : csg -> vertex -> vertex -> vertex  -> csg

(** [standard_multichop p root csf eal] returns a chopped program. where
    [p] is the input program, [root] the root of the callstring graph
    (e.g., main), [csf] is the chop start function, and [eal] is a
    list of addresses to end at.
    
    The standard multichop chop outside and chop end nodes are
    taken from {Vine_chop.std_chop_end} and
    {Vine_chop.std_chop_outside}.  We also insert a marker
    {!Vine_chop.std_chop_call_end_marker} at each point after we put
    in a call to either chop_outside or chop_end.  You can use the
    marker to find where the chopped calls are.
*)
val standard_multichop :
  Vine.program -> Vine.label -> string -> int64 list -> csg


(** the remaining functions are all from the ocamlgraph Persistent
    AbstractLabeled library. Please look at the ocamlgraph
    documentation for more information on using these functions
*)
val succ : csg -> vertex -> vertex list 
val label_of : vertex -> vinfo 
val is_empty : csg -> bool
val nb_vertex : csg -> int
val nb_edges : csg -> int
val in_degree : csg -> vertex -> int
val mem_vertex : csg -> vertex -> bool
val mem_edge : csg -> vertex -> vertex -> bool
val mem_edge_e : csg -> vertex -> vertex -> bool
val find_edge : csg -> vertex -> vertex -> edge
val succ : csg -> vertex -> vertex list
val pred : csg -> vertex -> vertex list
val succ_e : csg -> vertex -> edge list
val pred_e : csg -> vertex -> edge list
val iter_vertex : (vertex -> unit) -> csg -> unit
val iter_edges : (vertex -> vertex -> unit) -> csg -> unit
val fold_vertex : (vertex -> 'a -> 'a) -> csg -> 'a -> 'a
val fold_edges : (vertex -> vertex -> 'a -> 'a) -> csg -> 'a -> 'a
val iter_edges_e : (edge -> unit) -> csg -> unit
val fold_edges_e : (edge -> 'a -> 'a) -> csg -> 'a -> 'a
val iter_succ : (vertex -> unit) -> csg -> vertex -> unit
val iter_pred : (vertex -> unit) -> csg -> vertex -> unit
val fold_succ : (vertex -> 'a -> 'a) -> csg -> vertex -> 'a -> 'a
val fold_pred : (vertex -> 'a -> 'a) -> csg -> vertex -> 'a -> 'a
val iter_succ_e : (edge -> unit) -> csg -> vertex -> unit
val fold_succ_e : (edge -> 'a -> 'a) -> csg -> vertex -> 'a -> 'a
val iter_pred_e : (edge -> unit) -> csg -> vertex -> unit
val fold_pred_e : (edge -> 'a -> 'a) -> csg -> vertex -> 'a -> 'a

