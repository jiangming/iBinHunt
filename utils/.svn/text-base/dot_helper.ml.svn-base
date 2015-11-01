(** Helper for programs that manipulate .dot files

    These are some helpers for parsing and re-outpitting a graph in graphviz
    format.
*)


module B =
struct
  module V = struct
    type t = Graph.Dot_ast.node_id * Graph.Dot_ast.attr list
    let compare = compare
    and hash = Hashtbl.hash
    and equal = (=)
  end
  module E = struct
    type t = Graph.Dot_ast.attr list
    let compare = compare
    and default = []
  end
  module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(E)
  let empty () = G.empty
  and copy x = x
  and add_vertex = G.add_vertex
  and add_edge = G.add_edge
  and add_edge_e = G.add_edge_e
end

module G = B.G

module Parser = Graph.Dot.Parse
  (B)
  ( struct
      let node id attrlist = (id,attrlist)
      and edge attrlist = attrlist
    end
  )



let string_of_id = function 
  | Graph.Dot_ast.Ident  n
  | Graph.Dot_ast.Number n
  | Graph.Dot_ast.String n
  | Graph.Dot_ast.Html   n ->
      n

let find_vertex g name =
  let res = B.G.fold_vertex
    (fun v -> function
       | Some _ as x -> x
       | None -> 
	   match fst v with
	     | (id, _port) when string_of_id id = name ->
		 Some v
	     | _ -> None
    )
    g None
  in
    match res with
      | Some x -> x
      | None -> raise Not_found

let tr_common_attr (a,v) = 
  let vstring = function Some x -> string_of_id x | None -> "" in
    match string_of_id a with
      | "label" -> `Label (vstring v)
      | _ -> raise Not_found

let ast_vertex_attributes_to_graphviz attrs =
    List.fold_left
      (fun r a -> try tr_common_attr a::r with Not_found -> r)
      []
      (List.flatten attrs)
let ast_edge_attributes_to_graphviz attrs =
    List.fold_left
      (fun r a -> try tr_common_attr a::r with Not_found -> r)
      []
      (List.flatten attrs)


module Printer =
  Graph.Graphviz.Dot(
    struct
      include G

      let graph_attributes _ = []
      and default_vertex_attributes _ = []
      and default_edge_attributes _ = []

      and vertex_name ((id,_), _) = string_of_id id
      and vertex_attributes (_, attrs) = ast_vertex_attributes_to_graphviz attrs
      and get_subgraph _ = None (* FIXME *)
      and edge_attributes (_, attrs, _) = ast_edge_attributes_to_graphviz attrs
    end)
	

module Comp = Graph.Components.Make(G)

