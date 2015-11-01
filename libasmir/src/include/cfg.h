/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef _CFG_H
#define _CFG_H
#include <vector>
#include <map>
#include <string>
#include <algorithm>
#include <utility>
#include <iostream>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/graph/strong_components.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/breadth_first_search.hpp>
#include <boost/graph/depth_first_search.hpp>
#include "dominator.hpp"
#include <sstream>
#include "debug.h"

using namespace std;

/**
 * CFG_ENTRY = unique cfg entry point
 * CFG_EXIT = unique cfg exit point
 * CFG_STOP = halt/stop statement
 * CFG_IJMP = indirect jump target
 * CFG_CALL = call target
 * CFG_RET = function return point
 */
enum {CFG_ENTRY, CFG_EXIT,  CFG_STOP, CFG_IJMP, CFG_CALL, CFG_RET};


typedef boost::adjacency_list<
  boost::vecS, 
  boost::vecS,
  boost::bidirectionalS
  > cfg_t;



typedef boost::graph_traits<cfg_t>::vertex_descriptor cfg_vertex_t;
typedef pair<cfg_vertex_t, cfg_vertex_t> cfg_edge_t;

typedef map<cfg_edge_t, bool> cfg_edge_label_t;


typedef boost::graph_traits<cfg_t>::vertex_iterator cfg_vertex_iterator_t;
typedef boost::graph_traits<cfg_t>::adjacency_iterator 
   cfg_adjacency_iterator_t;
typedef boost::graph_traits<cfg_t>::edge_iterator cfg_edge_iterator_t;
typedef boost::graph_traits<cfg_t>::out_edge_iterator 
   cfg_out_edge_iterator_t;
typedef boost::graph_traits<cfg_t>::in_edge_iterator
  cfg_in_edge_iterator_t;

typedef struct _loop_info_t {
  cfg_edge_t back_edge;
  cfg_vertex_t loop_header;
  set<cfg_vertex_t> vertices;
  set<cfg_edge_t> loop_exits;
  cfg_t cfg;
} loop_info_t;



/// When we unroll a cfg, we create new nodes which don't map to nodes
/// in the original program.  This data structure contains the
/// unrolled, acyclic cfg, along with a mapping from the acyclic cfg
/// to the original cfg number;
typedef struct _unrolled_cfg {
  cfg_t acyclic_cfg;
  cfg_t original_cfg;
  map<cfg_vertex_t, cfg_vertex_t> unrolled2orig; 
} unrolled_cfg_t;


typedef map<cfg_vertex_t, set<cfg_vertex_t> > dom_t;


/// You can use this visitor in a BGL BFS search. The found nodes
/// correspond to reachable vertices.  Note that the constructor
/// argument is a reference: BGL passes in visitors by value, so a
/// copy of the visitor object is local to the BFS routine. By passing
/// in a reference argument, we are assured the reachable_set will be
/// visible and correct after the BFS routine completes.
class cfg_reachability_visitor : public boost::default_bfs_visitor { 
 public:
  cfg_reachability_visitor(set<cfg_vertex_t> &reach) :
    reachable_set(reach)   { };
  void discover_vertex(cfg_vertex_t v, const cfg_t &g)
    {  reachable_set.insert(v);  };
 protected:
  set<cfg_vertex_t> & reachable_set;
};

class cfg_back_edge_visitor : public boost::default_dfs_visitor {
 public:
  typedef boost::graph_traits<cfg_t>::edge_descriptor cfg_edge_desc_t;
  cfg_back_edge_visitor(set<cfg_edge_t> &bk) :
    backedge_set(bk)   { };
  void back_edge(cfg_edge_desc_t e, const cfg_t &g)
    { 
      cfg_edge_t edge;
      edge.first = boost::source(e, g);
      edge.second = boost::target(e, g);
      backedge_set.insert(edge);
    };
 protected:
  set<cfg_edge_t> &backedge_set;
};


/// Return a mapping from the default CFG labels in the 
/// CFG_ enum.
map<cfg_vertex_t, string> get_default_cfg_labels();

/// Get a list of successor ID's for @param node
set<cfg_vertex_t> get_succs(const cfg_vertex_t &node, const cfg_t &cfg );
/// Get a list of predecessor ID's for a @param node
set<cfg_vertex_t> get_preds(const cfg_vertex_t &node, const cfg_t &cfg );

/// A utility function which returns true if the cfg has an
/// edge (src,dst).  I suspect the boost graph library has
/// a function to do this, but I can't find it.
bool
has_edge(const cfg_t &cfg, const cfg_vertex_t &src, 
	 const cfg_vertex_t &dst);

/// Builds a map from a node -> {set of dominated nodes} from the
/// dominator tree.
dom_t
domtree_to_dommap(const cfg_t &dom_tree);

/// Print out a cfg. Prints to cout. Note this is not in DOT format....
void print_cfg(const cfg_t &cfg);

/// Prints out a cfg to the given ostream in DOT format.  @param names
/// is a mapping from cfg vertex to a name. If a vertex isn't found in
/// names, then the number is printed out.
void print_cfg_dot(const cfg_t &cfg, ostream &out, 
		   const map<cfg_vertex_t, string> &names);

/// Utility function to print the dominator mapping. You can
/// use print_cfg(dom_tree, out) to print the dominator tree.
void print_dom_map(const dom_t &dom_map, ostream &out=cout);

/// A helper function that determines if u dom v given the
/// dominator tree.
bool 
u_dom_v(const cfg_vertex_t &u, const cfg_vertex_t &v,
	const cfg_t &dom_tree);


/// A helper function that determines if u idom v given a the
/// dominator tree
bool
u_idom_v(const cfg_vertex_t &u, const cfg_vertex_t &v,
	 const cfg_t &dom_tree);


/// A graph is reducible iff once all backedges are removed the
/// resulting graph is a connected DAG. (dragon book, p 607)
bool
is_reducible_graph(const cfg_t &cfg, const cfg_t &dom_tree, 
		   const vector<cfg_edge_t> &back_edges,
		   const cfg_vertex_t &entry_id);

/// Returns true iff u dom v in the dominator map @param dom_map
bool
u_dommap_v(const cfg_vertex_t &u, const cfg_vertex_t &v,
	   const dom_t &dom_map);

/// A backedge is an edge (v,u) where u dom v.
vector<cfg_edge_t>
get_back_edges(const cfg_t &cfg, const cfg_t &dom_tree);

/// Calculate the loop info, i.e., exit edges, loop body, etc.
loop_info_t
get_loop_info(const cfg_t &cfg, const cfg_edge_t &back_edge);


/// This returns the loop info for the smallest loop.
/// The smallest loop is the loop with the smallest number
/// of nodes in the body. Note the "smallest" is not unique,
/// as two loops may have the same number of nodes in the body.
loop_info_t
get_smallest_loop(const cfg_t &cfg, 
		  const vector<cfg_edge_t> &back_edges);

/// This function unrolls the loop unroll_counts, updating the
/// cfg.  Since this unrolling will create new nodes, we map
/// each new created node to the original node id.  For example,
/// if node 1 is duplicated as node 4, 7, 10 in the new cfg,
/// the returned map (maintained as wp2cfg) will contain
/// 4->1, 7->1, 10->1
map<cfg_vertex_t, cfg_vertex_t>
unroll_loop(cfg_t &cfg, const loop_info_t &loop, 
	    const unsigned &unroll_count);


unrolled_cfg_t unroll_cfg(const cfg_t &original_cfg, 
			  const unsigned &unroll_count,
			  const cfg_vertex_t &entry_id,
			  const cfg_vertex_t &exit_id);


#endif
