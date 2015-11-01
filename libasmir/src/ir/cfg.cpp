/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "cfg.h"



set<cfg_vertex_t>
get_succs(const cfg_vertex_t &n, const cfg_t &cfg)
{
  cfg_out_edge_iterator_t ei, ei_end;
  set<cfg_vertex_t> ret;
  boost::tie(ei, ei_end) = boost::out_edges(n,cfg);
  for(; ei != ei_end; ei++){
    ret.insert(boost::target(*ei,cfg));
  }
  return ret;
}

set<cfg_vertex_t>
get_preds( const cfg_vertex_t &n,const cfg_t &cfg)
{
  cfg_in_edge_iterator_t ei, ei_end;
  set<cfg_vertex_t> ret;
  boost::tie(ei, ei_end) = boost::in_edges(n,cfg);
  for(; ei != ei_end; ei++){
    ret.insert(boost::source(*ei,cfg));
  }
  return ret;
}


/// A utility function which returns true if the cfg has an
/// edge (src,dst).  I suspect the boost graph library has
/// a function to do this, but I can't find it.
bool
has_edge(const cfg_t &cfg, const cfg_vertex_t &src, 
	 const cfg_vertex_t &dst)
{
  cfg_adjacency_iterator_t adj_i, adj_i_end;
  boost::tie(adj_i, adj_i_end) = adjacent_vertices(src, cfg);  
  for(; adj_i != adj_i_end; adj_i++){
    const cfg_vertex_t &v = *adj_i;
    if(v == dst)
      return true;
  }
  return false;
}


/// Builds a map from a node -> {set of dominated nodes} from the
/// dominator tree.
dom_t
domtree_to_dommap(const cfg_t &dom_tree)
{
  dom_t ret;
  // Every node also dominates itself
  cfg_vertex_iterator_t vi, vi_end;
  for(boost::tie(vi, vi_end) = boost::vertices(dom_tree);
      vi != vi_end; vi++){
    ret[*vi].insert(*vi);
    // Add all the successors to the node;
    cfg_out_edge_iterator_t oi, oi_end;
    for(boost::tie(oi, oi_end) = boost::out_edges(*vi, dom_tree);
	oi != oi_end; oi++){
      ret[*vi].insert(boost::target(*oi, dom_tree));
    }
  }
  // Now compute the transitive closure
  bool changed = true;
  while(changed){
    changed = false;
    for(dom_t::const_iterator it = ret.begin(); it != ret.end();
	it++){
      const set<cfg_vertex_t> &dominated = it->second;
      const cfg_vertex_t &dominator = it->first;
      unsigned sz_before = ret[dominator].size();
      for(set<cfg_vertex_t>::const_iterator i2 = dominated.begin();
	  i2 != dominated.end(); i2++){
	ret[dominator].insert(ret[*i2].begin(), ret[*i2].end());
      }
      if(ret[dominator].size() > sz_before)
	changed = true;
    }
  }
  return ret;
}


void print_cfg(const cfg_t &cfg)
{
  boost::print_graph(cfg, boost::get(boost::vertex_index,cfg));

}


void print_cfg_dot(const cfg_t &cfg, ostream &out, 
		   const map<cfg_vertex_t, string> &namemap)
{
  cfg_vertex_iterator_t vi, vi_end;
  boost::tie(vi, vi_end) = boost::vertices(cfg);
  unsigned num_vertices = vi_end - vi;
  string *names = new string[num_vertices+1];
  unsigned i = 0;
  ostringstream os;
  for(; vi != vi_end; vi++, i++){
    if(namemap.find(*vi) == namemap.end()){
      os.str("");
      os << *vi;
      names[i] = string(os.str());
    } else {
      names[i] = string(namemap.find(*vi)->second);
    }
  }  
  boost::write_graphviz(out, cfg, boost::make_label_writer(names));
  delete [] names;
}


/// Utility function to print the dominator mapping. You can
/// use print_graph(dom_tree, out) to print the dominator tree.
void print_dom_map(const dom_t &dom_map, ostream &out)
{
  for(dom_t::const_iterator it = dom_map.begin();
      it != dom_map.end(); it++){
    const cfg_vertex_t &dominator = it->first;
    const set<cfg_vertex_t> &dominated = it->second;
    out << dominator << " -> ";
    for(set<cfg_vertex_t>::const_iterator i2 = dominated.begin();
	i2 != dominated.end(); i2++){
      
      out << *i2 << ", ";
    }
    out << endl;
  }
}

/// A helper function that determines if u dom v given the
/// dominator tree.
bool 
u_dom_v(const cfg_vertex_t &u, const cfg_vertex_t &v,
	const cfg_t &dom_tree)
{
  cfg_out_edge_iterator_t oi, oi_end;

  set<cfg_vertex_t> reachable;
  cfg_reachability_visitor vis(reachable);
  boost::breadth_first_search(dom_tree, boost::vertex(u, dom_tree),
			      visitor(vis));

  if(reachable.find(v) != reachable.end())
     return true;
  else
    return false;

}

bool 
u_idom_v(const cfg_vertex_t &u, const cfg_vertex_t &v,
	const cfg_t &dom_tree)
{
  cfg_out_edge_iterator_t oi, oi_end;
  boost::tie(oi, oi_end) = boost::out_edges(u, dom_tree);
  for(; oi != oi_end; oi++){
    if(v == boost::target(*oi, dom_tree))
      return true;
  }
  return false;
}
						   


/// A graph is reducible iff once all backedges are removed the
/// resulting graph is a connected DAG. (dragon book, p 607)
bool
is_reducible_graph(const cfg_t &cfg, const cfg_t &dom_tree, 
		   const vector<cfg_edge_t> &back_edges,
		   const cfg_vertex_t &entry_id)
{

  cfg_t copy = cfg_t(cfg);
  set<cfg_vertex_t> before_reachable;
  cfg_reachability_visitor vis1(before_reachable);
  boost::breadth_first_search(copy, boost::vertex(entry_id, copy),
			      visitor(vis1));  
 
  for(vector<cfg_edge_t>::const_iterator it = back_edges.begin();
      it != back_edges.end(); it++){
    cfg_edge_t e = *it;
    print_debug("cfg", "removing backedge %u,%u", e.first, e.second);
    boost::remove_edge(e.first, e.second, copy);
  }


  set<cfg_vertex_t> after_reachable;
  cfg_reachability_visitor vis2(after_reachable);

  boost::breadth_first_search(copy, boost::vertex(entry_id, copy),
			      visitor(vis2));

  set<cfg_vertex_t> diff;
  set_difference(before_reachable.begin(), before_reachable.end(),
		 after_reachable.begin(), after_reachable.end(),
		 insert_iterator<set<cfg_vertex_t> >(diff, diff.begin()));

  for(unsigned i = 0; i < CFG_RET; i++)
    diff.erase(i);

  if(diff.size() == 0){
    return true;
  } else {
    ostringstream os;
    for(set<cfg_vertex_t>::const_iterator it = diff.begin();
	it != diff.end(); it++){
      os << *it << ", ";
    }
    print_debug("warning", 
		"irreducible graph!\nunreachable vertices:\n\t%s",
		os.str().c_str());
    return false;
		
  }


}

/// Returns truee iff u dom v in the dominator map @param dom_map
bool
u_dommap_v(const cfg_vertex_t &u, const cfg_vertex_t &v,
	   const dom_t &dom_map)
{
  assert(dom_map.find(u) != dom_map.end());
  set<cfg_vertex_t> dominated = dom_map.find(u)->second;
  if(dominated.find(v) != dominated.end())
    return true;
  for(set<cfg_vertex_t>::const_iterator it = dominated.begin();
      it != dominated.end(); it++){
    const cfg_vertex_t &tmp = *it;
    assert(dom_map.find(tmp) != dom_map.end());
    const set<cfg_vertex_t> &domin2 = dom_map.find(tmp)->second;
    if(domin2.find(v) != domin2.end())
      return true;
  }
  return false;
}

/// A backedge is an edge (v,u) where u dom v.
vector<cfg_edge_t>
get_back_edges(const cfg_t &cfg, const cfg_t &dom_tree)
{
  vector<cfg_edge_t> ret;

  cfg_edge_iterator_t ei, ei_end;
  //  dom_t dom_map = domtree_to_dommap(dom_tree);
  

  for(boost::tie(ei, ei_end) = boost::edges(cfg);
      ei != ei_end; ei++){
    const cfg_vertex_t &src = boost::source(*ei, cfg);
    const cfg_vertex_t &dst = boost::target(*ei, cfg);
    //if(u_dommap_v(dst, src, dom_map)){
    if(u_dom_v(dst, src, dom_tree)){
      print_debug("cfg", "\tback edge: (%u, %u)", src, dst);
      ret.push_back(cfg_edge_t(src, dst));
    }
  }
  return ret;
}

/// Calculate the loop info, i.e., exit edges, loop body, etc.
loop_info_t
get_loop_info(const cfg_t &cfg, const cfg_edge_t &back_edge)
{

  // Dragon book. Section 10.4 page 604.  Algorithm for finding
  // vertices in a loop.
  stack<cfg_vertex_t> vstack;
  loop_info_t lp;
  lp.back_edge = back_edge;
  lp.loop_header = back_edge.second;
  lp.vertices.insert(back_edge.second);
  cfg_vertex_t m = back_edge.first;
  if(lp.vertices.find(m) == lp.vertices.end()){
    lp.vertices.insert(m);
    vstack.push(m);
  }

  while(!vstack.empty()){
    m = vstack.top();
    vstack.pop();
    cfg_in_edge_iterator_t ie, ie_end;
    for(boost::tie(ie, ie_end) = boost::in_edges(m, cfg);
	ie != ie_end; ie++){
      const cfg_vertex_t &src = boost::source(*ie, cfg);
      if(lp.vertices.find(src) == lp.vertices.end()){
	lp.vertices.insert(src);
	vstack.push(src);
      }
    }
  }

  // For each vertex, any edge to a vertex not in the loop
  // must be an exit point.
  for(set<cfg_vertex_t>::const_iterator it = lp.vertices.begin();
      it != lp.vertices.end(); it++){
    cfg_out_edge_iterator_t oi, oi_end;
    for(boost::tie(oi, oi_end) = out_edges(*it, cfg);
	oi != oi_end; oi++){
      const cfg_vertex_t &dst = boost::target(*oi, cfg);
      if(lp.vertices.find(dst) == lp.vertices.end()){
	lp.loop_exits.insert(cfg_edge_t(*it, dst));
      }
    }
  }
  return lp;
}

/// This returns the loop info for the smallest loop.
/// The smallest loop is the loop with the smallest number
/// of nodes in the body. Note the "smallest" is not unique,
/// as two loops may have the same number of nodes in the body.
loop_info_t
get_smallest_loop(const cfg_t &cfg, const vector<cfg_edge_t> &back_edges)
{
  loop_info_t lp;
  unsigned min_loop_size = (unsigned) -1;

  if(back_edges.size() == 0){
    memset(&lp, 0, sizeof(loop_info_t));
    return lp;
  }

  // Find the smallest loop, which is the loop with the fewest
  // dominated nodes.
  for(unsigned cntr = 0; cntr < back_edges.size(); cntr++){
    loop_info_t t = get_loop_info(cfg, back_edges[cntr]);
    if(t.vertices.size() < min_loop_size){
      lp = t;
      min_loop_size = t.vertices.size();
    }
  }

  if(is_debug_on("cfg")){
    ostringstream os;

    os << "**** CURRENT SMALLEST LOOP ****" << endl;
    os << "Loop header: " << lp.loop_header << endl;
    os << "\tLoop body: ";
    cfg_vertex_iterator_t vit, vit_end;
    for(set<cfg_vertex_t>::const_iterator it = lp.vertices.begin();
	it != lp.vertices.end(); it++){
      os << *it << ", ";
    }
    os << endl;
    os << "\tLoop exit points: ";
    for(set<cfg_edge_t>::const_iterator lbi = lp.loop_exits.begin();
	lbi != lp.loop_exits.end(); lbi++){
      os << "(" << (*lbi).first << "," << (*lbi).second << ") ";
    }
    os << endl;
    print_debug("cfg", os.str().c_str());
  }
  return lp;
}

/// This function unrolls the loop unroll_counts, updating the
/// cfg.  Since this unrolling will create new nodes, we map
/// each new created node to the original node id.  For example,
/// if node 1 is duplicated as node 4, 7, 10 in the new cfg,
/// the returned map (maintained as wp2cfg) will contain
/// 4->1, 7->1, 10->1
map<cfg_vertex_t, cfg_vertex_t>
unroll_loop(cfg_t &cfg, const loop_info_t &loop, 
	   const unsigned &unroll_count)
{

  print_debug("cfg", "Starting to unroll loop w/ backedge (%u, %u)",
	      loop.back_edge.first, loop.back_edge.second);
  // By removing all backedges, we ensure the resulting
  // graph is cycle free.
  boost::remove_edge(loop.back_edge.first, loop.back_edge.second, cfg);

  if(unroll_count == 1) return map<cfg_vertex_t, cfg_vertex_t>();

  // map cfg to set of wp nodes in unrolling.
  map<cfg_vertex_t, vector<cfg_vertex_t> > cfg2wp; 
  // map wp node to the corresponding cfg node (this is what
  // we return)
  map<cfg_vertex_t, cfg_vertex_t> wp2cfg; 

  cfg_vertex_t new_vertex;
  // Make the new copies of each vertex in the body.
  for(set<cfg_vertex_t>::const_iterator it = loop.vertices.begin();
      it != loop.vertices.end(); it++){
    for(unsigned i = 0; i < unroll_count-1; i++){
      new_vertex = boost::add_vertex(cfg);
      cfg2wp[*it].push_back(new_vertex);
      print_debug("cfg", "%u -> new %u", *it, new_vertex);
      wp2cfg[new_vertex] = *it;
    }
  }

  

  // Copy over edges. 
  // For each vertex u in the loop body, we find it's out edges
  // (u,v). We will be duplicating (u,v) iff (u,v) is not an exit
  // edge, and (u,v) is not the back edge.
  cfg_out_edge_iterator_t oit, oit_end;
  for(set<cfg_vertex_t>::const_iterator it = loop.vertices.begin();
      it != loop.vertices.end(); it++){
    for(boost::tie(oit, oit_end) = boost::out_edges(*it, cfg);
	oit != oit_end; oit++){
      const cfg_vertex_t &src = boost::source(*oit, cfg);
      const cfg_vertex_t &dst = boost::target(*oit, cfg);
      // If this edge isn't an exit or backedge, then we make copies.
      if((loop.loop_exits.find(cfg_edge_t(src,dst)) ==
	 loop.loop_exits.end()) && 
	 (loop.back_edge.first != src || loop.back_edge.second != dst)){
	for(unsigned i = 0; i < unroll_count-1; i++){
	  boost::add_edge(cfg2wp[src][i],
			  cfg2wp[dst][i], cfg);
	  print_debug("cfg", "adding edge (%u, %u) for (%u,%u)", 
		      cfg2wp[src][i], cfg2wp[dst][i], src, dst);
	}	
      }
    }
  }


  const vector<cfg_vertex_t> &unroll_srcs =
     cfg2wp[loop.back_edge.first];
  const vector<cfg_vertex_t> &unroll_dsts = 
    cfg2wp[loop.back_edge.second];
  // Connect up each unroll
  boost::add_edge(loop.back_edge.first,
		  unroll_dsts[0], cfg);

  print_debug("cfg", "linking up unrolled copy via (%u, %u)",
	      loop.back_edge.first, unroll_dsts[0]);

  for(unsigned i = 1; i < unroll_count-1; i++){
    boost::add_edge(unroll_srcs[i-1], unroll_dsts[i],
 		    cfg);
    print_debug("cfg", "linking up unrolled copy via (%u, %u)",
		unroll_srcs[i-1], unroll_dsts[i]);
  }

  // Link up copies of new  vertex (u',exit_pt) where u' is a 
  // copy of u and (u,exit_pt).
  cfg_edge_t hdr_exit;
  for(set<cfg_edge_t>::const_iterator it = loop.loop_exits.begin();
      it != loop.loop_exits.end(); it++){
    const cfg_vertex_t &src = (*it).first;
    const cfg_vertex_t &dst = (*it).second;
    if(src == loop.loop_header)
      hdr_exit = *it;
    const vector<cfg_vertex_t> &srcs = cfg2wp[src];
    for(vector<cfg_vertex_t>::const_iterator sit = srcs.begin();
	sit != srcs.end(); sit++){
      const cfg_vertex_t &src2 = *sit;
      boost::add_edge(src2, dst, cfg);
      print_debug("cfg", "Linking up exit point (%u, %u)",
		  src2, dst);
    }
  }

  // The loop header appears one extra time.
  new_vertex = boost::add_vertex(cfg);
  cfg2wp[loop.loop_header].push_back(new_vertex);
  wp2cfg[new_vertex] = loop.loop_header;

  cfg_vertex_t error_vertex = boost::add_vertex(cfg);
  // Link up the extra header vertex to the graph
  boost::add_edge(cfg2wp[loop.back_edge.first][unroll_count-2],
  		  new_vertex, cfg);
  // If the header actually has an exit path, e.g., a while loop,
  // hook it up as well.
  for(set<cfg_edge_t>::const_iterator it = loop.loop_exits.begin();
      it != loop.loop_exits.end(); it++){
    const cfg_edge_t &edge = *it;
    if(edge.first == loop.back_edge.second){
      boost::add_edge(new_vertex, edge.second, cfg);
    }
  }

  // Link up the header vertex exit point to the 
  boost::add_edge(new_vertex, error_vertex,cfg);

  


  print_debug("cfg", "Done unrolling loop (%u, %u)",
	      loop.back_edge.first, loop.back_edge.second);
  return wp2cfg;
}


unrolled_cfg_t unroll_cfg(const cfg_t &original_cfg, 
			  const unsigned &unroll_count,
			  const cfg_vertex_t &entry_id,
			  const cfg_vertex_t &exit_id)
{
  unrolled_cfg_t ret;
  ret.original_cfg = original_cfg;
  ret.acyclic_cfg = original_cfg;
  cfg_t &new_cfg = ret.acyclic_cfg;
  map<cfg_vertex_t, cfg_vertex_t> &unrolled2orig = ret.unrolled2orig;

  cfg_t dom_tree = build_dominator_tree_fast(new_cfg,
					     entry_id,
					     exit_id);

  vector<cfg_edge_t> back_edges = get_back_edges(new_cfg, dom_tree);




  // We currently don't handle irreducible graphs. There are
  // known techniques to handle irreducible graphs (e.g., 
  // node-splitting), which we do not implement here.
  if(!is_reducible_graph(new_cfg, dom_tree, back_edges, entry_id)){
    fatal("cfg", "Irreducible CFG's not handled");
  }

  // Process loops inside to outside.  We unroll the inside
  // loops first (inside loops are smaller than outside loops)
  // because the unrolled inside loop is needed when unrolling
  // the outside loop. I'm sure there is a more efficient
  // algorithm, but right now this works.
  print_debug("cfg", "Unrolling loops (smallest to largest)");

  while(back_edges.size() != 0){

    loop_info_t loop_info = get_smallest_loop(new_cfg, back_edges);

    map<cfg_vertex_t, cfg_vertex_t > vertex_map = 
      unroll_loop(new_cfg, loop_info, unroll_count);

    for(map<cfg_vertex_t, cfg_vertex_t>::const_iterator i2 = 
	  vertex_map.begin(); i2 != vertex_map.end(); i2++){
      cfg_vertex_t orig_v = i2->second;
      // If we have an inner loop, after unrolling we
      // may create some new vertex, say x. Then there is mapping
      // orig -> x.  In an outer loop, if we run into x, we need
      // to map it back to orig.
      while(unrolled2orig.find(orig_v) != unrolled2orig.end())
	orig_v = unrolled2orig.find(orig_v)->second;
      const cfg_vertex_t &new_v = i2->first;
      unrolled2orig.insert(pair<cfg_vertex_t, cfg_vertex_t>(new_v, orig_v));
    }
    //    unrolled2orig.insert(vertex_map.begin(), vertex_map.end());

    dom_tree = build_dominator_tree_fast(new_cfg,
					 entry_id,
					 exit_id);
    back_edges = get_back_edges(new_cfg, dom_tree);
  }

  print_debug("cfg", "Done unrolling loops");
  if(is_debug_on("cfg")){
    print_debug("cfg", "Writing out unrolled loop to unrolled.dot");
    ofstream out("unrolled.dot");
    boost::write_graphviz(out,new_cfg);
    out.close();
  }

  // Now we do one pass looking for back-edges in a BFS traversal. If
  // we find any, we break them arbitrarily.
  
  set<cfg_edge_t> dfs_backedges;
  cfg_back_edge_visitor dfsvis(dfs_backedges);

  boost::depth_first_search(new_cfg,
			    visitor(dfsvis));

  //			    &color_vec[0]);
			    
    // 			    boost::vertex(entry_id, new_cfg)
    //			    );

  if(dfs_backedges.size() != 0)
    print_debug("warning", "During unrolling found unnatural loop");
  for(set<cfg_edge_t>::const_iterator it = dfs_backedges.begin();
      it != dfs_backedges.end(); it++){
    cfg_edge_t e = *it;
    print_debug("warning", "Breaking back-edge (%u, %u) arbitrarily",
		e.first, e.second);
    boost::remove_edge(e.first, e.second, new_cfg);
  }

  // Finally, make sure all cfg vertex numbers map to themself.
  // new vertex mappings were addded in the while loop above.
  cfg_vertex_iterator_t vit, vit_end;
  for(boost::tie(vit, vit_end) = boost::vertices(original_cfg);
      vit != vit_end; vit++){
    const cfg_vertex_t &v = *vit;
    unrolled2orig[v] = v;
  }
  return ret;
}


map<cfg_vertex_t, string> get_default_cfg_labels()
{
  map<cfg_vertex_t, string> ret;
 ret.insert(pair<cfg_vertex_t, string>(CFG_ENTRY, "ENTRY"));
 ret.insert(pair<cfg_vertex_t, string>(CFG_EXIT, "EXIT"));
 ret.insert(pair<cfg_vertex_t, string>(CFG_STOP, "STOP"));
 ret.insert(pair<cfg_vertex_t, string>(CFG_IJMP, "IJMP"));
 ret.insert(pair<cfg_vertex_t, string>(CFG_CALL, "CALL"));
 ret.insert(pair<cfg_vertex_t, string>(CFG_RET, "RET"));
 return ret;
}
