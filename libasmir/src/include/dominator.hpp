//=======================================================================
// Copyright 
// Authors: 
//
// Distributed under the Boost Software License, Version 1.0. (See
// accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//=======================================================================

#ifndef BOOST_GRAPH_DOMINATOR_HPP
#define BOOST_GRAPH_DOMINATOR_HPP


#include <boost/config.hpp>

#include <deque>
#include <set>

#include <boost/graph/depth_first_search.hpp>

namespace boost {

  using namespace std;
  
  namespace detail {
    /**
     * An extended time_stamper which also records vertices for each dfs number
     */
    template<typename TimeMap, typename VertexVector, typename TimeT, typename Tag>
    class time_stamper_with_vertex_vector
      : public base_visitor<
      time_stamper_with_vertex_vector<TimeMap, VertexVector, TimeT, Tag> >
    {
    public :
      typedef Tag event_filter;
      time_stamper_with_vertex_vector(
				      TimeMap timeMap, VertexVector& v, TimeT& t)
	: timeStamper_(timeMap, t), v_(v) { }
      
      template<typename Graph>
      void operator()(
		      const typename property_traits<TimeMap>::key_type& v, const Graph& g)
      {
	timeStamper_(v, g);
	v_[timeStamper_.m_time] = v;
      }
      
    private :
      time_stamper<TimeMap, TimeT, Tag> timeStamper_;
      VertexVector& v_;
    };
    
    /**
     * A convenient way to create a time_stamper_with_vertex_vector
     */
    template<
      typename TimeMap, class VertexVector, typename TimeT, typename Tag>
    time_stamper_with_vertex_vector<TimeMap, VertexVector, TimeT, Tag>
    stamp_times_with_vertex_vector(
				   TimeMap timeMap, VertexVector& v, TimeT& t, Tag)
		{
		  return time_stamper_with_vertex_vector<
		  TimeMap, VertexVector, TimeT, Tag>(timeMap, v, t);
		}
    
    template<class Graph>
    class dominator_visitor
    {
      typedef typename graph_traits<Graph>::vertex_descriptor Vertex;
      typedef typename property_map<Graph, vertex_index_t>::type vertexIndexMap;
      typedef
				iterator_property_map<
	typename vector<int>::iterator, vertexIndexMap>
      TimeMap;
      typedef
      iterator_property_map<
	typename vector<Vertex>::iterator, vertexIndexMap>
      PredMap;
      
    public :
      dominator_visitor(
			const Graph& g, const Vertex& entry, const Vertex& nil)
	: semi_(num_vertices(g)),
	  ancestor_(num_vertices(g), nil),
	  samedom_(ancestor_),
	  best_(semi_),
	  semiMap_(
		   make_iterator_property_map(
					      semi_.begin(), get(vertex_index, g))),
	  ancestorMap_(
		       make_iterator_property_map(
						  ancestor_.begin(), get(vertex_index, g))),
	  bestMap_(
		   make_iterator_property_map(
					      best_.begin(), get(vertex_index, g))),
	  buckets_(num_vertices(g)),
	  bucketMap_(
		     make_iterator_property_map(
						buckets_.begin(), get(vertex_index, g))),
	  entry_(entry), nil_(nil),
	  samedomMap(
		     make_iterator_property_map(
						samedom_.begin(), get(vertex_index, g))),
	  domTree(num_vertices(g))
      {
      }
      
      void operator()(
		      const Vertex& n,
		      const TimeMap& dfnumMap, const PredMap& parentMap,
		      const Graph& g)
      {
	if (n == entry_) return;
	
	const int numOfVertices = num_vertices(g);
	
	const Vertex p(parentMap[n]);
	assert(p != nil_);
	
	Vertex s(p);
	
	// 1. calculate the semidominator of n,
	// based on the semidominator thm.
	// * semidominator thm. : to find the semidominator of a node n,
	//   consider all predecessors v of n in the CFG.
	//  - If v is a proper ancestor of n in the spanning tree
	//    (so dfnum(v) < dfnum(n)), then v is a candidate for semi(n)
	//  - If v is a non-ancestor of n (so dfnum(v) > dfnum(n))
	//    then for each u that is an ancestor of v (or u = v),
	//    let semi(u) be a candidate for semi(n)
	//   of all these candidates, the one with lowest dfnum is
	//   the semidominator of n.
	
	// for each predecessor of n
	typename graph_traits<Graph>::in_edge_iterator inItr, inEnd;
	for (tie(inItr, inEnd) = in_edges(n, g); inItr != inEnd; ++inItr)
	  {
	    const Vertex v = source(*inItr, g);
	    // to deal with unreachable nodes
	    if (dfnumMap[v] < 0 || dfnumMap[v] >= numOfVertices) continue;

	    Vertex s2;
	    if (dfnumMap[v] <= dfnumMap[n])
	      s2 = v;
	    else
	      s2 = semiMap_[ancestor_with_lowest_semi_(v, dfnumMap)];
	    
	    assert(dfnumMap[s2] >= 0 && dfnumMap[s2] < numOfVertices);
	    assert(dfnumMap[s] >= 0 && dfnumMap[s] < numOfVertices);
	    if (dfnumMap[s2] < dfnumMap[s])
	      s = s2;
	  }
	assert(s != nil_);
	semiMap_[n] = s;
	
	// 2. calculation of n's dominator is deferred until
	// the path from s to n has been linked into the forest
	assert(
	       find(bucketMap_[s].begin(), bucketMap_[s].end(), n) ==
	       bucketMap_[s].end());
	bucketMap_[s].push_back(n);
	
	ancestorMap_[n] = p;
	bestMap_[n] = n;
	
	// 3. now that the path from p to v has been linked into
	// the spanning forest, these lines calculate the dominator of v,
	// based on the dominator thm., or else defer the calculation
	// until y's dominator is known
	// * dominator thm. : on the spanning-tree path below semi(n) and
	//   above or including n, let y be the node
	//   with the smallest-numbered semidominator. Then,
	//	
	//  idom(n) = semi(n) if semi(y)=semi(n) or
	//            idom(y) if semi(y) != semi(n)
	typename deque<Vertex>::iterator buckItr;
	for (buckItr = bucketMap_[p].begin();
	     buckItr != bucketMap_[p].end();
	     ++buckItr)
	  {
	    const Vertex v(*buckItr);
	    const Vertex y(ancestor_with_lowest_semi_(v, dfnumMap));
	    assert(y != nil_ && v != nil_);
	    assert(semiMap_[y] != nil_ && semiMap_[v] != nil_);
	    if (semiMap_[y] == semiMap_[v])
	      {
		assert(v != entry_);
		add_edge(p, v, domTree);
	      }
	    else samedomMap[v] = y;
	  }
	
	assert(p >= 0 && p < num_vertices(g));
	bucketMap_[p].clear();
      }
      
    protected :
      
      /**
       * evaluate function in Tarjan's path compression
       */
      const Vertex ancestor_with_lowest_semi_(
					      const Vertex& v, const TimeMap& dfnumMap)
      {
	const Vertex a(get(ancestorMap_, v));
	assert(a != nil_);
	
	if (get(ancestorMap_, a) != nil_)
	  {
	    const Vertex b(ancestor_with_lowest_semi_(a, dfnumMap));
	    assert(b != nil_);
	    
	    put(ancestorMap_, v, get(ancestorMap_, a));
	    
	    assert(get(semiMap_, b) != nil_);
	    assert(get(dfnumMap, get(semiMap_, b)) != -1);
	    assert(get(bestMap_, v) != nil_);
	    assert(get(semiMap_, get(bestMap_, v)) != nil_);
	    assert(get(dfnumMap, get(semiMap_, get(bestMap_, v))) != -1);
	    
	    if (get(dfnumMap, get(semiMap_, b)) <
		get(dfnumMap, get(semiMap_, get(bestMap_, v))))
	      put(bestMap_, v, b);
	  }
	
	return get(bestMap_, v);
      }
      
      vector<Vertex> semi_, ancestor_, samedom_, best_;
      PredMap semiMap_, ancestorMap_, bestMap_;
      vector< deque<Vertex>	> buckets_;
      iterator_property_map<
	typename vector< deque<Vertex> >::iterator, vertexIndexMap>
      bucketMap_;
      const Vertex& entry_, nil_;
      
    public :
      
      PredMap samedomMap;
      Graph domTree;
    };
    
  } // namespace detail
  
  /**
   * build dominator tree using Lengauer-Tarjan algorithm
   * it takes O((V+E)log(V+E)) time
   * 
   * @param idom [out] : immediate dominator map (parent map in dom. tree)
   *        domChildren [out] : children map in dominator tree
   *
   * @note reference Appel. p. 452~453. algorithm 19.9, 19.10.
   *
   * TODO : optimization in Finding Dominators in Practice, Loukas Georgiadis
   */
  template<typename Graph>
  const Graph
  build_dominator_tree_fast(
			    const Graph& g,
			    const typename graph_traits<Graph>::vertex_descriptor& entry,
			    const typename graph_traits<Graph>::vertex_descriptor& nil)
  {
    // typedefs and concept check
    typedef typename graph_traits<Graph>::vertex_descriptor Vertex;
    typedef typename graph_traits<Graph>::vertex_iterator vertexItr;
    typedef typename property_map<Graph, vertex_index_t>::type vertexIndexMap;
    typedef
      iterator_property_map<
    typename vector<int>::iterator, vertexIndexMap>
      TimeMap;
    typedef
      iterator_property_map<
    typename vector<Vertex>::iterator, vertexIndexMap>
      PredMap;
    
    function_requires< BidirectionalGraphConcept<Graph> >();
    
    // 1. make property maps
    const int numOfVertices = num_vertices(g);
    if (numOfVertices == 0) return Graph();
    vertexIndexMap indexMap(get(vertex_index, g));
    
    vector<int> dfnum(numOfVertices, -1);
    TimeMap dfnumMap(make_iterator_property_map(dfnum.begin(), indexMap));
    
    vector<Vertex> parent(numOfVertices, nil);
    PredMap parentMap(make_iterator_property_map(parent.begin(), indexMap));
    
    vector<Vertex> verticesByDFNum(numOfVertices, nil);
    
    int time = -1;
    depth_first_visit(
		      g, entry,
		      make_dfs_visitor(
				       make_pair(
						 record_predecessors(parentMap, on_tree_edge()),
						 detail::stamp_times_with_vertex_vector(
											dfnumMap, verticesByDFNum, time, on_discover_vertex()))),
		      &vector<default_color_type>(numOfVertices)[0]);
    
    // 2. visiting each vertex in reverse post order and calculate sdom
    detail::dominator_visitor<Graph> visitor(g, entry, nil);
    
    int i;
    for (i = numOfVertices - 1; i >= 0; --i)
      {
	const Vertex u(verticesByDFNum[i]);
	if (u != nil) visitor(u, dfnumMap, parentMap, g);
      }
    
    // 3. now all the deferred dominator calculations,
    // based on the second clause of the dominator thm., are performed
    for (i = 0; i <= numOfVertices - 1; ++i)
      {
	const Vertex n(verticesByDFNum[i]);
	
	if (n == entry || n == nil) continue;
	
	Vertex u = visitor.samedomMap[n];
	if (u != nil)
	  {
	    assert(in_degree(u, visitor.domTree) > 0);
	    
	    add_edge(
		     *inv_adjacent_vertices(u, visitor.domTree).first,
		     n,
		     visitor.domTree);
	  }
      }
    
    return visitor.domTree;
  }
  
  /**
   * Muchnick. p. 182, 184
   *
   * using iterative bit vector analysis
   */
  template<typename Graph>
  const Graph
  build_dominator_tree(
		       const Graph& g,
		       const typename graph_traits<Graph>::vertex_descriptor& entry,
		       const typename graph_traits<Graph>::vertex_descriptor& nil)
  {
    typedef typename graph_traits<Graph>::vertex_descriptor Vertex;
    typedef typename graph_traits<Graph>::vertex_iterator vertexItr;
    typedef typename property_map<Graph, vertex_index_t>::type vertexIndexMap;
    typedef
      iterator_property_map<
    typename std::vector< std::set<Vertex> >::iterator,
      vertexIndexMap>
      vertexSetMap;

    function_requires<BidirectionalGraphConcept<Graph> >();
    
    // 1. finding dominator
    // 1.1. initialize
    const int numOfVertices = num_vertices(g);
    if (numOfVertices == 0) return Graph();
    vertexIndexMap indexMap(get(vertex_index, g));
    
    vertexItr vi, viend;
    tie(vi, viend) = vertices(g);
    const std::set<Vertex> N(vi, viend);
		
    bool change = true;
    
    std::vector< std::set<Vertex> > dom(numOfVertices, N);
    vertexSetMap domMap(make_iterator_property_map(dom.begin(), indexMap));
    domMap[entry].clear();
    domMap[entry].insert(entry);
		
    while (change)
      {
	change = false;
	for (tie(vi, viend) = vertices(g); vi != viend; ++vi)
	  {
	    if (*vi == entry) continue;
	    
	    std::set<Vertex> T(N);
	    
	    typename graph_traits<Graph>::in_edge_iterator inItr, inEnd;
	    for (tie(inItr, inEnd) = in_edges(*vi, g); inItr != inEnd; ++inItr)
	      {
		const Vertex p = source(*inItr, g);
		
		std::set<Vertex> tempSet;
		std::set_intersection(
				      T.begin(), T.end(), domMap[p].begin(), domMap[p].end(),
				      std::inserter(tempSet, tempSet.begin()));
		T.swap(tempSet);
	      }
	    
	    T.insert(*vi);
	    if (T != domMap[*vi])
	      {
		change = true;
		domMap[*vi].swap(T);
	      }
	  } // end of for (tie(vi, viend) = vertices(g)
      } // end of while(change)
    
    // 2. build dominator tree
    for (tie(vi, viend) = vertices(g); vi != viend; ++vi)
      domMap[*vi].erase(*vi);
    
    Graph domTree(numOfVertices);
    
    for (tie(vi, viend) = vertices(g); vi != viend; ++vi)
      {
	if (*vi == entry) continue;
	
	// we should iterate through copied dominator set
	const std::set<Vertex> tempSet(domMap[*vi]);
	typename std::set<Vertex>::const_iterator s;
	for (s = tempSet.begin(); s != tempSet.end(); ++s)
	  {
	    typename std::set<Vertex>::const_iterator t;
	    for (t = domMap[*vi].begin(); t != domMap[*vi].end(); ++t)
	      {
		if (*t == *s) continue;
		if (domMap[*s].find(*t) != domMap[*s].end())
		  domMap[*vi].erase(t);
	      }
	  }
      }
    
    for (tie(vi, viend) = vertices(g); vi != viend; ++vi)
      {
	if (*vi != entry && domMap[*vi].size() == 1)
	  {
	    add_edge(*domMap[*vi].begin(), *vi, domTree);
	  }
      }
    
    return domTree;
  }
  
} // namespace boost

#endif // BOOST_GRAPH_DOMINATOR_HPP
