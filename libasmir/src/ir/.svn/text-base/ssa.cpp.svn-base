/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "ssa.h"

/// Compute the dominance frontier (Muchnick Alg 8.19 p255)
/// @param df (OUT) is the computed dominance frontier
/// @param cfg is the flow graph
/// @param dom_tree is the dominator tree for cfg
/// @param n is the node we are working on.
void compute_df(const cfg_t &cfg, const cfg_t &dom_tree, 
		const cfg_vertex_t &n, dom_t &df);

/// Print out the dominance frontier @param df
void print_df(const dom_t &df);


/// Insert the phi function at the beginning of the block. The phi
/// function will contain as many variables as there are predecessors
/// to @param block in the @param cfg
void insert_phi(ir_bb_t *block, const string name,
		const reg_t reg, const cfg_t &cfg);

/// Helper class to rename variables when converting to ssa form.
class SSARenameVisitor : public DefaultIRVisitor {
 public:
  SSARenameVisitor(ir_function_t *f,
		   const cfg_t &dom_tree,
		   const map<string, set<cfg_vertex_t> > &defsites);
  void rename(const cfg_vertex_t n);

  virtual void visitTemp(Temp *);
  virtual void visitPhi(Phi *);
  virtual void visitMove(Move *);
 protected:
  /// Variables defined within the node.
  map<cfg_vertex_t, set<string> > node_defs;
  map<string, unsigned> count;
  map<string, stack<unsigned> > varstack;
  bool update_phi;
  bool rename_definition;
  ir_function_t *f;
  cfg_t dom_tree;
  unsigned rename_position;
};

void compute_df(const cfg_t &cfg, const cfg_t &dom_tree, 
		const cfg_vertex_t &n, dom_t &df)
{
  set<cfg_vertex_t> S;
  set<cfg_vertex_t> succ = get_succs(n, cfg);
  for(set<cfg_vertex_t>::const_iterator it = succ.begin();
      it != succ.end(); it++){
    const cfg_vertex_t &y = *it;
    if(!u_idom_v(n, y, dom_tree)){
      S.insert(y);
    }
  }
  succ = get_succs(n, dom_tree);
  for(set<cfg_vertex_t>::const_iterator it = succ.begin();
      it != succ.end(); it++){
    compute_df(cfg, dom_tree, *it, df);
    assert(df.find(*it) != df.end());
    set<cfg_vertex_t> &wset = df[*it];
    for(set<cfg_vertex_t>::const_iterator wi = wset.begin();
	wi != wset.end(); wi++){
      cfg_vertex_t w = *wi;
      if((!u_dom_v(n,w,dom_tree)) || (n == w))
	S.insert(w);
    }
  }
  df.insert(pair<cfg_vertex_t, set<cfg_vertex_t> >(n, S));
}

void print_df(const dom_t &df)
{
  print_debug("ssa", "Dominance frontier");
  print_debug("ssa", "n\t\tDF(N)");
  for(map<cfg_vertex_t, set<cfg_vertex_t> >::const_iterator it =
	df.begin(); it != df.end(); it++){
    const set<cfg_vertex_t> &dfset = it->second;
    ostringstream os;
    for(set<cfg_vertex_t>::const_iterator i2 = dfset.begin();
	i2 != dfset.end(); i2++){
      os << *i2 << ",";
    }
    print_debug("ssa", "%u\t\t{%s}", it->first, os.str().c_str());
  }
}

/// Insert the phi function at the beginning of the block.
void insert_phi(ir_bb_t *block, const string name,
		const reg_t reg, const cfg_t &cfg)
{
  set<cfg_vertex_t> pred = get_preds(block->cfg_num, cfg);
  unsigned size = pred.size();
  vector<Temp *> temps;
  for(unsigned i = 0; i < size; i++){
    temps.push_back(new Temp(reg,name));
  }
  Phi *phi = new Phi(name, temps);
  Temp *t = new Temp(reg,name);
  Move *m = new Move(t, phi);
  // Insert phi function after label.
  vector<Stmt *>::iterator it;
  for(it = block->stmts.begin(); it != block->stmts.end(); it++){
    Stmt *s = *it;
    if(s->stmt_type != LABEL)
      break;
  }
  block->stmts.insert(it, m);
  print_debug("ssa", "Inserting phi node of degree %d in block %u for %s",
	      size, block->cfg_num, name.c_str());

}



void function_to_ssa(ir_function_t *f, const cfg_vertex_t entry_id,
		     const cfg_vertex_t exit_id)
{
  cfg_t dom_tree = build_dominator_tree_fast(f->cfg,
					     entry_id,
					     exit_id);

  if(is_debug_on("ssa")){
    cout << "Dominator tree" << endl;
    print_cfg(dom_tree);
  }
  // compute dominance frontier
  dom_t df;
  compute_df(f->cfg, dom_tree, entry_id, df);
  if(is_debug_on("ssa")){
    print_df(df);
  }

  // Calculate def/use information and blockmaps
  map<string, set<cfg_vertex_t> > defsites;
  DefUseVisitor duv;
  map<cfg_vertex_t, set<string> > Aorig;

  duv.compute(f);
  Aorig = duv.get_cfg_defmap();
  set<string> allvars = duv.get_all_vars();
  for(set<string>::const_iterator it = allvars.begin();
      it != allvars.end(); it++){
    defsites[*it] = duv.get_def2cfg(*it);
  }

  // compute where phi functions need inserting and insert them.
  // Phi-functions are inserted at nodes that satisfy the dominance
  // frontier criterion: Whenever a node x contains a definition of
  // some variable a, then any node z in the dominance frontier of x
  // needs a phi-function for a.

  map<string, set<cfg_vertex_t> > Aphi;

  for(set<string>::const_iterator it = allvars.begin();
      it != allvars.end(); it++){
    string a = *it;
    if(Aphi.find(a) == Aphi.end())
      Aphi[a] = set<cfg_vertex_t>();
    stack<cfg_vertex_t> W;
    for(set<cfg_vertex_t>::const_iterator ti = defsites[a].begin();
	ti != defsites[a].end(); ti++){
      print_debug("ssa", "Defsite for %s: %u",
		  a.c_str(), *ti);
      W.push(*ti);
    }
    while(!W.empty()){
      cfg_vertex_t n = W.top(); W.pop();
      //      assert(df.find(n) != df.end());
      set<cfg_vertex_t> &yset = df[n];
      for(set<cfg_vertex_t>::const_iterator yi = yset.begin();
	  yi != yset.end(); yi++){
	cfg_vertex_t y = *yi;
	if(Aphi[a].find(y) == Aphi[a].end()){
	  insert_phi(f->blockmap[y], a, duv.get_type(a), f->cfg);
	  Aphi[a].insert(y);
	  if(defsites[a].find(y) == defsites[a].end()){
	    defsites[a].insert(y);
	    W.push(y);
	  }
	}
      }
    }
  }

  // Rename variables. We do this following alg 19.7 in Appel.
  SSARenameVisitor ssarename(f, dom_tree,  defsites);
  ssarename.rename(entry_id);
}

SSARenameVisitor::SSARenameVisitor(ir_function_t *inf, 
				   const cfg_t &dom_tree,
				 const map<string, set<cfg_vertex_t> >
				   & defsites)
  : f(inf), dom_tree(dom_tree)
{
//   for(set<string>::const_iterator it = vars.begin();
//       it != vars.end(); it++){
//     count[*it] = 0;
//     varstack[*it].push(0);
//   }
  for(map<string, set<cfg_vertex_t> >::const_iterator it = 
	defsites.begin(); it != defsites.end(); it++){
    count[it->first] = 0;
    varstack[it->first].push(0);
    for(set<cfg_vertex_t>::const_iterator i2 = it->second.begin();
	i2 != it->second.end(); i2++){
      node_defs[*i2].insert(it->first);
    }
  }

  rename_definition = false;
  update_phi = false;
}

void
SSARenameVisitor::rename(const cfg_vertex_t n)
{
  assert(f->blockmap.find(n) != f->blockmap.end());
  ir_bb_t *block = f->blockmap[n];
  for(vector<Stmt *>::const_iterator it = block->stmts.begin();
      it != block->stmts.end(); it++){
    Stmt *s = *it;
    update_phi = false;
    s->accept(this);
  }
  update_phi = true;
  set<cfg_vertex_t> succ = get_succs(n, f->cfg);
  for(set<cfg_vertex_t>::const_iterator it = succ.begin();
      it != succ.end(); it++){
    cfg_vertex_t y = *it;
    set<cfg_vertex_t> pred = get_preds(y, f->cfg);
    unsigned pred_cntr = 0;
    unsigned pred_position = 0;
    for(set<cfg_vertex_t>::const_iterator i2 = pred.begin();
	i2 != pred.end(); i2++){
      if(*i2 == n){
	pred_position = pred_cntr;
	break;
      }
      pred_cntr++;
    }
    rename_position = pred_position;
    ir_bb_t *blk = f->blockmap[y];
    for(vector<Stmt *>::const_iterator bit = blk->stmts.begin();
	bit != blk->stmts.end(); bit++){
      Stmt *s = *bit;
      s->accept(this);
    }
  }
  update_phi = false;
  succ = get_succs(n, dom_tree);
  for(set<cfg_vertex_t>::const_iterator it = succ.begin();
      it != succ.end(); it++){
    this->rename(*it);
  }
  for(set<string>::const_iterator it = node_defs[n].begin();
      it != node_defs[n].end(); it++){
    varstack[*it].pop();
  }
}



void SSARenameVisitor::visitMove(Move *m)
{
  rename_definition=false;
  m->rhs->accept(this);
  rename_definition=true;
  m->lhs->accept(this);
  rename_definition=false;

}


void SSARenameVisitor::visitPhi(Phi *p)
{
  if(update_phi == false) return;
  if(p->vars.size() < rename_position) return;
  assert(varstack.find(p->phi_name) != varstack.end());
  ostringstream os;
  os << p->phi_name << varstack[p->phi_name].top();
  p->vars[rename_position]->name = os.str();
}

void
SSARenameVisitor::visitTemp(Temp *t)
{
  // If we're just updating phi nodes, don't do anything.
  if(update_phi == true) return;
  ostringstream os;
  cfg_vertex_t i;
  if(rename_definition){
    assert(count.find(t->name) != count.end());
    count[t->name] = count[t->name]+1;
    i = count[t->name];
    varstack[t->name].push(i);
  } else {
    i = varstack[t->name].top();
  }
  os << t->name << i;
  t->name = os.str();
}


