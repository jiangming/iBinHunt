/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "deadcode.h"

static void remove_dead_code(ir_function_t *f, set<Stmt *> &s);

void ssa_deadcode_elimination(ir_program_t *p)
{
  for(set<ir_function_t *>::const_iterator it = p->functions.begin();
      it != p->functions.end(); it++){
    ssa_deadcode_elimination(*it);
  }
}

void ssa_deadcode_elimination(ir_function_t *f)
{
  set<Stmt *> dead_stmts;
  map<string, set<Stmt *> > usemap;
  map<string, Stmt *> defmap;
  DefUseVisitor duv;

  duv.compute(f);
  // Get a list of all variable names;
  set<string> worklist = duv.get_all_vars();


  for(set<string>::const_iterator it = worklist.begin();
      it != worklist.end(); it++){
    usemap[*it] = duv.get_use2stmt(*it);
    set<Stmt *> stmts = duv.get_def2stmt(*it);
    /// The code should be in SSA form such that each
    /// variable name is only defined once.
    assert(stmts.size() < 2);
    if(stmts.size() == 1)
      defmap[*it] = *(stmts.begin());
  }

  set<string>::iterator it;
  while(!worklist.empty()){
    it = worklist.begin();
    string v = *it;
    worklist.erase(*it);
    if(usemap.find(*it) == usemap.end() ||
       usemap[*it].size() == 0){
      if(defmap.find(*it) != defmap.end()){
	Stmt *s = defmap.find(*it)->second;
	dead_stmts.insert(s);
	set<string> used_by_s = duv.get_stmt_uses(s);
	for(set<string>::const_iterator i2 = used_by_s.begin();
	    i2 != used_by_s.end(); i2++){
	  if(usemap[*i2].find(s) != usemap[*i2].end())
	    usemap[*i2].erase(usemap[*i2].find(s));
	  worklist.insert(*i2);
	}
      }
    }
  }
  remove_dead_code(f,dead_stmts);


}


void remove_dead_code(ir_function_t *f, set<Stmt *> &dead)
{
  if(dead.size() == 0) return;
  for(set<ir_bb_t *>::const_iterator bit = f->blocks.begin();
      bit != f->blocks.end(); bit++){
    ir_bb_t *block = *bit;
    if(dead.size() == 0)
      return;
    for(vector<Stmt *>::iterator sit = block->stmts.begin();
	sit != block->stmts.end(); sit++){
      Stmt *s = *sit;
      if(dead.find(s) != dead.end()){
	print_debug("deadcode", "Removing dead stmt: %s", 
		    s->tostring().c_str());
	block->stmts.erase(sit);
	dead.erase(s);
      }
    }
  }

  /// Note: we should delete all dead statements. If there is a
  /// dead statement left in the dead set, then we didn't find it
  /// in the function. But this shouldn't happen, since we 
  /// should only consider statements in the function!
  assert(dead.size() == 0);
}

