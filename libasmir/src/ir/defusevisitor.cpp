/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "defusevisitor.h"


void DefUseVisitor::compute(const ir_function_t *f)
{
  for(set<ir_bb_t *>::const_iterator it = f->blocks.begin();
      it != f->blocks.end(); it++){
    ir_bb_t *block = *it;
    assert(block != NULL);
    this->compute(block);
  }
}

void DefUseVisitor::compute(const ir_bb_t *block)
{
  for(vector<Stmt *>::const_iterator it = block->stmts.begin();
      it != block->stmts.end(); it++){
    Stmt *s = *it;
    assert(s != NULL);
    s->accept(this);
    cfg_defmap[block->cfg_num].insert(stmt_defmap[s].begin(),
				      stmt_defmap[s].end());
    cfg_usemap[block->cfg_num].insert(stmt_usemap[s].begin(),
				      stmt_usemap[s].end());
  }
}

void DefUseVisitor::compute(Stmt *s)
{
  assert(s);
  s->accept(this);
}


void DefUseVisitor::clear()
{
  stmt_defmap.clear();
  stmt_usemap.clear();
  cfg_defmap.clear();
  cfg_usemap.clear();
  name2register.clear();
  refset.clear();
}

set<cfg_vertex_t> DefUseVisitor::get_def2cfg(const string name)
{
  set<cfg_vertex_t> verts;
  for(map<cfg_vertex_t, set<string> >::const_iterator it =
	cfg_defmap.begin(); it != cfg_defmap.end(); it++){
    const set<string> &v = it->second;
    if(v.find(name) != v.end())
      verts.insert(it->first);
  }   
  return verts;
}

set<cfg_vertex_t> DefUseVisitor::get_use2cfg(const string name)
{
  set<cfg_vertex_t> verts;
  for(map<cfg_vertex_t, set<string> >::const_iterator it =
	cfg_usemap.begin(); it != cfg_usemap.end(); it++){
    const set<string> &v = it->second;
    if(v.find(name) != v.end())
      verts.insert(it->first);
  }   
  return verts;
}


set<Stmt *> DefUseVisitor::get_use2stmt(const string name)
{
  set<Stmt *> ret;
  for(map<Stmt *, set<string> >::const_iterator it = 
	stmt_usemap.begin(); it != stmt_usemap.end(); it++){
    Stmt *s = it->first;
    const set<string > &uses = it->second;
    if(uses.find(name) != uses.end())
      ret.insert(s);
  }
  return ret;
}

set<Stmt *> DefUseVisitor::get_def2stmt(const string name)
{
  set<Stmt *> ret;
  for(map<Stmt *, set<string> >::const_iterator it = 
	stmt_defmap.begin(); it != stmt_defmap.end(); it++){
    Stmt *s = it->first;
    const set<string > &defs = it->second;
    if(defs.find(name) != defs.end())
      ret.insert(s);
  }
  return ret;  
}



set<string> DefUseVisitor::get_cfg_defs(const cfg_vertex_t &v)
{
  if(cfg_defmap.find(v) == cfg_defmap.end())
    return set<string>();
  return cfg_defmap.find(v)->second;
}

set<string> DefUseVisitor::get_cfg_uses(const cfg_vertex_t &v)
{
  if(cfg_usemap.find(v) == cfg_usemap.end())
    return set<string>();
  return cfg_usemap.find(v)->second;
}

set<string> DefUseVisitor::get_stmt_defs(Stmt *s)
{
  if(stmt_defmap.find(s) == stmt_defmap.end())
    return set<string>();
  return stmt_defmap.find(s)->second;
}

set<string> DefUseVisitor::get_stmt_uses( Stmt *s)
{
  if(stmt_usemap.find(s) == stmt_usemap.end())
    return set<string>();
  return stmt_usemap.find(s)->second;
}



set<string> DefUseVisitor::get_bb_vars(const cfg_vertex_t &v)
{
  set<string> ret;
  if(cfg_usemap.find(v) != cfg_usemap.end())
    ret.insert(cfg_usemap[v].begin(), cfg_usemap[v].end());
  if(cfg_defmap.find(v) != cfg_defmap.end())
    ret.insert(cfg_defmap[v].begin(), cfg_defmap[v].end());

  return ret;
}

set<string> DefUseVisitor::get_all_vars()
{
  set<string> ret;
  for(map<string, reg_t>::const_iterator it = 
	name2register.begin(); it != name2register.end(); it++){
    ret.insert(it->first);
  }
  return ret;
}

map<Stmt *, set<string> > DefUseVisitor::get_stmt_defmap()
{  return stmt_defmap; }

map<Stmt *, set<string> > DefUseVisitor::get_stmt_usemap()
{ return stmt_usemap; }



map<cfg_vertex_t, set<string> > DefUseVisitor::get_cfg_defmap()
{
  return cfg_defmap;
}

map<cfg_vertex_t, set<string> > DefUseVisitor::get_cfg_usemap()
{
  return cfg_usemap;
}


map<string, reg_t> DefUseVisitor::get_name2register()
{
  return name2register;
}

reg_t DefUseVisitor::get_type(const string name)
{
  assert(name2register.find(name) != name2register.end());
  return name2register.find(name)->second;
}



void DefUseVisitor::visitTemp(Temp *t)
{
  refset.insert(t->name);
  // This is a safety check.  name2type contains the type of a Temp
  // name.  It is concievable that someone will have broken analysis
  // that causes a Temp to have the same name, but different types.
  // This check should catch this.
  reg_t tw;
  if(name2register.find(t->name) != name2register.end()){
    tw = name2register.find(t->name)->second;
    //JIM
    //    assert(tw.kind == t->typ.kind); 
    //    assert(tw.width == t->typ.width);
    if(tw != t->typ){
      cerr << "Temp " << t->name << " used with different types!" << endl;
      cerr << "\tuse1: " << Exp::string_type(tw) << endl;
      cerr << "\tuse2: " << Exp::string_type(t->typ) << endl;
      assert(0);
    }
  } else {
    tw = t->typ;
  }
  name2register.insert(pair<string, reg_t>(t->name, tw));
}


void DefUseVisitor::visitSpecial(Special *s)
{
  if(s->special == "halt")
    return; // Do nothing
  // visitSpecial should return the set of defined and killed
  // registers eventually. For now, just issue a warning.
  print_debug("warning", 
	      "defusevisitor is not defined for Special %s yet"
	      " def/kill sets may be wrong in subsequent analysis",
	      s->special.c_str());
}


void DefUseVisitor::visitCJmp(CJmp *j)
{
  refset.clear();
  j->cond->accept(this);
  j->t_target->accept(this);
  j->f_target->accept(this);
  stmt_usemap[j].insert(refset.begin(), refset.end());
  refset.clear();
}



void DefUseVisitor::visitJmp(Jmp *j)
{
  j->target->accept(this);
  stmt_usemap[j].insert(refset.begin(), refset.end());
  refset.clear();
}

void DefUseVisitor::visitMove(Move *m)
{
  refset.clear();
  m->lhs->accept(this);
  if(m->lhs->exp_type == TEMP){
    stmt_defmap[m].insert(refset.begin(), refset.end());
  }
  refset.clear();
  m->rhs->accept(this);
  stmt_usemap[m].insert(refset.begin(), refset.end());
  refset.clear();
}


void DefUseVisitor::visitExpStmt(ExpStmt *e)
{
  refset.clear();
  e->exp->accept(this);
  stmt_usemap[e].insert(refset.begin(), refset.end());
  refset.clear();
}


