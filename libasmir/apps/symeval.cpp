/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include <stmt.h>
#include <exp.h>
#include <irvisitor.h>
#include <queue>
#include <assert.h>
#include "symeval.h"

using namespace std;


bool
SymEval::execute(const vector<Stmt *> stmts, Exp *&ret)
{
  Exp *exp;
  
  for(vector<Stmt *>::const_iterator it = stmts.begin();
      it != stmts.end(); it++){
    q.push(*it);
  }

  while(!q.empty()){
    Stmt *s = q.front();
    print_debug("symeval", "Executing %s", s->tostring().c_str());
    q.pop();
    CJmp *cj;
    switch(s->stmt_type){
    case JMP:
      assert(1 == 0); // Shouldn't happen
      break;
    case SPECIAL:
      print_debug("symeval", 
		  "%s", s->tostring().c_str());
      break;
    case CJMP:
      cj = (CJmp *)s;
      exp = cj->cond->clone();
      exp->accept(this);
      ret = exp;
      return true;
      break;
    default:
      s->accept(this); break;
    }
  }
  return false;
}

void 
SymEval::visitTemp(Temp *t)
{

  if(regstate.find(t->name) != regstate.end()){
    ret = regstate.find(t->name)->second->clone();
  } else {
    ret = t;
  }
}

void
SymEval::visitMove(Move *m)
{
  m->rhs->accept(this);

  m->lhs->accept(this);

  if(m->lhs->exp_type == TEMP){
    Temp *t = (Temp *)m->lhs;
    regstate[t->name] = m->rhs;
  } else {
    memstate[m->lhs] = m->rhs;
  }

  if(is_debug_on("interpret")){
    print_debug("interpret",
		"%s = %s", m->lhs->tostring().c_str(), 
		m->rhs->tostring().c_str());
  }
}


int main()
{
  debug_on("interpret");

  vector<Stmt *> stmts;
  // a = a + b;
  Stmt *s = new Move(new Temp(REG_32, "a"),
		     new BinOp(PLUS, 
			       new Temp(REG_32, "a"),
			       new Temp(REG_32, "b")));
  stmts.push_back(s);
  // b = b + c;
  s = new Move(new Temp(REG_32, "b"),
	       new BinOp(PLUS, 
			 new Temp(REG_32, "b"),
			 new Temp(REG_32, "c")));
  
  stmts.push_back(s);
  // a = a + b
  s = new Move(new Temp(REG_32, "a"),
	       new BinOp(PLUS, 
			 new Temp(REG_32, "a"),
			 new Temp(REG_32, "a")));
  stmts.push_back(s);
  // a = b + b
  s = new Move(new Temp(REG_32, "a"),
	       new BinOp(PLUS, 
			 new Temp(REG_32, "b"),
			 new Temp(REG_32, "a")));
  stmts.push_back(s);

  CJmp *cj = new CJmp(new BinOp(EQ, 
				new Temp(REG_32, "a"),
				new Constant(REG_32, 1)),
		      new Name("t_branch"),
		      new Name("f_branch"));
  stmts.push_back(cj);
				
  SymEval interpreter;
  Exp *query;
  bool ret = interpreter.execute(stmts, query);
  if(ret){
    print_debug("interpret", "final: %s", query->tostring().c_str());
  }
  return 0;
}
