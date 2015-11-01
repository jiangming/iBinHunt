/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "irvisitor.h"
#include "exp.h"
#include "stmt.h"




void DefaultIRVisitor::visitBinOp(BinOp *b)
{ 
  b->lhs->accept(this); 
  b->rhs->accept(this);
}

void DefaultIRVisitor::visitUnOp(UnOp *u)
{
  u->exp->accept(this);
}
void DefaultIRVisitor::visitConstant(Constant *c)
{
}

void DefaultIRVisitor::visitTemp(Temp *t)
{
}

void DefaultIRVisitor::visitPhi(Phi *p)
{
  for(vector<Temp *>::const_iterator it = p->vars.begin();
      it != p->vars.end(); it++){
    Temp *e = *it;
    e->accept(this);
  }
}

void DefaultIRVisitor::visitSpecial(Special *s)
{
}

void DefaultIRVisitor::visitMem(Mem *m)
{
  m->addr->accept(this);
}

void DefaultIRVisitor::visitUnknown(Unknown *u)
{
}

void DefaultIRVisitor::visitCast(Cast *c)
{
  c->exp->accept(this);
}

void DefaultIRVisitor::visitName(Name *n)
{
}

void DefaultIRVisitor::visitJmp(Jmp *j)
{
  j->target->accept(this);
}

void DefaultIRVisitor::visitCJmp(CJmp *c)
{
  c->cond->accept(this);
  c->t_target->accept(this);
  c->f_target->accept(this);
}



void DefaultIRVisitor::visitLabel(Label *l)
{
}

void DefaultIRVisitor::visitMove(Move *m)
{
  m->lhs->accept(this);
  m->rhs->accept(this);
}

void DefaultIRVisitor::visitComment(Comment *c)
{}

void DefaultIRVisitor::visitExpStmt(ExpStmt *c)
{
  c->exp->accept(this);
}


void DefaultIRVisitor::visitVarDecl(VarDecl *v)
{
}

void DefaultIRVisitor::visitLet(Let *l)
{
  l->var->accept(this);
  l->exp->accept(this);
  l->in->accept(this);
}

void DefaultIRVisitor::visitCall(Call *c)
{
  if (c->lval_opt != NULL)
    c->lval_opt->accept(this);
  for(vector<Exp*>::iterator 
        i=c->params.begin(); i!=c->params.end(); i++)
    (*i)->accept(this);
}

void DefaultIRVisitor::visitReturn(Return *r)
{
  if (r->exp_opt != NULL)
    r->exp_opt->accept(this);
}

void DefaultIRVisitor::visitFunc(Func *f)
{
  for(vector<VarDecl*>::iterator 
        i=f->params.begin(); i!=f->params.end(); i++)
    (*i)->accept(this);
  for(vector<Stmt*>::iterator 
        i=f->body.begin(); i!=f->body.end(); f++) {
    (*i)->accept(this);
  }
}

void DefaultIRVisitor::visitAssert(Assert *a)
{
  a->cond->accept(this);
}

void IRChangeVisitor::visitBinOp(BinOp *b)
{
  Exp *o = b->lhs;
  ret = o;
  b->lhs->accept(this);
  if(ret != o){
    Exp::destroy(o);
  }
  b->lhs = ret;
  o = b->rhs;
  ret = o;
  b->rhs->accept(this);
  if(ret != o){
    Exp::destroy(o);
  }
  b->rhs = ret;
  ret = b;
}

void IRChangeVisitor::visitUnOp(UnOp *u)
{
  Exp *o = u->exp;
  ret = o;
  u->exp->accept(this);

  if(ret != o){
    Exp::destroy(o);
  }
  u->exp = ret;
  ret = u;
}

void IRChangeVisitor::visitConstant(Constant *c)
{ret = c;}

void IRChangeVisitor::visitTemp(Temp *t)
{ret = t;}
void IRChangeVisitor::visitPhi(Phi *p)
{
  Exp *o;
  unsigned size = p->vars.size();
  for(unsigned i =0; i < size; i++){
    o = p->vars[i];
    ret = o;
    p->vars[i]->accept(this);
    if(ret != o){
      Exp::destroy(o);
    }
    p->vars[i] = (Temp *) ret;
  }
  ret = p;
}


void IRChangeVisitor::visitMem(Mem *m)
{
  Exp *o;
  o = m->addr;
  m->addr->accept(this);
  if(ret != o){
    Exp::destroy(o);
  }
  m->addr = ret;
  ret = m;
}

void IRChangeVisitor::visitUnknown(Unknown *u)
{ret = u;}

void IRChangeVisitor::visitCast(Cast *c)
{
  Exp *o;
  o = c->exp;
  c->exp->accept(this);
  if(ret != o){
    Exp::destroy(o);
  }
  c->exp = ret;
  ret = c;
}

void IRChangeVisitor::visitName(Name *n)
{ret = n;}

void IRChangeVisitor::visitJmp(Jmp *j)
{
  Exp *o;
  o = j->target;
  j->target->accept(this);
  if(ret != o){
    Exp::destroy(o);
  }
  j->target = ret;
}

void IRChangeVisitor::visitCJmp(CJmp *j)
{
  Exp *o;
  o = j->cond;
  j->cond->accept(this);
  if(o != ret){
    Exp::destroy(o);
  }
  j->cond =ret;

  o = j->t_target;
  j->t_target->accept(this);
  if(o != ret){
    Exp::destroy(o);
  }
  j->t_target =ret;

  o = j->f_target;
  j->f_target->accept(this);
  if(o != ret){
    Exp::destroy(o);
  }
  j->f_target =ret;
}

void IRChangeVisitor::visitLabel(Label *l)
{}

void IRChangeVisitor::visitMove(Move *m)
{
  Exp *o;
  o = m->lhs;
  m->lhs->accept(this);
  if(o != ret){
    Exp::destroy(o);
  }
  m->lhs = ret;

  o = m->rhs;
  m->rhs->accept(this);
  if(o != ret){
    Exp::destroy(o);
  }
  m->rhs = ret;
}

void IRChangeVisitor::visitComment(Comment *c)
{}
void IRChangeVisitor::visitExpStmt(ExpStmt *e)
{
  Exp *o;
  o = e->exp;
  e->exp->accept(this);
  if(o != ret){
    Exp::destroy(o);
  }
  e->exp = ret;
}

void IRChangeVisitor::visitSpecial(Special *s)
{}

void IRChangeVisitor::visitVarDecl(VarDecl *v)
{
}

void IRChangeVisitor::visitLet(Let *l)
{
  l->var->accept(this);
  l->exp->accept(this);
  l->in->accept(this);
}

void IRChangeVisitor::visitCall(Call *c)
{
  if (c->lval_opt != NULL) {
    Exp *o = c->lval_opt;
    c->lval_opt->accept(this);
    if(o != ret)
      Exp::destroy(o);
    c->lval_opt = ret;
  }

  vector<Exp*> new_params;
  for(vector<Exp*>::iterator 
        i=c->params.begin(); i!=c->params.end(); i++) {
    Exp *o = (*i);
    (*i)->accept(this);
    if (o != ret)
      Exp::destroy(o);
    new_params.push_back(ret);
  }
  c->params = new_params;
}

void IRChangeVisitor::visitReturn(Return *r)
{
  if (r->exp_opt != NULL) {
    Exp *o = r->exp_opt;
    r->exp_opt->accept(this);
    if (o != ret)
      Exp::destroy(o);
    r->exp_opt = ret;
  }
}

void IRChangeVisitor::visitFunc(Func *f)
{
  for(vector<VarDecl*>::iterator 
        i=f->params.begin(); i!=f->params.end(); i++) {
    (*i)->accept(this);
  }

  for(vector<Stmt*>::iterator 
        i=f->body.begin(); i!=f->body.end(); f++) {
    (*i)->accept(this);
  }
}

void IRChangeVisitor::visitAssert(Assert *a)
{
  Exp *o = a->cond;
  a->cond->accept(this);
  if (o != ret)
    Exp::destroy(o);
  a->cond = ret;
}
