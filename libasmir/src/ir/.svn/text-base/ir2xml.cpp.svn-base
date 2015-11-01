/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "ir2xml.h"

IR2XML::IR2XML(ostream &o) : depth(0), os(o)
{
}

void IR2XML::xml_prologue()
{
  os <<"<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n"
     <<"<!DOCTYPE vine SYSTEM \"vine.dtd\">\n"
     <<"<vine>\n";
}

void IR2XML::xml_epilogue()
{
  os <<"</vine>\n";
}

void IR2XML::print_depth()
{
  for(unsigned i =0; i < depth; i++)
    os << "  ";
}

void IR2XML::print_reg_type(const reg_t t)
{
  os << "type=\"";
  switch(t){
  case REG_1: os << "REG_1"; break;
  case REG_8: os << "REG_8"; break;
  case REG_16: os << "REG_16"; break;
  case REG_32: os << "REG_32"; break;
  case REG_64: os << "REG_64"; break;
  }
  os << "\"";
}



void IR2XML::visitBinOp(BinOp *b)
{
  print_depth();
  os << "<binop type=\"" << BinOp::optype_to_name(b->binop_type) 
     << "\">" << endl;
  depth++;
  print_depth();
  os << "<!-- LHS -->" << endl;
  b->lhs->accept(this);
  print_depth();
  os << "<!-- RHS -->" << endl;
  b->rhs->accept(this);
  depth--;
  print_depth();
  os << "</binop>" << endl;
}

void IR2XML::visitUnOp(UnOp *o)
{
  print_depth();
  os << "<unop type=\"" << UnOp::optype_to_string(o->unop_type) 
     << "\">" << endl;
  depth++;
  o->exp->accept(this);
  depth--;
  print_depth();
  os << "</unop>" << endl;
}

void IR2XML::visitConstant(Constant *c)
{
  print_depth();
  os << "<constant ";
  print_reg_type(c->typ);
  os << ">0x";
  os << hex << c->val;

  os << "</constant>" << endl;
}

void IR2XML::visitTemp(Temp *t)
{
  print_depth();
  os << "<temp ";
  print_reg_type(t->typ);
  os << ">";
  os << t->name;
  os << "</temp>" << endl;
}

void IR2XML::visitPhi(Phi *p)
{
  print_depth();
  os << "<phi>" << endl;
  for(vector<Temp*>::const_iterator it = p->vars.begin();
      it != p->vars.end(); it++){
    Temp *e = *it;
    e->accept(this);
  }
  print_depth();
  os << "</phi>";
}

void IR2XML::visitSpecial(Special *s)
{
  print_depth();
  os << "<special>" << s->special << "</special>" << endl;
}

void IR2XML::visitMem(Mem *m)
{
  print_depth();
  os << "<mem ";
  print_reg_type(m->typ);
  os << ">" << endl;
  depth++;
  print_depth();
  os << "<!-- Address -->" << endl;
  m->addr->accept(this);
  depth--;
  print_depth();
  os << "</mem>" << endl;
}

void IR2XML::visitUnknown(Unknown *u)
{
  print_depth();
  os << "<unknown>" << u->str << "</unknown>" << endl;
}

void IR2XML::visitCast(Cast *c)
{
  print_depth();
  os << "<cast ";
  print_reg_type(c->typ);
  os << " casttype=\"" << Cast::cast_type_to_string(c->cast_type) << "\">" << endl;
  depth++;
  c->exp->accept(this);
  depth--;
  print_depth();
  os << "</cast>" << endl;
}

void IR2XML::visitName(Name *n)
{
  print_depth();
  os << "<name>"
     << n->name
     << "</name>" << endl;
}

void IR2XML::visitJmp(Jmp *j)
{
  print_depth();
  os << "<jmp>" << endl;
  depth++;
  j->target->accept(this);
  depth--;
  print_depth();
  os << "</jmp>" << endl;
}

void IR2XML::visitCJmp(CJmp *c)
{
  print_depth();
  os << "<cjmp>" << endl;
  depth++;
  c->cond->accept(this);
  print_depth();
  os << "<!-- True target -->" << endl;
  c->t_target->accept(this);
  print_depth();
  os << "<!-- False target -->" << endl;
  c->f_target->accept(this);
  depth--;
  print_depth();
  os << "</cjmp>" << endl;
}


void IR2XML::visitLabel(Label *l)
{
  print_depth();
  os << "<label>" << l->label << "</label>" << endl;
}

void IR2XML::visitMove(Move *m)
{
  print_depth();
  os << "<move>" << endl;
  depth++;
  print_depth();
  os << "<!-- LHS -->" << endl;
  m->lhs->accept(this);
  print_depth();
  os << "<!-- RHS -->" << endl;
  m->rhs->accept(this);
  depth--;
  print_depth();
  os << "</move>" << endl;
}

void IR2XML::visitComment(Comment *c)
{
  // FIXME: escape comment appropriately
  print_depth();
  os << "<comment>" << c->comment << "</comment>" <<  endl;
}

void IR2XML::visitExpStmt(ExpStmt *s)
{
  print_depth();
  os << "<expstmt>" << endl;
  depth++;
  s->exp->accept(this);
  depth--;
  print_depth();
  os << "</expstmt>" << endl;
}

void IR2XML::visitVarDecl(VarDecl *s)
{
  print_depth();
  os << "<vardecl>" << endl;
  depth++;
  os << s->name << ":" << Exp::string_type(s->typ) << endl;
  depth--;
  print_depth();
  os << "</expstmt>" << endl;
}

