/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include <iostream>
#include "typecheck_ir.h"

//#define THROW_ERROR(s) do {printf(s); return -1; } while(0)
#define THROW_ERROR(s) throw TypeError(s)


int typecheck_exp(reg_t *t,
		  const map<string,reg_t> *g,
		  const Exp *e)
{
  // Note: t should be assigned to before comparing to e.typ so that
  // this function can be used to infer the type of e in the first place
  switch (e->exp_type) {
  case CONSTANT:
    *t =((Constant*)e)->typ;
    return 0;
  case BINOP: {
    BinOp *b = (BinOp*)e;
    reg_t r;
    if (typecheck_exp(t, g, b->lhs) < 0)
      THROW_ERROR("lhs of binop failed to typecheck\n");
    if (typecheck_exp(&r, g, b->rhs) < 0)
      THROW_ERROR("rhs of binop failed to typecheck\n");

    switch (b->binop_type) {
    case PLUS:
    case MINUS:
    case TIMES:
    case DIVIDE:
    case SDIVIDE:
    case MOD:
    case BITAND:
    case BITOR:
    case XOR:
      if(r != *t)
	THROW_ERROR("lhs and rhs of binop are different types/sizes ("+e->tostring()+")");
    // these should maybe have differently sized rhs operands
    case LSHIFT:
    case RSHIFT:
    case ARSHIFT:
    case LROTATE:
    case RROTATE:
      break;;
    case LOGICAND:
    case LOGICOR:
    case EQ:
    case NEQ:
    case GT:
    case LT:
    case GE:
    case LE:
      if(r != *t)
	THROW_ERROR("lhs and rhs of comparison are different types/sizes\n");
      *t = REG_1;
      break;;
    default:
      THROW_ERROR("unknown type of BinOp\n");
    }

    return 0;
  }
  case UNOP: {
    UnOp *u = (UnOp*)e;
    return typecheck_exp(t, g, u->exp);
  }
  case MEM: {
    Mem *m = (Mem*)e;
    reg_t addr_type;
    if (typecheck_exp(&addr_type, g, m->addr) < 0)
      return -1; // FIXME: also check the address is of the right type
    *t = m->typ;
    return 0;
  }
  case TEMP: {
    Temp *v = (Temp*)e;
    *t = v->typ;
    if (g) {
      map<string,reg_t>::const_iterator t2 = g->find(v->name);
      if (t2 == g->end()) {
	cout <<"unknown temp var '" <<v->name <<"'\n";
	// FIXME: temp vars are used for  registers, before assigining to them
	// so we don't know if this is actually an error
	return 0;
      }
      if(t2->second != v->typ)
	THROW_ERROR("temp var referenced with different type than saved\n");
    }
    return 0;
  }
  case CAST: {
    Cast *c = (Cast*)e;
    if (typecheck_exp(t, g, c->exp) < 0)
      return -1;

    switch (c->cast_type) {
    case CAST_HIGH:
    case CAST_LOW:
      if(Exp::reg_to_bits(*t) <= Exp::reg_to_bits(c->typ))
	THROW_ERROR("Narrowing cast to a wider type");
      *t = c->typ;
      return 0;
    case CAST_UNSIGNED:
    case CAST_SIGNED:
      if(Exp::reg_to_bits(*t) >= Exp::reg_to_bits(c->typ))
	THROW_ERROR("Widening cast to a narrower size");
      *t = c->typ;
      return 0;

    case CAST_FLOAT:
    case CAST_RFLOAT:
      THROW_ERROR("CAST_(R)FLOAT: Floats not currently handled\n");
//       if (t->kind == REG_FLOAT)
// 	THROW_ERROR("CAST_(R)FLOAT from "+Exp::string_type(*t)+"\n");
//       if(t->width != c->width)
// 	THROW_ERROR("CAST_(R)FLOAT from different size");
//       t->kind = REG_FLOAT;
      return 0;
    case CAST_INTEGER:
    case CAST_RINTEGER:
      THROW_ERROR("CAST_(R)INTEGER: Floats not currently handled\n");
//       // FIXME: assuming this casts to a signed
//       if (t->kind != REG_FLOAT)
// 	THROW_ERROR("CAST_(R)INTEGER from "+Exp::string_type(*t)+"");
//       if (t->width != c->width)
// 	THROW_ERROR("CAST_(R)INTEGER from different size");
//       t->kind = REG_SIGNED;
      return 0;
    }
    THROW_ERROR("Unknown type of cast");
  }
  case NAME:
    *t = REG_ADDRESS_T;
    return 0;

  case PHI: {
    Phi *p = (Phi*)e;
    unsigned int i;
    for (i=0; i < p->vars.size(); i++) {
      reg_t t2;
      if (typecheck_exp(i?&t2:t, g, p->vars[i]) < 0)
	THROW_ERROR("typechecking var in phi expression failed\n");
      if (i && ( (*t) != t2))
	THROW_ERROR("variable in phi expression has different type\n");
    }
    if (!i)
      THROW_ERROR("empty phi expression\n");
    return -!i;
  }
  case UNKNOWN:
  default:
    return -1;
  }  
}



int typecheck_stmt(map<string,reg_t> *g, Stmt *s) {
  reg_t t;
  VarDecl *vd;
  switch (s->stmt_type) {
  case VARDECL:
    vd = (VarDecl *)s;
    if(g->find(vd->name) != g->end()){
      THROW_ERROR("variable redeclaration");
    }
    g->insert(pair<string, reg_t>(vd->name, vd->typ));
    return 0;
  case JMP:
    // FIXME: for now all types are valid addresses
    return typecheck_exp(&t, g, ((Jmp*)s)->target);

  case CJMP: {
    CJmp *c = (CJmp*)s;
    if (typecheck_exp(&t, g, c->cond) < 0)
      THROW_ERROR("condition failed to typecheck\n");
    if(t != REG_1)
      THROW_ERROR("condition is not a boolean\n");
    if (typecheck_exp(&t, g, c->t_target) < 0
	|| typecheck_exp(&t, g, c->f_target) < 0)
      return -1;
    return 0;
  }    
  case MOVE: {
    Move *m = (Move*)s;
    reg_t t2;
    // so that we can update the context to avoid finding unknown vars later
    int retval = 0;
    if (typecheck_exp(&t, g, m->rhs) < 0) {
      THROW_ERROR("rhs of assignment fails to typecheck\n");
      retval = -1;
    }
    if (m->lhs->exp_type == TEMP) {
      // assigning a new variable
      Temp *v = (Temp*)m->lhs;
      if (g)
	(*g)[v->name] = v->typ;
      t2 = v->typ;
    }
    else { //assigning to memory
      if (m->lhs->exp_type != MEM)
	THROW_ERROR("LHS of assignment is not memory or temp\n");
      if (typecheck_exp(&t2, g, m->lhs) < 0) {
	THROW_ERROR("lhs of assignment fails to typecheck\n");
	return -1;
      }
    }
    if (retval)
      return retval;
    if(t != t2) {
      THROW_ERROR("implicit type cast in assignment\n");
      return -1;
    }
    return 0;
  }
  case EXPSTMT:
    // ExpStmts are just tossed around for convenience. I'm not sure why
    // they are part of the language itself.
    // They have no meaning, so there is no need to check them.
  case SPECIAL:
  case COMMENT:
  case LABEL: return 0;
  case CALL: // FIXME: no typechecking on calls for now.
    return 0;
  case ASSERT: {
    Assert *a = (Assert*)s;
    if (typecheck_exp(&t, g, a->cond) < 0)
      THROW_ERROR("assert condition failed to typecheck\n");
    if(t != REG_1)
      THROW_ERROR("assert condition is not a boolean\n");
    return 0;
  }
  }
  THROW_ERROR("encountered unknown type of statement\n");
  return -1;
}
