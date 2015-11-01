/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "irdeendianizer.h"


vector<Exp*> IRDeEndianizer::split_mem(Mem *mem, int size)
{
  vector<Exp*> exps;
  exps.reserve(size);

  Exp *addr = mem->addr;

  int i,inc,stop;
  if (endian == ENDIAN_LITTLE) {
    i = 0;
    inc = 1;
    stop = size;
  } else {
    i = size-1;
    stop = inc = -1;
  }

  for (; i != stop; i += inc) {
    const_val_t x;
    x = (uint64_t)i;
    Exp *myaddr;
    if (i)
      myaddr = new BinOp(PLUS, addr->clone(),
			 new Constant(REG_ADDRESS_T, x) );
    else
      myaddr = addr->clone(); // don't add 0...

    exps.push_back(new Mem(myaddr, width));
  }

  return exps;
}


void IRDeEndianizer::visitBlock(ir_bb_t *b)
{
  visitvectorStmt(&b->stmts);
}


void IRDeEndianizer::visitvectorStmt(vector<Stmt*> *stmts)
{
  IRVisitor *vis = dynamic_cast<IRVisitor*>(this);
  for(vector<Stmt*>::const_iterator i = stmts->begin();
      i != stmts->end(); i++) {

    print_debug("deend", "%s", (*i)->tostring().c_str());
    int new_stmts_size = new_stmts.size();
    // visitMove will copy/mutate moves, the rest we must copy here
    // to avoid doing it separately for each Stmt type
    // We still call the accept method, because the Exps inside other Stmts
    // need changing.
    if ((*i)->stmt_type != MOVE) {
      (*i)->accept(vis);
      new_stmts.push_back(*i);
    } else {
      (*i)->accept(vis);
    }

    for(unsigned j=new_stmts_size; j<new_stmts.size(); j++) {
      print_debug("deend", "--> %s", new_stmts[j]->tostring().c_str());
    }

  }
  // and finally replace the old bits with the new ones
  *stmts = new_stmts;

}


string mk_tempname( string base)
{
    static int temp_counter = 0;
    return base + "_" + int_to_str(temp_counter++);
}


void IRDeEndianizer::visitMove(Move *mov)
{
  // Copied from IRChangeVisitor::visitMove and modified :(
  {
    Exp *o;
    if (mov->lhs->exp_type != MEM) {
      o = mov->lhs;
      mov->lhs->accept(this);
      if(o != ret){
	Exp::destroy(o);
      }
      mov->lhs = ret;
    }
    else {
      IRChangeVisitor::visitMem((Mem*)mov->lhs); // only visit the address part
      // JIM: something seems wrong here
    }

    o = mov->rhs;
    mov->rhs->accept(this);
    if(o != ret){
      Exp::destroy(o);
    }
    mov->rhs = ret;
  }
  // end Copied from IRChangeVisitor::visitMove

  if (mov->lhs->exp_type != MEM || ((Mem*)mov->lhs)->typ == width) {
    // keep as is
    new_stmts.push_back(mov);
    ret = (Exp*)mov;
    return;
  }
  
  Mem *mem = (Mem*)mov->lhs;

  // FIXME: floats should be reinterpreted as ints before casting to bytes

  Temp tmp(mem->typ, mk_tempname("T_m"));
  new_stmts.push_back(new VarDecl(tmp.name, tmp.typ));
  new_stmts.push_back(new Move(new Temp(tmp), mov->rhs->clone(), mov->asm_address));

  vector<Exp*> exps;

  switch (mem->typ) { // the low half
  case REG_64: {
      Exp *lowmid = new Cast(new Cast(new Temp(tmp), REG_32, CAST_LOW),
			     REG_16, CAST_HIGH );
      exps.insert(exps.begin(), new Cast(lowmid, width, CAST_HIGH));
      exps.insert(exps.begin(), new Cast(lowmid->clone(), width, CAST_LOW));
  }
  case REG_32:
    exps.insert(exps.begin(),
		new Cast(new Cast(new Temp(tmp), REG_16, CAST_LOW),
			 width, CAST_HIGH ) );
  case REG_16:
    exps.insert(exps.begin(), new Cast(new Temp(tmp), width, CAST_LOW));
    break;;
  case REG_1:
  case REG_8:
    // FIXME: umm, what's the proper thing to do here?
    assert(0);
    exps.push_back(new Cast(new Temp(tmp), width, CAST_UNSIGNED));
  }

  switch (mem->typ) { // the high half
  case REG_64: {
    Exp *himid = new Cast(new Cast(new Temp(tmp), REG_32, CAST_HIGH),
			  REG_16, CAST_LOW );
    exps.push_back(new Cast(himid, width, CAST_LOW));
    exps.push_back(new Cast(himid->clone(), width, CAST_HIGH));
  }
  case REG_32:
    exps.push_back(new Cast(new Cast(new Temp(tmp), REG_16, CAST_HIGH),
			    width, CAST_LOW));
  case REG_16:
    exps.push_back(new Cast(new Temp(tmp), width, CAST_HIGH));
  default:
    break;;
  }
  
  vector<Exp*> mems = split_mem(mem, reg_width_to_size(mem->typ));
  vector<Exp*>::iterator ei = exps.begin();
  for (vector<Exp*>::iterator mi=mems.begin(); mi != mems.end(); mi++, ei++) {
    new_stmts.push_back(new Move(*mi, *ei, mov->asm_address ));
  }


  // Note that because the old pointers will be dropped on the floor,
  // any Stmt that we don't add to new_stmts should be freed now.
  Move::destroy(mov);

  ret = (Exp*)mov; // A sequence Stmt type would be nice here
  return;
}


void IRDeEndianizer::visitMem(Mem *mem)
{
  IRChangeVisitor::visitMem(mem);

  if (mem->typ == width)
    return;

  ret = NULL;
  int i = 0;
  vector<Exp*> mems = split_mem(mem, reg_width_to_size(mem->typ));
  for (vector<Exp*>::iterator mi=mems.begin(); mi != mems.end(); mi++, i++) {
    const_val_t shift;
    shift = (uint64_t)i*8;
    Exp *byte = new BinOp(LSHIFT,
			  new Cast(*mi, mem->typ, CAST_UNSIGNED),
			  new Constant(mem->typ, shift));
    
    if (ret)
      ret = new BinOp(BITOR, byte, ret);
    else
      ret = byte;
  }
}

