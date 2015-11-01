/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "ir_program.h"
#include "disasm-pp.h"

// Our address counter for translated ir statements.
const static address_t ir_addr_base = 100;

/// Add an edge to the cfg. The dst is deduced from the target
/// expression. Called only by ir_build_initial_cfg()
static cfg_edge_t cfg_add_target(cfg_vertex_t src, Exp *target,
				 const map<address_t, ir_bb_t *> &blockmap,
				 const map<string, Label *> &label_map,
				 ir_function_t *f);


/// Build the initial CFG of the IR from the stmts and blocks
static void build_initial_cfg(ir_function_t *f, 
			      const vector<Stmt *> &stmts,
			      const map<string, Label *> &label_map);

/// create initial basic blocks from the stmt list. Label stmts
/// may get inserted when necessary.
static void
build_initial_bb(ir_function_t *f, vector<Stmt *> &stmts,
		  map<string, Label *> &label_map);


ir_program_t *asm_program_to_ir(asm_program_t *asm_p)
{
  ir_program_t *ir_p = new ir_program_t;
  for(map<address_t, asm_function_t *>::const_iterator it =
	asm_p->functions.begin(); it != asm_p->functions.end();
      it++){
    asm_function_t *asmf = it->second;
    ir_function_t *f = asm_function_to_ir(asm_p, asmf);
    ir_p->functions.insert(f);
  }
  return ir_p;
}

struct vine_block_sort{
  bool operator()(vine_block_t* const & a, vine_block_t* const&b){
    return a->inst->address < b->inst->address;
  }
};




map<address_t, vector<Stmt *> >
instruction_to_ir(asm_program_t *prog, vector<Instruction *> &instrs)
{
    translate_init(); 
    map<address_t, vector<Stmt *> > ret;

    vector<vine_block_t *> vine_blocks = generate_vex_ir(prog, instrs);
    
    vine_blocks = generate_vine_ir(prog, vine_blocks);
    for(vector<vine_block_t *>::iterator it = vine_blocks.begin();
	it != vine_blocks.end(); it++){
	vine_block_t *block = *it;
	address_t addr = block->inst->address;
	vector<Stmt *> ir = *(block->vine_ir);
	if(is_debug_on("asm_comments") && block->inst){
	  ostringstream os;
	  ostream_insn(prog, block->inst, os);
	  ir.insert(ir.begin()+1,new Comment(os.str()));
	}
	ret.insert(pair<address_t, vector<Stmt *> >(addr, ir));


#ifdef DEBUGGING
        cout << "   ";
        ostream_insn(prog, block->inst, cout);
	for (int i=0; i<3; i++)
	    printf(" %02X", block->inst->opcode[i]); 
        cout << endl;

	if (block->vex_ir) 
	    ppIRSB(block->vex_ir); 

        vector<Stmt *> *inner = block->vine_ir;

        cout << "  {" << endl;

        for ( int j = 0; j < inner->size(); j++ )
        {
	  Stmt *s = inner->at(j);
	  cout << "     " << s->tostring();
	  cout << endl;

        }
        cout << "  }" << endl;
#endif

	delete block->vine_ir;
	delete block;
	vx_FreeAll();
    }
    
    return ret;
}


vine_block_t* asm_addr_to_ir(asm_program_t *p, address_t addr)
{
  translate_init();
  asm_function_t *f = get_nearest_function(p, addr);
  assert(f);
  assert(f->instmap.find(addr) != f->instmap.end());
  Instruction *inst = f->instmap.find(addr)->second;
  vector<Instruction *> instrs;
  instrs.push_back(inst);
  vector<vine_block_t *> vine_blocks = generate_vex_ir(p, instrs);
  vine_blocks = generate_vine_ir(p, vine_blocks);
  assert(vine_blocks.size() == 1);
  return vine_blocks[0];
}

map<address_t, vector<Stmt *> > 
asm_addrs_to_ir(asm_program_t *p, 
		const vector<address_t> &addrs)
{
  map<address_t, vector<Stmt *> > ret;

  for(vector<address_t>::const_iterator it = addrs.begin();
      it != addrs.end(); it++){
    address_t addr = *it;
    vine_block_t *block = asm_addr_to_ir(p, addr);
    assert(addr == block->inst->address);
    vector<Stmt *> ir = *(block->vine_ir);
    if(is_debug_on("asm_comments") && block->inst){
      ostringstream os;
      ostream_insn(p, block->inst, os);
      ir.insert(ir.begin(),new Comment(os.str()));
    }
    ret.insert(pair<address_t, vector<Stmt *> >(addr, ir));


#ifdef DEBUGGING
        cout << "   ";
        ostream_insn(p, block->inst, cout);
        cout << endl;

	if (block->vex_ir) 
	    ppIRSB(block->vex_ir); 

        vector<Stmt *> *inner = block->vine_ir;

        cout << "  {" << endl;

        for ( int j = 0; j < inner->size(); j++ )
        {
	  Stmt *s = inner->at(j);
	  cout << "     " << s->tostring();
	  cout << endl;

        }
        cout << "  }" << endl;
#endif


    delete block->vine_ir;
    delete block;
    vx_FreeAll();
  }

  return ret;
}


ir_function_t *asm_function_to_ir(asm_program_t *prog, asm_function_t *asm_f)
{
  ir_function_t *ir_f = new ir_function_t;
  // Last translated instruction for a ret.
  set<address_t> returns_last_insr;
  translate_init();

  vector<Stmt *> all_vine_stmts;
  vector<vine_block_t *> vine_blocks = generate_vex_ir(prog, asm_f);
  // Now we must sort the vine_blocks
  std::sort(vine_blocks.begin(), vine_blocks.end(), vine_block_sort());

  vine_blocks = generate_vine_ir(prog, vine_blocks);

  for(vector<vine_block_t *>::iterator it = vine_blocks.begin();
      it != vine_blocks.end(); it++){
    vine_block_t *block = *it;
    for(vector<Stmt *>::const_iterator i2 = block->vine_ir->begin();
	i2 != block->vine_ir->end(); i2++){
      Stmt *s = *i2;
      s->asm_address = block->inst->address;
      all_vine_stmts.push_back(s);      
    }
        delete block->vine_ir;
	delete block;
  }

  build_initial_blocks_and_cfg(ir_f, all_vine_stmts);

  return ir_f;
}

void build_initial_blocks_and_cfg(ir_function_t *f, 
				  vector<Stmt *> &stmts)
{
  map<string, Label *> label_map;
  /// Identify all the possible intra-procedural jump
  /// targets
  for(vector<Stmt *>::const_iterator it = stmts.begin();
      it != stmts.end(); it++){
    Stmt *s = *it;
    if(s->stmt_type != LABEL) continue;
    Label *l = (Label *) s;
    label_map.insert(pair<string, Label *>(l->label, l));
  }

  build_initial_bb(f, stmts, label_map);
  build_initial_cfg(f, stmts, label_map);

}

cfg_edge_t cfg_add_target(cfg_vertex_t src, Exp *target,
			  const map<address_t, ir_bb_t *> &addrmap,
			  const map<string, Label *> &label_map,
			  ir_function_t *f)
{
  cfg_edge_t new_edge;
  if(target->exp_type == NAME){
    Name *n = (Name *) target;
    if(label_map.find(n->name) != label_map.end()){
      // Intra-procedural direct jump
      Label *l = label_map.find(n->name)->second;
      assert(addrmap.find(l->ir_address) != addrmap.end());
      ir_bb_t *block = addrmap.find(l->ir_address)->second;
      boost::add_edge(src, block->cfg_num, f->cfg);
      new_edge.first = src; new_edge.second = block->cfg_num;
    } else {
      // Inter-procedural direct jmp
      boost::add_edge(src, CFG_CALL, f->cfg);
      f->calls.insert(n->name);
      new_edge.first = src; new_edge.second = CFG_CALL;
    }
  } else {
    // Indirect jump
    boost::add_edge(src, CFG_IJMP, f->cfg);
    new_edge.first = src; new_edge.second = CFG_IJMP;
  }
  
  return new_edge;
}

void build_initial_cfg(ir_function_t *f, const vector<Stmt *> &stmts,
		       const map<string, Label *> &label_map)
{

  ir_bb_t *block;

  // Map each stmt addr to a block;
  map<address_t, ir_bb_t *> addrmap;

  for(set<ir_bb_t *>::const_iterator it = f->blocks.begin();
      it != f->blocks.end(); it++){
    block = *it;
    for(vector<Stmt *>::const_iterator i2 = block->stmts.begin();
	i2 != block->stmts.end(); i2++){
      Stmt *s = *i2;
      addrmap.insert(pair<address_t, ir_bb_t *>(s->ir_address, block));
    }
  }

  // Set up some initial edges: return exits the cfg, and the first
  //  statment is linked up to CFG_ENTRY
  cfg_edge_t new_edge;
  boost::add_edge(CFG_RET, CFG_EXIT, f->cfg);
  new_edge.first = CFG_RET; new_edge.second = CFG_EXIT;
  f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge, true));

  if(stmts.size() == 0) return;

  assert(addrmap.find(stmts[0]->ir_address) != addrmap.end());
  block = addrmap.find(stmts[0]->ir_address)->second;
  new_edge.first= CFG_ENTRY;
  new_edge.second = block->cfg_num;
  boost::add_edge(CFG_ENTRY, block->cfg_num, f->cfg);
  f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge, true));


  for(set<ir_bb_t *>::const_iterator it = f->blocks.begin();
      it != f->blocks.end(); it++){
    block = *it;
    if(block->stmts.size() <= 0) continue;
    Stmt *s = block->stmts[block->stmts.size()-1];
    Jmp *j;
    CJmp *cj;
    Special *spec;

    ir_bb_t *dstblock;
    switch(s->stmt_type){
    case JMP:
      j = (Jmp *) s;
      new_edge = cfg_add_target(block->cfg_num, j->target, 
				addrmap, label_map,f);
      f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge, true));
      break;
    case CJMP:
      cj = (CJmp *) s;
      new_edge = cfg_add_target(block->cfg_num, cj->f_target, 
				addrmap, label_map, f);
      f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge, false));
      new_edge = cfg_add_target(block->cfg_num, cj->t_target, 
				addrmap, label_map, f);
      f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge, true));
      break;
    case SPECIAL:
      spec = (Special *) s;
      if(spec->special == "hlt"){
	boost::add_edge(block->cfg_num, CFG_STOP, f->cfg);
	new_edge.first = block->cfg_num;
	new_edge.second = CFG_STOP;
	f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge, true));
      } else if(spec->special == "ret"){
	boost::add_edge(block->cfg_num, CFG_RET, f->cfg);
	new_edge.first = block->cfg_num;
	new_edge.second = CFG_RET;
	f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge, true));
      } else {
	// If we have a fallthrough, add the link
	if(addrmap.find(s->ir_address+1) != addrmap.end()){
	  dstblock = addrmap.find(s->ir_address+1)->second;
	  new_edge.first = block->cfg_num; 
	  new_edge.second = dstblock->cfg_num;
	  boost::add_edge(new_edge.first, new_edge.second, f->cfg);
	  f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge,
						       true));
	}
      }
      break;
    case MOVE:
    case COMMENT:
    case LABEL:
    case VARDECL:
    case EXPSTMT:
      if(addrmap.find(s->ir_address+1) != addrmap.end()){
	dstblock = addrmap.find(s->ir_address+1)->second;
	new_edge.first = block->cfg_num; 
	new_edge.second = dstblock->cfg_num;
	boost::add_edge(new_edge.first, new_edge.second, f->cfg);
	f->edge_labels.insert(pair<cfg_edge_t, bool>(new_edge,
						     true));
      }
      break;
   case CALL:
   case RETURN:
   case FUNCTION:
        assert(0); // These are not handled
    }
  }
}

void
build_initial_bb(ir_function_t *f, vector<Stmt *> &stmts,
		 map<string, Label *> &label_map)
{
  cfg_vertex_t block_cntr = 0;
  ir_bb_t *block;
  map<Stmt *, ir_bb_t *> blockmap;


  /// Create our special basic blocks
  for(block_cntr = 0; block_cntr < CFG_RET+1; block_cntr++){
    block = new ir_bb_t;
    block->cfg_num = block_cntr;
    f->blocks.insert(block);
  }
  block_cntr = CFG_RET+1;

  /// Identify block leaders -- the first stmt in a basic block.
  /// Map the first statement that begins the basic block to
  /// the basic block
  bool next_is_leader = true;
  vector<Stmt *> newstmts;
  for(vector<Stmt *>::iterator it = stmts.begin();
      it != stmts.end(); it++){
    Stmt *s = *it;
    CJmp *cj;
    Jmp *j;
    Name *n;

    Label *l;

    if(next_is_leader == true){
      if(s->stmt_type != LABEL){
	Label *lbl = mk_label();
	print_debug("bb", "Adding label node");
	newstmts.push_back(lbl);
	label_map.insert(pair<string, Label *>(lbl->label, lbl));
	if(blockmap.find(lbl) == blockmap.end()){
	  blockmap.insert(pair<Stmt *, ir_bb_t *>(lbl, new ir_bb_t));
	  blockmap[lbl]->cfg_num = block_cntr++;
	}
      } else {
	if(blockmap.find(s) == blockmap.end()){
	  blockmap.insert(pair<Stmt *, ir_bb_t *>(s, new ir_bb_t));
	  blockmap[s]->cfg_num = block_cntr++;
	}
      }
      next_is_leader = false;
    }
    newstmts.push_back(s);
    switch(s->stmt_type){
    case JMP:
      j = (Jmp *) s;
      if(j->target->exp_type == NAME){
	n = (Name *) j->target;
	if(label_map.find(n->name) != label_map.end()){
	  // Intra-procedural jmp
	  l = label_map.find(n->name)->second;
	  if(blockmap.find(l) == blockmap.end()){
	    blockmap.insert(pair<Stmt *, ir_bb_t *>(l, new ir_bb_t));
	    blockmap[l]->cfg_num = block_cntr++;
	  }
	} 
      }
      next_is_leader = true;
      break;
    case CJMP:
      cj = (CJmp *) s;
      if(cj->t_target->exp_type == NAME){
	n = (Name *) cj->t_target;
	if(label_map.find(n->name) != label_map.end()){
	  // Intra-procedural jmp to a known target
	  l = label_map.find(n->name)->second;
	  if(blockmap.find(l) == blockmap.end()){
	    blockmap.insert(pair<Stmt *, ir_bb_t *>(l, new ir_bb_t));
	    blockmap[l]->cfg_num = block_cntr++;
	  }
	} 
      }
      if(cj->f_target->exp_type == NAME){
	n = (Name *) cj->f_target;
	if(label_map.find(n->name) != label_map.end()){
	  // Intra-procedural jmp
	  l = label_map.find(n->name)->second;
	  if(blockmap.find(l) == blockmap.end()){
	    blockmap.insert(pair<Stmt *, ir_bb_t *>(l, new ir_bb_t));
	    blockmap[l]->cfg_num = block_cntr++;
	  }
	}
      }
      next_is_leader = true;
      break;
    case SPECIAL:
      next_is_leader = true;
      break;
    case MOVE:
    case COMMENT:
    case LABEL:
    case VARDECL:
    case EXPSTMT:
      break;
    case CALL:
    case RETURN:
    case FUNCTION:
        assert(0); // not handled. file deprecated anyway. -djb
    }
  }

  stmts = vector<Stmt *>(newstmts);

  block = NULL;
  address_t cntr = ir_addr_base;

  // Fill in each basic block with its statements
  for(vector<Stmt *>::const_iterator it = stmts.begin();
      it != stmts.end(); it++){
    Stmt *s = *it;
    s->ir_address = cntr++;
    if(blockmap.find(s) != blockmap.end()){
      block = blockmap.find(s)->second;
    }
    assert(block != NULL);
    block->stmts.push_back(s);
    blockmap[s] = block;
  }
  // Collect the basic blocks as a set
  for(map<Stmt *, ir_bb_t *>::const_iterator it = blockmap.begin();
      it != blockmap.end(); it++){
    f->blocks.insert(it->second);
  }
  for(set<ir_bb_t *>::const_iterator it = f->blocks.begin();
      it != f->blocks.end(); it++){
    ir_bb_t *block = *it;
    f->blockmap.insert(pair<cfg_vertex_t, ir_bb_t *>(block->cfg_num,
						     block));
  }
}


void print_function(ir_function_t *f, ostream &out)
{
  out << "Function: " << f->name << endl;
  cfg_edge_iterator_t ei, ei_end;
  boost::tie(ei, ei_end) = boost::edges(f->cfg);
  unsigned i =0;
  out << "CFG Edges: ";
  for(; ei != ei_end; ei++, i++){
    if(i % 10 == 0){
      out << endl << "\t";
    }
    cfg_vertex_t src = boost::source(*ei, f->cfg);
    cfg_vertex_t dst = boost::target(*ei, f->cfg);
    out << "(" << src << "," << dst << ") ";
  }
  out << endl;

  for(map<cfg_vertex_t,ir_bb_t *>::const_iterator it = f->blockmap.begin();
      it != f->blockmap.end(); it++){
    ir_bb_t *block = it->second;
    out << "Block " << block->cfg_num << endl;
    for(vector<Stmt *>::const_iterator i2 = block->stmts.begin();
	i2 != block->stmts.end(); i2++){
      Stmt *s = *i2;
      out << "  (" << std::hex << s->asm_address << ") " 
	  <<  std::dec << s->ir_address 
	  << std::dec << ": " <<  s->tostring() << endl;
    }
    out << endl;
  }
}

void DefaultIRProgramVisitor::visitProgram(ir_program_t *prog)
{
  for(set<ir_function_t *>::const_iterator it=
	prog->functions.begin(); it != prog->functions.end();
      it++){
    this->visitFunction(*it);
  }
}
void DefaultIRProgramVisitor::visitFunction(ir_function_t *f)
{
  for(set<ir_bb_t *>::const_iterator it = 
	f->blocks.begin(); it != f->blocks.end(); it++){
    this->visitBlock(*it);
  }
}

void DefaultIRProgramVisitor::visitBlock(ir_bb_t *b)
{
  for(vector<Stmt *>::const_iterator it =
	b->stmts.begin(); it != b->stmts.end(); it++){
    Stmt *s = *it;
    s->accept(this);
  }
}

/*
void DefaultIRProgramVisitor::visitBinOp(BinOp *b)
{  b->accept(this); }

void DefaultIRProgramVisitor::visitUnOp(UnOp *u)
{ u->accept(this);}

void DefaultIRProgramVisitor::visitConstant(Constant *c)
{  c->accept(this);}

void DefaultIRProgramVisitor::visitTemp(Temp *t)
{ t->accept(this); }

void DefaultIRProgramVisitor::visitPhi(Phi *p)
{ p->accept(this); }

void DefaultIRProgramVisitor::visitSpecial(Special *s)
{ s->accept(this); }

void DefaultIRProgramVisitor::visitMem(Mem *m)
{ m->accept(this); }

void DefaultIRProgramVisitor::visitJmp(Jmp *j)
{ j->accept(this); }

void DefaultIRProgramVisitor::visitCJmp(CJmp *c)
{ c->accept(this); }

void DefaultIRProgramVisitor::visitLabel(Label *l)
{ l->accept(this); }

void DefaultIRProgramVisitor::visitMove(Move *m)
{ m->accept(this); }

void DefaultIRProgramVisitor::visitComment(Comment *c)
{ c->accept(this); }

void DefaultIRProgramVisitor::visitExpStmt(ExpStmt *e)
{ e->accept(this); }

void DefaultIRProgramVisitor::visitUnknown(Unknown *u)
{ }

void DefaultIRProgramVisitor::visitCast(Cast *c)
{ c->accept(this); }

void DefaultIRProgramVisitor::visitName(Name *n)
{ n->accept(this); }
*/

ir_function_t *
unroll_function(ir_function_t *f, const unsigned &unroll_cnt)
{
  // TBD:
  return f;
  /*  map<cfg_vertex_t, set<cfg_vertex_t> > retmap;
  
  print_debug("cfg", "Unrolling %s", f->name.c_str());
  unrolled_cfg_t ur= unroll_cfg(f->cfg,
				unroll_cnt,
				CFG_ENTRY,
				CFG_EXIT);
  string s = "unrolled.cfg";
  ofstream out(s.c_str());
  boost::write_graphviz(out, ur.acyclic_cfg);
  out.close();
  */
}


