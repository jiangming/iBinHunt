/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include "translate.h"
#include <bfd.h>

extern bool use_eflags_thunks;


// from asm_program.cpp
void init_disasm_info(asm_program_t *prog);

asm_program_t *instmap_to_asm_program(instmap_t *map)
{
  return map->prog;
}

// Returns a fake asm_program_t for use when disassembling bits out of memory
asm_program_t* fake_prog_for_arch(enum bfd_architecture arch)
{
  int machine = 0; // TODO: pick based on arch
  asm_program_t *prog = new asm_program_t;
  
  prog->abfd = bfd_openw("/dev/null", NULL);
  assert(prog->abfd);
  bfd_set_arch_info(prog->abfd, bfd_lookup_arch(arch, machine));

  //not in .h bfd_default_set_arch_mach(prog->abfd, arch, machine);
  bfd_set_arch_info(prog->abfd, bfd_lookup_arch(arch, machine));
  init_disasm_info(prog);
  return prog;
}


int instmap_has_address(instmap_t *insts,
			address_t addr)
{
  return (insts->imap.find(addr) != insts->imap.end());
}

/*
cflow_t *instmap_control_flow_type(instmap_t *insts,
		      address_t addr)
{
  cflow_t * ret = (cflow_t *) malloc(sizeof(cflow_t));

  assert(insts->imap.find(addr) != insts->imap.end());
  Instruction *inst = insts->imap.find(addr)->second;
  address_t target;
  ret->ctype = get_control_transfer_type(inst, &target);
  ret->target = target;
  return ret;
}
*/

vine_block_t *instmap_translate_address(instmap_t *insts,
					address_t addr)
{
  translate_init();
  vx_FreeAll();
  vector<Instruction *> foo;

  assert(insts->imap.find(addr) != insts->imap.end());

  foo.push_back(insts->imap.find(addr)->second);
  vector<vine_block_t *> blocks = generate_vex_ir(insts->prog, foo);
  blocks = generate_vine_ir(insts->prog, blocks);
  assert(blocks.size() == 1);
  vine_block_t *block = *(blocks.begin());
  block->vex_ir = NULL;
  vx_FreeAll();
  return block;
}


vine_blocks_t *instmap_translate_address_range(instmap_t *insts,
					   address_t start,
					   address_t end)
{
  translate_init();
  vx_FreeAll();
  vector<Instruction *> foo;
  vine_blocks_t *ret = new vine_blocks_t;

  for(address_t i = start; i <= end; i++){
    if(insts->imap.find(i) == insts->imap.end()) continue;
    foo.push_back(insts->imap.find(i)->second);
   }
  vector<vine_block_t *> blocks = generate_vex_ir(insts->prog, foo);
  blocks = generate_vine_ir(insts->prog, blocks);

  for(unsigned i = 0; i < blocks.size(); i++){
    vine_block_t *block = blocks.at(i);
    assert(block);
    
    if(block->inst == NULL)
      continue;
    
    /* This is broken as it removes the jumps from the end of
       repz instructions. Just because control flow eventually goes on
       to the following instruction doesn't mean that jump is at the end.
       It should simply be checking that the jump is to the following
       instruction since we know where that is.
    // If the statement isn't control flow, and not the last
    // remove the dummy jumps to the next block that vex inserts
    bfd_vma target;
    int ctype = get_control_transfer_type(block->inst, &target);
    Stmt *s;
    switch(ctype){
    case INST_CONT:
      s = block->vine_ir->back();
      if(s->stmt_type == JMP){
	block->vine_ir->pop_back();
      }
      break;
    default:
      break;
    }
    */
  }
  
  ret->insert(ret->end(), blocks.begin(), blocks.end());
  
  for(vector<vine_block_t *>::iterator it = ret->begin();
      it != ret->end(); it++){
    vine_block_t *block = *it;
    block->vex_ir = NULL; // this isn't available. 
  }

  return ret;
}



address_t get_last_segment_address(const char *filename, 
				   address_t addr)
{
  bfd *abfd = initialize_bfd(filename);
  unsigned int opb = bfd_octets_per_byte(abfd);

  address_t ret = addr;
  for(asection *section = abfd->sections; 
      section != (asection *)  NULL; section = section->next){

    bfd_vma datasize = bfd_get_section_size_before_reloc(section);
    if(datasize == 0) continue;

    address_t start = section->vma;
    address_t end = section->vma + datasize/opb;
    if(addr >= start && addr <= end)
      return end;
  }
  return ret;
}




instmap_t *
sqlite3_fileid_to_instmap(char *filename, int fileid)
{
  char sql[1024];
  char sql_seg[1024];
  int r;
  int r_seg;
  sqlite3_stmt *ppstmt;
  sqlite3_stmt *ppstmt_seg;
  vector<vine_block_t *> results;
  Segment *seg, *ts;
  instmap_t *ret = new instmap_t;

  // FIXME: get arch from sqlite3 file
  ret->prog = fake_prog_for_arch(bfd_arch_i386);
  ret->prog->segs = NULL;
  struct disassemble_info *disasm_info = &ret->prog->disasm_info;
  

  sqlite3 *db;
  r = sqlite3_open(filename, &db);
  if(r){
    fprintf(stderr, "Can't open database: %s\n", sqlite3_errmsg(db));
    sqlite3_close(db);
    exit(1);
  }

  snprintf(sql_seg, sizeof(sql_seg), 
	   "SELECT start_address, end_address from"
	   " segments where file_id = %d;", fileid);
  r_seg = sqlite3_prepare_v2(db, sql_seg, -1, &ppstmt_seg, NULL);
  if(r_seg != SQLITE_OK || ppstmt_seg == NULL){
    fatal("sqlite3_fileid_to_instmap", 
	  "sqlite3_prepare failed for segs: %s", sqlite3_errmsg(db));
  }
  // iterate through all segments, creating the appropriate
  // disassemble information.
  while(1){
    r_seg = sqlite3_step(ppstmt_seg);
    if(r_seg == SQLITE_DONE) break;
    if(r_seg != SQLITE_ROW) break;
    sqlite_int64 startaddr = sqlite3_column_int64(ppstmt_seg, 0);
    sqlite_int64 endaddr = sqlite3_column_int64(ppstmt_seg, 1);

    // Set up segment.
    assert(( endaddr-startaddr) > 0);
    seg = (Segment *) malloc(sizeof(Segment));
    memset(seg, 0, sizeof(Segment));
    seg->data = (bfd_byte *) malloc(endaddr-startaddr);
    memset(seg->data, 0, endaddr-startaddr);
    seg->datasize = (endaddr-startaddr);
    seg->start_addr = startaddr;
    seg->end_addr = endaddr;
    seg->is_code = 1;

      // Next 4 lines are similar to what:
      //      init_disasm_info(&disasm_info, seg);
      // does.
    disasm_info->buffer = seg->data;
    disasm_info->buffer_vma = startaddr;
    disasm_info->buffer_length = seg->datasize;
    disasm_info->section = NULL;
    

    // Query database for instructions 
    // in segment
    snprintf(sql,sizeof(sql), 
	     "SELECT address,length,bytes"
	     " from instrs where file_id = %d and address >= %llu and"
	     " address <= %llu;", 
	     fileid, startaddr, endaddr);
    r = sqlite3_prepare_v2(db, sql, -1, &ppstmt, NULL);
    if(r != SQLITE_OK || ppstmt == NULL){
      fatal("sqlite3_fileid_to_instmap", 
	    "sqlite3_prepare failed for instrs: %s", sqlite3_errmsg(db));
    }
    // add seg to segments list.
    seg->next = NULL;
    if(ret->prog->segs == NULL) {
      ret->prog->segs = seg;
    }
    else{
      ts = ret->prog->segs;
      // Note: this is O(n^2) in the number of segments, but n is usually small,
      // so I'm leaving it as is.
      while(ts->next != NULL)
	ts = ts->next;
      ts->next = seg;
    }
    while(1){
      // Populate segment
      r = sqlite3_step(ppstmt);
      if(r == SQLITE_DONE) break;
      if(r != SQLITE_ROW) break;
      uint32_t bytes[4];
      sqlite_int64 addr = sqlite3_column_int64(ppstmt, 0);
      sqlite_int64 len = sqlite3_column_int64(ppstmt, 1);
      const unsigned char * bytestr = sqlite3_column_text(ppstmt,2);
      char buf[3];
      
      for(int j = 0; j < len; j++){
	uint8_t byte = 0;
	sscanf((char *)bytestr, "%2x", &byte);
	bytestr +=2;
	seg->data[(addr-startaddr)+j] = byte;
      }

      Instruction *inst = get_inst_of(ret->prog, addr);
      if(inst != NULL){
	ret->imap.insert(pair<address_t, Instruction *>(inst->address,
						 inst));
      } else {
	print_debug("warning", "Instruction %llu is NULL. skipping\n",
	      addr);
      }

    }
  } 
  return ret;
}

instmap_t *
filename_to_instmap(const char *filename)
{
  instmap_t *ret = new instmap_t;
  asm_program_t *prog = disassemble_program(filename);
  ret->prog = prog;

  // iterate over functions
  for ( map<address_t, asm_function_t *>::const_iterator i = prog->functions.begin();
	i != prog->functions.end(); i++ )
    {
      asm_function_t *f = i->second;
      ret->imap.insert(f->instmap.begin(), f->instmap.end());
      //ret->insert(pair<address_t, Instruction *>(inst->address, inst));
    }
 
  return ret;
}


// from asm_program.cpp
void init_disasm_info(bfd *abfd, struct disassemble_info *disasm_info);


// Quick helper function for ocaml, since we don't have a proper libopcodes
// interface yet.
// This isn't really the right place for it...
extern "C" {
void print_disasm_rawbytes(enum bfd_architecture arch,
			   bfd_vma addr,
			   const char *buf, int size)
{
  asm_program_t *prog = byte_insn_to_asmp(arch, addr, (unsigned char*)buf, size);
  
  if (!prog)
    return;

  disassembler_ftype disas = disassembler(prog->abfd);
  disas(addr, &prog->disasm_info);
  free_asm_program(prog);
  fflush(stdout);
}

}
