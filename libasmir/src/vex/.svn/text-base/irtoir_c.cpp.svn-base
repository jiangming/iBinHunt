/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include <bfd.h>
#include "irtoir.h"

vine_blocks_t * asmir_asmprogram_to_vine(asm_program_t *prog) {
  vector<vine_block_t *> *res = new vector<vine_block_t *>();
  // eww, references
  *res = generate_vex_ir(prog);
  generate_vine_ir(prog, *res);
  return res;
}

int asmir_vine_blocks_size(vine_blocks_t *bs) {
  return bs->size();
}

vine_block_t * asmir_vine_blocks_get(vine_blocks_t *bs, int i) {
  return bs->at(i);
}

void destroy_vine_block(vine_block_t *b) {
  // FIXME: inst seems to be a pointer into the asm_program_t,
  // so we don't need to free it?
  // FIXME: stuff in vex_ir seems to be allocated in VEX's own heap?
  // If so, should provide a way to free that memory too?
  //free(b->vex_ir);
  for (vector<Stmt*>::iterator j = b->vine_ir->begin();
       j != b->vine_ir->end(); j++) {
    Stmt::destroy(*j);
  }
  delete b->vine_ir;
  delete b;
}

void destroy_vine_blocks(vine_blocks_t *bs) {
  for (vector<vine_block_t *>::iterator i = bs->begin(); i != bs->end(); i++) {
    destroy_vine_block(*i);
  }
  delete bs;
}



address_t asmir_vine_block_address(vine_block_t *b)
{
  return b->inst->address;
}

int asmir_vine_block_size(vine_block_t *b) {
  return b->vine_ir->size();
}

Stmt * asmir_vine_block_get(vine_block_t *b, int i) {
  return b->vine_ir->at(i);
}


// from translate.cpp
asm_program_t* fake_prog_for_arch(enum bfd_architecture arch);
extern VexArch guest_arch;

// hmm, this isn't in bfd.h, but is in the documentation...
extern "C" {
  extern void *bfd_alloc (bfd *, bfd_size_type);
}

asm_program_t*
byte_insn_to_asmp(bfd_architecture arch, address_t addr, unsigned char *bb_bytes, unsigned int len)
{
  asm_program_t *prog = fake_prog_for_arch(arch);
  unsigned char *bytes = (unsigned char*)bfd_alloc(prog->abfd, len);
  // copy the string, because the old one is freed when we return
  memcpy(bytes, bb_bytes, len);
  Instruction *inst = new Instruction;

  inst->address = addr;
  inst->length = len;
  inst->bytes = bytes;

  struct disassemble_info *disasm_info = &prog->disasm_info;
  disasm_info->buffer = bytes;
  disasm_info->buffer_vma = addr;
  disasm_info->buffer_length = len;
  disasm_info->section = NULL;

  asm_function_t *asmf = new asm_function_t;
  asmf->name = "";
  asmf->start_addr = addr;
  asmf->end_addr = addr+len;
  asmf->instmap[addr] = inst;
  
  prog->functions[addr] = asmf;
      
  return prog;
}
