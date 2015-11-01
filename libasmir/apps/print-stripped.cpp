/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <set>

#include "asm_program.h"
#include "disasm-pp.h"

extern "C" 
{
#include "libvex.h"
}

#include "irtoir.h"
#include "typecheck_ir.h"
#include "irdeendianizer.h"
#include "ir2xml.h"
#include "ir_printer.h"

using namespace std;

extern Segment *segs;

void print(map<string, vector<Instruction *> > insns){

  print_globals();
  vector<Instruction *> insts = insns[".text"];
  vector<vine_block_t *> vine_blocks = generate_vex_ir(insts);
  vine_blocks = generate_vine_ir(vine_blocks);
    //       for(vector<vine_block_t *>::const_iterator i2 =
    // 	    vine_blocks.begin(); i2 != vine_blocks.end(); i2++){
    // 	vine_block_t *bl = *i2;
    // 	IRDeEndianizer deend;
    // 	deend.visitvectorStmt(bl->vine_ir);
    //       }
  print_vine_ir(vine_blocks);
}

map<string, vector<Instruction *> > disassemble_sections(bfd *abfd)
{
  struct disassemble_info disasm_info;
  map<string, vector<Instruction *> > ret;
  bzero(&disasm_info, sizeof(disasm_info));
  unsigned int opb = bfd_octets_per_byte(abfd);
  disasm_info.octets_per_byte = opb;

  for(asection *section = abfd->sections; 
      section != (asection *)  NULL; section = section->next){
    Segment *seg, *ts;

    if(strcmp(section->name, ".text") != 0) continue;
    int is_code = 0;
    bfd_byte *data = NULL;
    bfd_vma datasize = bfd_get_section_size_before_reloc(section);
    if(datasize == 0) continue;

    data = (bfd_byte *) xalloc((size_t) datasize, (size_t)
			       sizeof(bfd_byte));
    bfd_get_section_contents(abfd, section, data, 0, datasize);
    seg = (Segment *) xalloc(1, sizeof(Segment));
    seg->data = data;
    seg->datasize = datasize;
    seg->start_addr = section->vma;
    seg->end_addr = section->vma + datasize/opb;
    seg->section = section;
    if(section->flags & SEC_CODE == 0)
      is_code = 0;
    else
      is_code = 1;
    seg->is_code = is_code;
    if(is_code){
      seg->status = (unsigned char *)
	xalloc((seg->end_addr - seg->start_addr), sizeof(char));
      seg->insts = (Instruction **) xalloc((seg->end_addr - 
					    seg->start_addr),
					   sizeof(Instruction *));
      init_disasm_info(&disasm_info, seg);

      bfd_vma pc = seg->start_addr;
      vector<Instruction *> insts;
      while(pc < seg->end_addr){
	Instruction *inst = get_i386_insn(&disasm_info, pc, seg);
	if(inst == NULL){
	  print_debug("warning", 
		      "Disassembled NULL instruction at %X", pc);
	  print_debug("warning", "Skipping rest of section");
	  break;
	}
	//	if(strcmp(section->name, ".text") == 0){
	//	  ostream_i386_insn(inst, cout);
	//	}
	insts.push_back(inst);
	pc += inst->length;
      }

      ret.insert(pair<string, vector<Instruction *> >(section->name,
						      insts));

      for(pc = seg->start_addr; pc < seg->end_addr; ++pc){
	Instruction *inst = get_i386_insn(&disasm_info, pc, seg);
	// DJB: Hack for stmxcsr and ldmxcsr instrs as found
	// in atphttpd instr 806a36e
	//if(inst->opcode[0] == 0xae && inst->opcode[1] == 0xf)
	//  inst->length++;
	seg->insts[pc - seg->start_addr] = inst;
      }

      seg->next = NULL;
      if(segs == NULL)
	segs = seg;
      else{
	ts = segs;
	while(ts->next != NULL)
	  ts = ts->next;
	ts->next = seg;
      }
    }
  }
  return ret;
}

int main(int argc, char *argv[])
{
  char *filename;
  debug_on("warning");
  map<string, vector<Instruction *> > insns;
  if(argc != 2){
    printf("Usage: %s <filename>\n", argv[0]);
    return -1;
  }
  filename = argv[1];
  cerr << "Disassembling stripped binary." << endl;
  translate_init();
  bfd *abfd = initialize_bfd(filename);
  insns = disassemble_sections(abfd);
  print(insns);
}
