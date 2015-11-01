/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#include <iostream>
#include "ir_program.h"

using namespace std;

int main(int argc, char *argv[])
{
  if(argc != 3){
    fprintf(stderr, "Usage: %s filename function\n", argv[0]);
  }
  asm_program_t *asmp = disassemble_program(argv[1]);
  assert(asmp);
  address_t addr = get_function_address(asmp, argv[2]);
  assert(addr);
  assert(asmp->functions.find(addr) != asmp->functions.end());
  asm_function_t *asmf = asmp->functions.find(addr)->second;
  ir_function_t *irf = asm_function_to_ir(asmp, asmf);
  assert(irf);
  print_function(irf, cout);
  string dotfile = argv[2] + string(".dot");
  ofstream out(dotfile.c_str());
  print_cfg_dot(irf->cfg,out,map<cfg_vertex_t, string>());
  out.close();
  return 0;
}
