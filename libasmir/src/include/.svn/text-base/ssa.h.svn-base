/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef _SSA_H
#define _SSA_H
#include <map>
#include <stack>
#include "stmt.h"
#include "exp.h"
#include "irvisitor.h"
#include "cfg.h"
#include "ir_program.h"
#include "defusevisitor.h"
#include <iostream>

using namespace std;


/// Convert function @param f to SSA form using alg 19.7 from Appel
/// java compilers book (p 447)
void function_to_ssa(ir_function_t *f, 
		     const cfg_vertex_t entry_id = CFG_ENTRY,
		     const cfg_vertex_t exit_id = CFG_EXIT);


#endif
