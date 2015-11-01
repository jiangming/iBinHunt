/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef _DEADCODE_H
#define _DEADCODE_H
#include "defusevisitor.h"

/// removes dead statements from SSA program @param p
void ssa_deadcode_elimination(ir_program_t *p);
/// removes dead statements from SSA function @param f
/// Using algorithm from appel p.456 (19.12)
void ssa_deadcode_elimination(ir_function_t *f);
#endif
