/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef __IRDEENDIANIZER_H__
#define __IRDEENDIANIZER_H__

#include "ir_program.h"
#include "irvisitor.h"


/*
 * This class will visit an ir_program_t and modify all movs to and from memory
 * to be of the same size. (for now one byte, but the idea is that all accesses
 * are the same size, so you don't need to worry about endianness)
 // assumes memory is byte addressed
 */
class IRDeEndianizer : public IRChangeVisitor {
 public:
  typedef enum {ENDIAN_BIG, ENDIAN_LITTLE} endian_t;

  IRDeEndianizer() : endian(ENDIAN_LITTLE), width(REG_8) { }
  IRDeEndianizer(endian_t e) : endian(e), width(REG_8) { }
  virtual ~IRDeEndianizer() {}

  virtual void visitMove(Move *);
  virtual void visitMem(Mem *);
  virtual void visitBlock(ir_bb_t *);
  /// So that this visitor is useful for vine_block_ts
  virtual void visitvectorStmt(vector<Stmt*> *);

  static int reg_width_to_size(reg_t w) {
    switch (w) {
    case REG_1:
      return 1;
    case REG_8:
      return 1;
    case REG_16:
      return 2;
    case REG_32:
      return 4;
    case REG_64:
      return 8;
    }
    return -1;
  }
  /** @returns a vector of memory references, from the least significant
   * address to the most*/
  vector<Exp*> split_mem(Mem *addr, int size);

 protected:
  endian_t endian;
  reg_t width;
  /* We  can't normally modify the vector<Stmt*> in place, because doing so
   * invalidates our iterators over it, if it ever gets reallocated.
   * One solution is to  we must make a modified copy then replace the contents
   * of the old vector with those of the new vector.
   */
  vector<Stmt*> new_stmts;
  //vector<Stmt*>::iterator cur_stmt;
  //ir_bb_t *block;
};

#endif
