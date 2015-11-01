/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef _CONSTANT_SIMPLIFY_EXP_H
#define _CONSTANT_SIMPLIFY_EXP_H
#include "exp.h"
#include "stmt.h"
#include "irvisitor.h"
#include <assert.h>
using namespace std;
/// @return a new Constant = @param c1 + @param c2
/// If there is overflow, or if addition has an unexpected result due
/// to mistyped @param c1 and @param c2, this will return a binop
/// for the subtraction of the constants.  Note the error
/// cases result in a NEW binop, thus may result in a memory leak.
Exp *add_constant(Constant *c1, Constant *c2, reg_t ret_type);
/// @return a new Constant = @param c1 * @param c2
/// If there is overflow, or if addition has an unexpected result due
/// to mistyped @param c1 and @param c2, this will return a binop
/// for the subtraction of the constants.  Note the error
/// cases result in a NEW binop, thus may result in a memory leak.
Exp *mul_constant(Constant *c1, Constant *c2, reg_t ret_type);
/// @return a new Constant = @param c1 - @param c2
/// If there is underflow, or if addition has an unexpected result due
/// to mistyped @param c1 and @param c2, this will return a binop
/// for the subtraction of the constants.  Note the error
/// cases result in a NEW binop, thus may result in a memory leak.
Exp *sub_constant(Constant *c1, Constant *c2, reg_t ret_type);


/// Rotations  and simplifications 
/// described in Muchnik Figure 12.6 (page 337).
bool R1R3R5(Exp *&b);
bool R2R4R6(Exp *&b);
bool R7(Exp *&b);
bool R8(Exp *&b);
bool R9(Exp *&b);
bool R10(Exp *&b);
bool R11(Exp *&b);
bool R12(Exp *&b);
bool R13(Exp *&b);
bool R14(Exp *&b);
bool R15(Exp *&b);
bool R16(Exp *&b);
bool R17(Exp *&b);
bool R18(Exp *&b);
bool R19(Exp *&b);
bool R20(Exp *&b);

/// This canonicalizes the expression tree. A canonicalized tree turns
/// expressions into sums of products. We simplify the expression
/// along the way, performing constant folding where appropriate.
class ConstantSimplifyExp : public IRChangeVisitor {
 public:
  ConstantSimplifyExp();
  virtual ~ConstantSimplifyExp();
  Exp * simplify(Exp *exp);
  virtual void visitBinOp(BinOp *b);

 protected:
  bool change;
  set <Exp*> simplified; //keep track of which exp's are fully simplified
};

#endif
