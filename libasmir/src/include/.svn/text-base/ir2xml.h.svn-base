/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef _IR2XML_H
#define _IR2XML_H
#include "irvisitor.h"
#include "exp.h"
#include "stmt.h"

/**
 * @class IR2XML serializes the IR to an XML format.  The XML format
 * is ad-hoc, but should be simple enough to use in practice.
 */
class IR2XML : public DefaultIRVisitor {
 public:
  /// @param out is the serialized output stream
  IR2XML(ostream &out);
  virtual void xml_prologue();
  virtual void xml_epilogue();
  /// @param e is serialized as <binop type=optype>lhs rhs</binop>
  virtual void visitBinOp(BinOp *e);
  /// @param e is serialized as <unop type=optype>operand</unop>
  virtual void visitUnOp(UnOp *e);
  /// @param e is serialized <constant type=t width=w>value</constant>
  virtual void visitConstant(Constant *c);
  /// @param e is serialized as <temp type=t width=w>name</temp>
  virtual void visitTemp(Temp *e);
  /// @param p is serialized as <phi> var1 var2 ... varn </phi>
  virtual void visitPhi(Phi *p);
  /// @param s is serialized as <special>string</special>
  virtual void visitSpecial(Special *s);
  /// @param m is serialized as <mem type=t width=w>exp</mem>
  virtual void visitMem(Mem *m);
  /// @param u is serialized as <unknown>string</unknown>
  virtual void visitUnknown(Unknown *u);
  /// @param c is serialized as <cast type=t width=sw casttype=str>expr</cast>
  virtual void visitCast(Cast *c);
  /// @param n is serialized as as <name>label</name>
  virtual void visitName(Name *n);
  /// @param j is serialized as as <jmp>label</jmp>
  virtual void visitJmp(Jmp *j);
  /// @param j is serialized as <cjmp> cond true_label false_label</cjmp>
  virtual void visitCJmp(CJmp *j);
  /// @param l is serialized as <label>string</label>
  virtual void visitLabel(Label *l);
  /// @param m is serialized as <move>lhs rhs</move>
  virtual void visitMove(Move *m);
  /// @param c is serialized as <comment>string</comment>
  virtual void visitComment(Comment *c);
  /// @param s is serialized as <expstmt>exp</expstmt>
  virtual void visitExpStmt(ExpStmt *s);
  /// @param s is serialzed as <decl>string:type</decl>
  virtual void visitVarDecl(VarDecl *s);

  virtual ~IR2XML(){};

 protected:
  /// prints out register type, e.g., <binop kind="FLOAT", width="8">
  void print_reg_type(const reg_t t);
  /// prints out spaces so that expressions look nested.
  void print_depth();
  unsigned depth;
  ostream &os;
};

#endif
