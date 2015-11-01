/*
 Owned and copyright David Brumley, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef _SYMEVAL_H
#define _SYMEVAL_H
class SymEval : public IRChangeVisitor {
public:
  SymEval() {};
  bool execute(const vector<Stmt *> stmts, Exp *&ret);
  virtual void visitTemp(Temp *t);
  virtual void visitMove(Move *m);

  queue<Stmt *> q;
  map<string, Exp *> regstate;
  map<Exp *, Exp *> memstate;
};

#endif
