/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
#ifndef _DEFUSEVISITOR_H
#define _DEFUSEVISITOR_H
#include "irvisitor.h"
#include "ir_program.h"


/// @class used for computing def-use sets.  Also keep track of the
/// type of variables defined or used. 
/// ( Note that type mapping checks
/// for self-consistency: the same variable name should always have
/// the same type. We do this hear not because it is part of
/// calculating def/use sets, but just as an added consistency check.)
class DefUseVisitor : public DefaultIRVisitor {
 public:
  DefUseVisitor() {};
  /// Compute def and use sets for a function. 
  void compute(const ir_function_t *f);

  /// Compute def and use sets for a block.
  void compute(const ir_bb_t *block);

  /// Compute def and use sets for a stmt
  void compute(Stmt *s);

  /// Clear out all tables
  void clear();
  
  /// @return the cfg nodes that define \param @name
  set<cfg_vertex_t> get_def2cfg(const string name);
  /// @return the cfg nodes that use @param name
  set<cfg_vertex_t> get_use2cfg(const string name);
  /// @return the Stmt nodes that use @param name
  set<Stmt *> get_use2stmt(const string name);
  /// @return the Stmt nodes that def @param name
  set<Stmt *> get_def2stmt(const string name);

  /// @return the set of all defined variables in block @param v
  set<string> get_cfg_defs(const cfg_vertex_t &v);
  /// @return the set of all used vars in block @param v 
  set<string> get_cfg_uses(const cfg_vertex_t &v);
  /// @return the set of all used vars in Stmt @param v
  set<string> get_stmt_uses(Stmt *s);
  /// @return the set of all defed vars in Stmt @param v
  set<string> get_stmt_defs(Stmt *s);

  /// @return the set of all variables both used or defined in block
  /// @param v
  set<string> get_bb_vars(const cfg_vertex_t &v);

  /// @return the set of all variables used or defined in the function
  set<string> get_all_vars();

  /// @return the mapping from Temp name to stmts defining it.
  map<Stmt *, set<string> > get_stmt_defmap();
  /// @return the mapping from Temp name to stmts using it.
  map<Stmt *, set<string> > get_stmt_usemap();
  /// @return the map from vertex id to set of defined vars
  map<cfg_vertex_t, set<string> > get_cfg_defmap();
  /// @return the map from vertex id to set of used vars
  map<cfg_vertex_t, set<string> > get_cfg_usemap();
  /// @return a map from name of var to type of var
  map<string, reg_t> get_name2register();
  /// @return the type of var, given @param name
  reg_t get_type(const string name);

  virtual void visitTemp(Temp *);
  virtual void visitSpecial(Special *);
  virtual void visitCJmp(CJmp *);
  virtual void visitJmp(Jmp *);
  virtual void visitMove(Move *);
  virtual void visitExpStmt(ExpStmt *);
  virtual ~DefUseVisitor() {};

 protected:
  /// A mapping from Stmt to the set of vars defined in that stmt
  map<Stmt *, set<string> > stmt_defmap;
  /// A mapping frmo Stmt to the set of vars used in that stmt
  map<Stmt *, set<string> > stmt_usemap;

  /// A mapping from bb id to the set of vars defined in that bb
  map<cfg_vertex_t, set<string> > cfg_defmap;
  /// A mapping from bb id to the set of vars used in that bb
  map<cfg_vertex_t, set<string> > cfg_usemap;
  /// A mapping from a var name to its type.
  map<string, reg_t> name2register;

 private:
  // These are temporaries used to keep track of referenced variables
  // (either def or use), defed, and used in a particular statement.
  set<string> refset;

};
#endif
