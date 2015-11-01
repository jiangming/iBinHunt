/*
 Owned and copyright BitBlaze, 2007. All rights reserved.
 Do not copy, disclose, or distribute without explicit written
 permission.
*/
/*
 * Functions to typecheck different parts of the Vine IR
 */

#ifndef __TYPECHECK_IR_H__
#define __TYPECHECK_IR_H__

#include <stdexcept>
#include "exp.h"
#include "stmt.h"


class TypeError : public std::logic_error {
 public:
  TypeError(string err) : std::logic_error(err) { }
};


/* Typecheck an IR expression.
 * e is the Exp that needs typechecking.
 * g is a map containing the context. If NULL, context will be assumed right
 * t is a pointer to where to store the type of e.
 * Returns <0 on error, and leaves t in an undefined state.
 * or raises a TypeError exception
 */
int typecheck_exp(reg_t *t,
		  const map<string,reg_t> *g,
		  const Exp *e);


/* Typecheck an IR statement.
 * s is the statement to typecheck.
 * g is a map containing the context, which may be modified. (Ignored if NULL)
 * if the statement is an assignment
 * Returns <0 on error, after which g is undefined
 * or raises a TypeError exception
 */
int typecheck_stmt(map<string,reg_t> *g, Stmt *s);

#endif
