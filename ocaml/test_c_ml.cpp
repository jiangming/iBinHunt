/* A simple test example showing how to use c_to_ml_stp interface */

#include <stdio.h>
extern "C" {
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include "c_interface.h"
}

#include <stmt.h>
//#include "libasmir.h"

extern "C" {
  int query_ml_stp_exp_vc(void *arg1, void * arg2);
  int query_ml_stp_exp_vc_deend(void *arg1, void * arg2);
  char *query_ml_stp_exp_string(void *arg1, void * arg2);
  void query_ml_stp_exp_file(void *arg1, void *arg2, char *file_name);
  int query_ml_stp_exp(void *exp);
  void init(char **argv);

}

int main(int argc, char **argv)
{
  int ret;
  init(argv);
  Exp *e1, *e2, *e3, *e4, *e5, *e;
  const_val_t val;
  void *ptr;
  val = 3;
  char *ret_str;

  /* 
   * let mem[fffc] = R_EAX in
   *   let mem[10000] = INPUT_1 in
   *     mem[10000] == mem[fffc]
   */

  e1 = new Let(
      new Mem(new Constant(REG_32, 0x0000fffc)), 
      new Temp(REG_32, "R_EAX"), 
      new Let(
	new Mem(new Constant(REG_32, 0x00010000)),
	new Temp(REG_8, "INPUT_1"),
	new BinOp(EQ, 
	  new Mem(new Constant(REG_32, 0x00010000)),
	  new Mem(new Constant(REG_32, 0x0000fffc)))
	));
  e5 = e1;
  /*
  e1 = new Temp(REG_32, "t");
  e2 = new Constant(REG_32, 3);
  e3 = new BinOp(PLUS, e1, e2);
  e4 = new Constant(REG_32, 5);
  //t + 3 < 5
  e5 = new BinOp(LT, e3, e4);
  */
  ptr = (void *) e5;
  // ret = query_ml_stp_exp(ptr);
  // if(ret) {printf("valid!\n");} else {printf("invalid!\n");}
  // e = new Constant(REG_32, 3);
  // ptr = (void *) e;
  // ret = query_ml_stp_exp(ptr);
  // if(ret) {printf("valid!\n");} else {printf("invalid!\n");}  
  
  VC vc;
  vc = vc_createValidityChecker();
  ptr = (void *) e5;
  // ret_str = query_ml_stp_exp_string(e5,vc);
  query_ml_stp_exp_file(e5, vc, "test_file.out");
  // printf("STP FILE:\n%s\n", ret_str);
  /*
  if(ret) {printf("valid!\n");} else 
    {printf("invalid!\n");   
    vc_printCounterExample(vc);}  
    */

}
