#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#include <caml/camlidlruntime.h>

#include "libasmir.h"
#include "libstp.h"

/* created by camlidl as part of libasmir_stubs.c */
value camlidl_c2ml_libasmir_Exp(Exp * _c2, camlidl_ctx _ctx);

void init(char **argv)
{
  caml_startup(argv);
}

/* arg1 is a C++ Exp * cast to void ptr.  arg2 is a STP VC cast to
   void * */
int query_ml_stp_exp_vc(void *arg1, void * arg2)
{
  Exp *exp; /* this is _not_ a C++ Exp..it's a libasmir.idl Exp */
  Vc *vc;
  CAMLparam0();
  CAMLlocal3(ml_e, ml_vc, ret);
  
  exp = (Exp *) arg1;
  vc = (Vc *) arg2;
  static value *closure_query_stp_exp = NULL;

  if(closure_query_stp_exp == NULL){
    closure_query_stp_exp = caml_named_value("cpp_exp_to_stp_handle");
  }

  if(closure_query_stp_exp == NULL){
    fprintf(stderr, 
	    "caml_named_value lookup for cpp_exp_to_stp_handle failed!\n");
    exit(-1);
  }
  /* translation done by camlidl */
  ml_e = camlidl_c2ml_libasmir_Exp((Exp *) &exp, NULL);
  ml_vc = camlidl_c2ml_libstp_Vc((Vc *) &vc, NULL);
 
  ret = caml_callback2(*closure_query_stp_exp, ml_vc, ml_e);
  CAMLreturn(Bool_val(ret));
}

/* arg1 is a C++ Exp * cast to void ptr.  arg2 is a STP VC cast to
   void * */
int query_ml_stp_exp_vc_deend(void *arg1, void * arg2)
{
  Exp *exp; /* this is _not_ a C++ Exp..it's a libasmir.idl Exp */
  Vc *vc;
  CAMLparam0();
  CAMLlocal3(ml_e, ml_vc, ret);
  
  exp = (Exp *) arg1;
  vc = (Vc *) arg2;
  static value *closure_query_stp_exp = NULL;

  if(closure_query_stp_exp == NULL){
    closure_query_stp_exp = caml_named_value("cpp_exp_to_stp_deend_handle");
  }

  if(closure_query_stp_exp == NULL){
    fprintf(stderr, 
	    "caml_named_value lookup for cpp_exp_to_stp_deend_handle failed!\n");
    exit(-1);
  }
  /* translation done by camlidl */
  ml_e = camlidl_c2ml_libasmir_Exp((Exp *) &exp, NULL);
  ml_vc = camlidl_c2ml_libstp_Vc((Vc *) &vc, NULL);
 
  ret = caml_callback2(*closure_query_stp_exp, ml_vc, ml_e);
  CAMLreturn(Bool_val(ret));
}

char *query_ml_stp_exp_string(void *arg1, void *arg2)
{
  Exp *exp; /* this is _not_ a C++ Exp..it's a libasmir.idl Exp */
  Vc *vc;
  CAMLparam0();
  CAMLlocal3(ml_e, ml_vc, ret);
  
  exp = (Exp *) arg1;
  vc = (Vc *) arg2;
  static value *closure_query_stp_exp = NULL;

  if(closure_query_stp_exp == NULL){
    closure_query_stp_exp = caml_named_value("cpp_exp_to_stp_string");
  }

  if(closure_query_stp_exp == NULL){
    fprintf(stderr, 
	    "caml_named_value lookup for cpp_exp_to_stp_string failed!\n");
    exit(-1);
  }
  /* translation done by camlidl */
  ml_e = camlidl_c2ml_libasmir_Exp((Exp *) &exp, NULL);
  ml_vc = camlidl_c2ml_libstp_Vc((Vc *) &vc, NULL);
 
  ret = caml_callback2(*closure_query_stp_exp, ml_vc, ml_e);
  CAMLreturn(String_val(ret));
}

int query_ml_stp_exp_file(void *arg1,char *file_name, int add_query)
{
  Exp *exp; /* this is _not_ a C++ Exp..it's a libasmir.idl Exp */
  // Vc *vc;
  CAMLparam0();
  CAMLlocal4(ml_e, ret, ml_str, ml_addquery);
  
  exp = (Exp *) arg1;
  // vc = (Vc *) arg2;
  static value *closure_query_stp_exp = NULL;

  if(closure_query_stp_exp == NULL){
    closure_query_stp_exp = caml_named_value("cpp_exp_to_stp_file");
  }

  if(closure_query_stp_exp == NULL){
    fprintf(stderr, 
	    "caml_named_value lookup for cpp_exp_to_stp_file failed!\n");
    exit(-1);
  }
  /* translation done by camlidl */
  ml_e = camlidl_c2ml_libasmir_Exp((Exp *) &exp, NULL);
  // ml_vc = camlidl_c2ml_libstp_Vc((Vc *) &vc, NULL);
  ml_str = caml_copy_string(file_name);
  // XXX: ml_file = camlidl_c2ml_lib
  ml_addquery = Val_int(add_query);
 
  // ret = caml_callback2(*closure_query_stp_exp, ml_vc, ml_e);
  caml_callback3(*closure_query_stp_exp, ml_e, ml_str, ml_addquery);
  CAMLreturn(Int_val(ret));
}

int query_ml_stp_exp(void *arg){
  Exp *exp;  /* this is _not_ a C++ Exp..it's a libasmir.idl Exp */
  CAMLparam0();
  CAMLlocal2(ml_e, ret); // type value

  //  CAMLlocal1(ret);
  exp = (Exp *) arg;

  static value *closure_query_stp_exp = NULL;

  if(closure_query_stp_exp == NULL){
    closure_query_stp_exp = caml_named_value("query_stp_cpp_exp");
  }

  if(closure_query_stp_exp == NULL){
    fprintf(stderr, 
	    "caml_named_value lookup for query_stp_exp failed!\n");
    exit(-1);
  }
  /* translation done by camlidl */
  /* *ml_e points to the same location as *exp */
  ml_e =camlidl_c2ml_libasmir_Exp((Exp *) &exp, NULL);
 
  ret = caml_callback(*closure_query_stp_exp, ml_e);
  CAMLreturn(Bool_val(ret));
}

