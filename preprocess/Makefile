# $Id: Makefile 786 2007-03-09 01:38:13Z dbrumley $

export OCAMLMAKEFILE=../ocaml/OCamlMakefile
include ../libasmir/makefile.inc

# common sources
export common_SOURCES = \
	../ocaml/debug.mli ../ocaml/debug.ml \
	../ocaml/symbols.mli ../ocaml/symbols.ml \
	../ocaml/vine_util.mli ../ocaml/vine_util.ml \
	../ocaml/vine.ml ../ocaml/vine.mli \
	../ocaml/vine_alphavary.mli ../ocaml/vine_alphavary.ml \
	../ocaml/vine_typecheck.mli ../ocaml/vine_typecheck.ml \
	../ocaml/vine_opt.ml \
	../ocaml/stp.ml \
	../ocaml/vine_absyn.mli ../ocaml/vine_absyn.ml \
	../ocaml/vine_grammar.mly \
	../ocaml/vine_lexer.mll \
	../ocaml/libasmir.idl \
	../ocaml/asmir.ml \
	../ocaml/vine_memory2array.ml \
	../ocaml/vine_parser.mli ../ocaml/vine_parser.ml \
	../ocaml/dataflow.mli ../ocaml/dataflow.ml \
	../ocaml/dominator.ml \
	../ocaml/vine_cfg.mli ../ocaml/vine_cfg.ml \
	../ocaml/vine_eval.mli ../ocaml/vine_eval.ml \
	../ocaml/vine_unroll.ml \
	../ocaml/ssa.mli ../ocaml/ssa.ml \
	../ocaml/vine_dataflow.mli ../ocaml/vine_dataflow.ml \
        ../ocaml/vine_idadb.mli ../ocaml/vine_idadb.ml \
	../ocaml/vine_tovine.mli ../ocaml/vine_tovine.ml \
	../ocaml/vine_stpvc.mli ../ocaml/vine_stpvc.ml \
	../ocaml/vine_chop.mli ../ocaml/vine_chop.ml \
	../ocaml/gcl.ml \
	../ocaml/wp.ml \
	../ocaml/vine_pp.ml



# ocamlfind packages required
export PACKS = gdome2 str ocamlgraph extlib unix sqlite3
export YFLAGS = -v

include ../libasmir/makefile.inc
export CLIBS = asmir vex opcodes bfd iberty stdc++ #exectrace
export CFLAGS = -g
export LDFLAGS = $(LIBASMIR_LDFLAGS) 
export CLIBFLAGS= $(LDFLAGS)
export LIBDIRS = ../libasmir/src # ../appreplay ../stp ../stp/ocaml

# default subprojects to build
ifndef SUBPROJS
#irtrans is so much more useful than parseir for debugging...
	export SUBPROJS = convert convert2 test fromDG
endif


define PROJ_convert
	RESULT=convert
	SOURCES = $(common_SOURCES)  mycg.ml utils_common.ml mytoir.ml convert.ml  
	INCDIRS = ../stp/ocaml 
	EXTLIBDIRS += ../stp ../stp/ocaml
	LIBS = stpvc
        THREADS = pthread
	DOC_FILES=$(SOURCES)
endef
export PROJ_convert


define PROJ_convert2
	RESULT=convert2
	SOURCES = $(common_SOURCES)  mycg.ml utils_common.ml mytoir.ml convert2.ml  
	INCDIRS = ../stp/ocaml 
	EXTLIBDIRS += ../stp ../stp/ocaml
	LIBS = stpvc
        THREADS = pthread
	DOC_FILES=$(SOURCES)
endef
export PROJ_convert2


define PROJ_test
	RESULT=test
	SOURCES = $(common_SOURCES)  mycg.ml utils_common.ml mytoir.ml test.ml  
	INCDIRS = ../stp/ocaml 
	EXTLIBDIRS += ../stp ../stp/ocaml
	LIBS = stpvc
        THREADS = pthread
	DOC_FILES=$(SOURCES)
endef
export PROJ_test

define PROJ_fromDG
	RESULT= fromDG
	SOURCES = fromDG.ml  
	INCDIRS = 
	EXTLIBDIRS += ../stp ../stp/ocaml 
	LIBS = 
        THREADS = pthread
	DOC_FILES=$(SOURCES)
endef
export PROJ_fromDG

export  BCSUFFIX = .dbg 
all: nc dc

# You may also tell "make" at the command-line what kind of target to
# produce (e.g. "make nc").  Here all the possibilities with shortcuts
# between parenthesis:
# 
#    * byte-code                     (bc)
#    * byte-code-nolink              (bcnl)   - no linking stage
#    * byte-code-library             (bcl)
#    * native-code                   (nc)
#    * native-code-nolink            (ncnl)   - no linking stage
#    * native-code-library           (ncl)
#    * debug-code                    (dc)
#    * debug-code-nolink             (dcnl)   - no linking stage
#    * debug-code-library            (dcl)
#    * profiling-byte-code           (pbc)
#    * profiling-byte-code-library   (pbcl)
#    * profiling-native-code         (pnc)
#    * profiling-native-code-library (pncl)
#    * byte-code-dll                 (bcd)
#    * native-code-dll               (ncd)
#    * pack-byte-code              (pabc)
#    * pack-native-code            (panc)
#    * toplevel interpreter          (top)
#    * subprjs



%:
	make -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@


#include $(OCAMLMAKEFILE)
