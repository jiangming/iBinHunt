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
        ../utils/utils_common.mli ../utils/utils_common.ml     

export vinewp_SOURCES = \
	../ocaml/gcl.ml \
	../ocaml/wp.ml 

export bindiff_SOURCES = \
	../bindiff/mycg.ml \


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
	export SUBPROJS = callinsts
endif


define PROJ_callinsts
	RESULT=callinsts
	SOURCES = $(common_SOURCES) $(vinewp_SOURCES) $(bindiff_SOURCES) callinsts.ml
	INCDIRS = ../stp/ocaml ../bindiff/
	EXTLIBDIRS += ../stp ../stp/ocaml
	LIBS = stpvc
        THREADS = pthread
	DOC_FILES=$(SOURCES)
endef
export PROJ_callinsts

export BCSUFFIX = .dbg
all: nc dc

%:
	make -f $(OCAMLMAKEFILE) subprojs SUBTARGET=$@


#include $(OCAMLMAKEFILE)
