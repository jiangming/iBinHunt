# $Id: Makefile 1022 2007-04-05 20:54:27Z dbrumley $

export OCAMLMAKEFILE=OCamlMakefile
export VINE_OCAMLDIR=../ocaml

export bindiff_SOURCES = \
	../bindiff/mycg.ml \
	
# ocamlfind packages required
export PACKS = gdome2 str ocamlgraph extlib unix sqlite3
export LIBS = vine 
export INCDIRS = $(VINE_OCAMLDIR)

# Include sources from ../ocaml in the automatically generated dependencies.
# It seems like there should be a more elegant way to do this.
export OCAMLDEP = ocamldep -I $(VINE_OCAMLDIR)

#trace_diff_old
# default subprojects to build
ifndef SUBPROJS
	export SUBPROJS = irtrans toir tocfg evaluator irutil callstrings elfutil \
	callgraph trace_reader idadb_reader ir2c\
	tainttree appreplay appreplay_old dynslicer wputil chop stackstats \
	hookgraph valset_ir callarginfo troubleshooter dotchop \
	statereader bb_chop trace_diff  negstp trace_diff_old srcline save_ir trace_diff_old2 syntac readscore stp_test to_dot \
	binhunt_flat_ir trace_reader_filter
endif



# Our IR utility driver used for regression tests.  This is a good
# place to add options to test your modules, especially for regression
# tests.  

define PROJ_bb_chop
	RESULT=bb_chop
	SOURCES = $(bindiff_SOURCES) exectrace.ml bb_chop.ml 
	DOC_FILES=$(SOURCES)
endef
export PROJ_bb_chop

define PROJ_to_dot
	RESULT=to_dot
	SOURCES = $(bindiff_SOURCES) exectrace.ml to_dot.ml 
	DOC_FILES=$(SOURCES)
endef
export PROJ_to_dot


define PROJ_stackstats
	RESULT=stackstats
	SOURCES = stackstats.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_stackstats

define PROJ_irutil
	RESULT=irutil
	SOURCES = irutil.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_irutil

define PROJ_evaluator
	RESULT=evaluator
	SOURCES = evaluator.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_evaluator

define PROJ_callstrings
	RESULT=callstrings
	SOURCES = callstrings.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_callstrings


define PROJ_ir2c
	RESULT=ir2c
	SOURCES = ir2c.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_ir2c

define PROJ_callgraph
	RESULT=callgraph
	SOURCES = callgraph.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_callgraph

define PROJ_tocfg
	RESULT=tocfg
	SOURCES = tocfg.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_tocfg

define PROJ_elfutil
	RESULT=elfutil
	SOURCES=elfutil.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_elfutil

define PROJ_trace_reader
	RESULT=trace_reader
	SOURCES=trace_reader.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_trace_reader

define PROJ_trace_reader_filter
	RESULT=trace_reader_filter
	SOURCES=trace_reader_filter.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_trace_reader_filter

define PROJ_tainttree
	RESULT=tainttree
	SOURCES=tainttree.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_tainttree

define PROJ_hookgraph
	RESULT=hookgraph
	SOURCES=hookgraph.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_hookgraph

define PROJ_idadb_reader
	RESULT=idadb_reader
	SOURCES=idadb_reader.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_idadb_reader

#trace_diff.mli trace_diff.ml 
define PROJ_appreplay
        RESULT=appreplay
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  appreplay.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_appreplay

define PROJ_appreplay_old
        RESULT=appreplay_old
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  appreplay_old.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_appreplay_old

define PROJ_trace_diff
        RESULT=trace_diff
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  trace_diff.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_trace_diff

define PROJ_stp_test
        RESULT=stp_test
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  stp_test.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_stp_test

define PROJ_trace_diff_old
        RESULT=trace_diff_old
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  trace_diff_old.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_trace_diff_old

define PROJ_trace_diff_old2
        RESULT=trace_diff_old2
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  trace_diff_old2.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_trace_diff_old2

define PROJ_syntac
        RESULT=syntac
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  syntac.ml 
        INCDIRS += ../stp/ocaml ../stp 
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_syntac


define PROJ_save_ir
        RESULT=save_ir
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  save_ir.ml
        INCDIRS += ../stp/ocaml ../stp
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_save_ir

define PROJ_binhunt_flat_ir
        RESULT=binhunt_flat_ir
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  binhunt_flat_ir.ml
        INCDIRS += ../stp/ocaml ../stp
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_binhunt_flat_ir


define PROJ_negstp
        RESULT=negstp
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  negstp.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_negstp

define PROJ_readscore
        RESULT=readscore
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  readscore.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_readscore

define PROJ_srcline
        RESULT=srcline
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                temu_state.ml  srcline.ml
        INCDIRS += ../stp/ocaml ../stp 
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc
        THREADS = pthread
        DOC_FILES=$(SOURCES)
endef
export PROJ_srcline

define PROJ_valset_ir
	RESULT=valset_ir
        SOURCES=$(common_SOURCES) $(vinewp_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
		valset.ml valset_ir.ml
	INCDIRS += ../stp/ocaml ../stp
	EXTLIBDIRS += ../stp ../stp/ocaml
	LIBS += stpvc vine
endef
export PROJ_valset_ir

define PROJ_dynslicer
        RESULT=dynslicer
        INCDIRS += ../stp/ocaml ../stp
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc vine
        SOURCES=$(common_SOURCES) \
                $(vineexectrace_SOURCES) exectrace.ml \
                trace_slice.ml dynslicer.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_dynslicer


# subproject specific bits
define PROJ_irtrans
        RESULT=irtrans
        SOURCES=$(common_SOURCES) exectrace.ml irtrans.ml
        DOC_FILES=$(SOURCES)
endef
export PROJ_irtrans

define PROJ_countpaths
	RESULT=countpaths
	SOURCES = countpaths.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_countpaths

define PROJ_toir
	RESULT=toir
	SOURCES = utils_common.ml toir.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_toir

define PROJ_wputil
	RESULT=wputil
	SOURCES = $(common_SOURCES) $(vinewp_SOURCES) wputil.ml
        INCDIRS += ../stp/ocaml ../stp #../appreplay
        EXTLIBDIRS += ../stp ../stp/ocaml
        LIBS += stpvc vine
	DOC_FILES=$(SOURCES)
endef
export PROJ_wputil

define PROJ_chop
	RESULT=chop
	SOURCES = utils_common.ml chop.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_chop

define PROJ_test_vsa
	RESULT=test_vsa
	SOURCES = test_vsa.ml
endef
export PROJ_test_vsa

define PROJ_test_regionvsa
	RESULT=test_regionvsa
	SOURCES = test_regionvsa.ml
endef
export PROJ_test_regionvsa

define PROJ_test_almostvsa
	RESULT=test_almostvsa
	SOURCES = test_almostvsa.ml
endef
export PROJ_test_almostvsa

define PROJ_callarginfo
	RESULT=callarginfo
	SOURCES=callarginfo.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_callarginfo

define PROJ_troubleshooter
	RESULT=troubleshooter
	SOURCES=$(common_SOURCES) exectrace.ml trace_slice.ml troubleshooter.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_troubleshooter

define PROJ_dotchop
	RESULT=dotchop
	SOURCES=dot_helper.ml dotchop.ml
	DOC_FILES=$(SOURCES)
endef
export PROJ_dotchop

define PROJ_statereader
        RESULT=state_reader
        SOURCES=temu_state.ml state_reader.ml
        DOC_FILES=$(SOURCES)
endef
export PROJ_statereader


# suffix for bytecode (which when we make all is debug code)
export BCSUFFIX = .dbg

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
