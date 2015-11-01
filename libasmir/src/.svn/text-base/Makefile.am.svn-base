# Owned and copyright BitBlaze, 2007. All rights reserved.
# Do not copy, disclose, or distribute without explicit written
# permission.


RANLIB = @RANLIB@
lib_LIBRARIES = libasmir.a
#libasm.a 
#lib_LTLIBRARIES = libasmir.la
AM_CFLAGS = -I@VEX_DIR@/pub -I./include -fPIC
AM_CXXFLAGS = -I@VEX_DIR@/pub -I./include -fPIC


libasmir_a_SOURCES = ./util/debug.cpp \
	./util/info.cpp \
	./disasm/objdump.cpp \
	./disasm/asm_program.cpp \
	./vex/vexmem.cpp \
	./vex/irtoir.cpp \
	./vex/irtoir-i386.cpp \
	./vex/irtoir-arm.cpp \
	./vex/irtoir_c.cpp \
	./vex/vexir.cpp \
	./vex/gen_thunks.cpp \
	./ir/cfg.cpp \
	./ir/typecheck_ir.cpp \
	./ir/ir_program.cpp \
	./ir/stmt.cpp \
	./ir/stmt_c.cpp \
	./ir/irdeendianizer.cpp \
	./ir/defusevisitor.cpp \
	./ir/exp.cpp \
	./ir/exp_c.cpp \
	./ir/ssa.cpp \
	./ir/irvisitor.cpp \
	./ir/const_simplify_exp.cpp \
	./ir/deadcode.cpp \
	./ir/ir2xml.cpp \
	./ir/translate.cpp

#libasm_a_SOURCES = \
#        ./disasm/objdump.cpp \
#        ./disasm/junk.cpp \
#        ./disasm/disasm-i386.cpp \
#        ./disasm/asm_program.cpp 

