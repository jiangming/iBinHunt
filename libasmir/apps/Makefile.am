bin_PROGRAMS = \
	disassembler \
	print-ir \
	translate-function \
	symeval \
	gen_thunks
#	print-stripped

disassembler_SOURCES = disassembler.cpp
print_ir_SOURCES = print-ir.cpp ir_printer.cpp
#print_stripped_SOURCES = print-stripped.cpp ir_printer.cpp
translate_function_SOURCES = translate-function.cpp
symeval_SOURCES = symeval.cpp
gen_thunks_SOURCES = gen_thunks.cpp
LDADD =  -lasmir -lvex -lbfd -liberty -lopcodes
AM_LDFLAGS = -L../src -L@VEX_DIR@ -L@BINUTILS_DIR@
AM_CXXFLAGS = -I../src/include  -I@VEX_DIR@/pub -I@BINUTILS_DIR@

# these executables should depend on libasmir, since they link it in
# statically.
$(bin_PROGRAMS): ../src/libasmir.a
