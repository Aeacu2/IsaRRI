GMP ?= /opt/homebrew
CC = clang
ROOT := ../..

time_one: time_one.c $(ROOT)/export/isarri.ll $(ROOT)/runtime/lib_isabelle_llvm.c
	$(CC) -O2 -w -I$(ROOT)/export -I$(GMP)/include time_one.c $(ROOT)/export/isarri.ll $(ROOT)/runtime/lib_isabelle_llvm.c -L$(GMP)/lib -lgmp -o $@

clean:
	rm -f time_one

.PHONY: clean
