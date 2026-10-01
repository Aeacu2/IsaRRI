GMP ?= /opt/homebrew
CC = clang
ROOT := ..
CFLAGS = -O2 -I$(ROOT)/export -I$(GMP)/include

test_isarri_simple: test_isarri_simple.c isarri_simple.c isarri_simple.h $(ROOT)/export/isarri.ll $(ROOT)/runtime/lib_isabelle_llvm.c
	$(CC) $(CFLAGS) -w test_isarri_simple.c isarri_simple.c $(ROOT)/export/isarri.ll $(ROOT)/runtime/lib_isabelle_llvm.c -L$(GMP)/lib -lgmp -lpthread -o $@

test: test_isarri_simple
	./test_isarri_simple

clean:
	rm -f test_isarri_simple

.PHONY: test clean
