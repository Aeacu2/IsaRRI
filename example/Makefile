GMP ?= /opt/homebrew
CC = clang
ROOT := ..

isarri_example: isarri_example.c $(ROOT)/export/isarri.ll $(ROOT)/runtime/lib_isabelle_llvm.c
	$(CC) -O2 -w -I$(ROOT)/export -I$(GMP)/include isarri_example.c $(ROOT)/export/isarri.ll $(ROOT)/runtime/lib_isabelle_llvm.c -L$(GMP)/lib -lgmp -o $@

clean:
	rm -f isarri_example

.PHONY: clean
