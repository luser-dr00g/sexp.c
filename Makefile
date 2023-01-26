CFLAGS ?= -g -Wno-implicit-int -Wno-implicit-function-declaration
CFLAGS += -std=gnu99

.PHONY: all test dump

all: sexp

test: sexp
	./sexp<test 2>error
	@echo error: ; cat error

dump:
	xxd mem.dump
	od --endian=little -v -t d4 -A n mem.dump
