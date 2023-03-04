CFLAGS ?= -g -Wno-implicit-int -Wno-implicit-function-declaration
CFLAGS += -std=gnu99

.PHONY: all test dump clean analyze

all: sexp

clean:
	rm -f sexp mem.dump

test: sexp
	./sexp<test 2>error
	@echo error: ; cat error

mem.dump: sexp
	./sexp -d 15 -s <small

dump: mem.dump
	od --endian=little -v -t x4z -A x mem.dump

analyze: mem.dump
	./memanalyze.awk mem.dump
