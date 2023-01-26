CFLAGS ?= -g -Wno-implicit-int -Wno-implicit-function-declaration
CFLAGS += -std=gnu99

all: sexp

test: sexp
	./sexp<test 2>error
	@echo error: ; cat error
