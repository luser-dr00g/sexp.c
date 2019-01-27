all: sexp
CFLAGS+= $(cflags)
CFLAGS+= -Wno-implicit-int -Wno-implicit-function-declaration -g

test: sexp
	./sexp<test
