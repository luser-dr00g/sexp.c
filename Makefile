all: sexp
CFLAGS+= -Wno-implicit-int -Wno-implicit-function-declaration -g

test: sexp
	./sexp<test
