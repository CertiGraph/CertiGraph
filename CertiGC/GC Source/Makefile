CC=gcc
CFLAGS=  -g -O3

# CFLAGS=  -m32 -g -O3   ///use this for 32-bit x86 mode


all: gc_stack.o nogc.o gctest gctest2 ocamltest ocamltest-nonopt

time: all
	time ./gctest 10000000
	time ./gctest2 10000000
	time ./ocamltest 10000000
	time ./ocamltest-nonopt 10000000

gctest: testmain.o gctest.o gc_stack.o
	${CC} ${CFLAGS} testmain.o gctest.o gc_stack.o -o gctest

gctest2: gctest2.o gc_stack.o
	${CC} ${CFLAGS} testmain.o gctest2.o gc_stack.o -o gctest2

ocamltest: ocamltest.ml
	ocamlopt ocamltest.ml -o ocamltest

ocamltest-nonopt: ocamltest.ml
	ocamlc ocamltest.ml -o ocamltest-nonopt


testmain.o: testmain.c config.h values.h gc_stack.h
gc_stack.o: gc_stack.c config.h values.h gc_stack.h
nogc.o: nogc.c config.h values.h gc_stack.h
gctest.o: gctest.c config.h values.h gc_stack.h
gctest2.o: gctest2.c config.h values.h gc_stack.h

gctest.s: gctest.c config.h values.h
	${CC} ${CFLAGS} -S gctest.c

gctest2.s: gctest2.c config.h values.h
	${CC} ${CFLAGS} -S gctest2.c

clean:
	rm -f *.o gctest gctest2 gctest.s ocamltest ocamltest-nonopt *.cmi *.cmx *.cmo;
	rm -rf oprofile_data

