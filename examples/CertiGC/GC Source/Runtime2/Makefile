CC=gcc
CFLAGS=  -g -O3

# CFLAGS=  -m32 -g -O3   ///use this for 32-bit x86 mode


all: gc.o nogc.o gctest gctest2 gctest2_float gctest2_string ocamltest ocamltest-nonopt ocamltest_float ocamltest_float-nonopt ocamltest_string ocamltest_string-nonopt

time: all
	time ./gctest 10000000
	time ./gctest2 10000000
	time ./ocamltest 10000000
	time ./ocamltest-nonopt 10000000

timefloat: all
	time ./gctest2_float 1000000
	time ./ocamltest_float 1000000
	time ./ocamltest_float-nonopt 1000000

timestring: all
	time ./gctest2_string 10000
	time ./ocamltest_string 10000
	time ./ocamltest_string-nonopt 10000

gctest: testmain.o gctest.o gc.o
	${CC} ${CFLAGS} testmain.o gctest.o gc.o -o gctest

gctest2: gctest2.o gc.o
	${CC} ${CFLAGS} testmain.o gctest2.o gc.o -o gctest2

gctest2_float: gctest2_float.o gc.o
	${CC} ${CFLAGS} testmain.o gctest2_float.o gc.o -o gctest2_float

gctest2_string: gctest2_string.o gc.o
	${CC} ${CFLAGS} testmain.o gctest2_string.o gc.o -o gctest2_string

ocamltest: ocamltest.ml
	ocamlopt ocamltest.ml -o ocamltest

ocamltest-nonopt: ocamltest.ml
	ocamlc ocamltest.ml -o ocamltest-nonopt

ocamltest_float: ocamltest_float.ml
	ocamlopt ocamltest_float.ml -o ocamltest_float

ocamltest_float-nonopt: ocamltest.ml
	ocamlc ocamltest_float.ml -o ocamltest_float-nonopt

ocamltest_string: ocamltest_string.ml
	ocamlopt ocamltest_string.ml -o ocamltest_string

ocamltest_string-nonopt: ocamltest.ml
	ocamlc ocamltest_string.ml -o ocamltest_string-nonopt

testmain.o: testmain.c config.h values.h gc.h
gc.o: gc.c config.h values.h gc.h
nogc.o: nogc.c config.h values.h gc.h
gctest.o: gctest.c config.h values.h gc.h
gctest2.o: gctest2.c config.h values.h gc.h
gctest2_float.o: gctest2_float.c config.h values.h gc.h
gctest2_string.o: gctest2_string.c config.h values.h gc.h

gctest.s: gctest.c config.h values.h
	${CC} ${CFLAGS} -S gctest.c

gctest2.s: gctest2.c config.h values.h
	${CC} ${CFLAGS} -S gctest2.c

gctest2_string.s: gctest2_string.c config.h values.h
	${CC} ${CFLAGS} -S gctest2_string.c

clean:
	rm -f *.o gctest gctest2 gctest2_float gctest2_string gctest.s ocamltest ocamltest-nonopt ocamltest_float ocamltest_float-nonopt ocamltest_string ocamltest_string-nonopt *.cmi *.cmx *.cmo;
	rm -rf oprofile_data
