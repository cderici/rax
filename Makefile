.PHONY: clean

runtime: runtime.o
	gcc -c -g -std=c99 runtime.c

test: runtime
	racket compiler.rkt

clean:
	rm -f *.o *.out *.exe *.s *~
