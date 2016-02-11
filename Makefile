.PHONY: clean test

CC = gcc

runtime.o: runtime.c runtime.h cheney.h
	$(CC) -c -g -std=c99 runtime.c

test: runtime
	racket run-tests.rkt

clean:
	rm -f *.o *.out *.exe *.s *~
