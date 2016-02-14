.PHONY: clean test

CC     = gcc
RACKET = racket
RM     = rm

runtime.o: runtime.c runtime.h rgscott_cheney.h rgscott_utilities.h
	$(CC) -c -g -std=c99 runtime.c

test: runtime.o
	$(RACKET) run-tests.rkt

clean:
	$(RM) -f *.o *.out *.exe *.s *~
