
ifeq (test,$(firstword $(MAKECMDGOALS)))
  TEST_ARGS := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  $(eval $(TEST_ARGS):dummy;@:)
endif

dummy: # ...
    # ...

.PHONY: clean test paper

CC     = gcc
RACKET = racket
RM     = rm

runtime.o: runtime.c runtime.h rgscott_cheney.h rgscott_utilities.h
	$(CC) -c -g -std=c99 runtime.c

# to run all tests
# >> make test
# to run a single test
# >> make test r3_4
test: runtime.o
	$(RACKET) run-tests.rkt $(TEST_ARGS)

clean:
	$(RM) -f *.o *.out *.exe *.s *~

proposal:
	pdflatex final-project/proposal.tex
