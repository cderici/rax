## Rax

A (small subset of) Racket to x86_64 nanopass compiler with a static type checker and a (two-space copying) GC, written in Racket with some C runtime support. The source language has integers, booleans, tuples, vectors, comparisons, lexical closures, etc.

Here are the passes:

* **typecheck** : a relatively simple one-directional static type checker
* **uniquify** : make sure that all the variables have unique names (similar to maintaining a symbol table)
* **reveal-functions** : separate the function applications from primitive applications
* **convert-to-closure** : turn functions into toplevel closures, i.e. vector with a function pointer and free variables
* **flatten** : A-normalization + some extra bookkeeping
* **expose-allocation** : identify allocations and add a check for `collection-needed?` to invoke the GC when necessary
* **uncover-call-live-roots** : discover the roots that are alive during the call to GC (so we can copy them to the shadow stack/root stack)
* **select-instructions** : start transitioning to x86, e.g., `(assign x (+ 10 32)) -> (addq (int 10) (var x))`
* **assign-homes** : register allocation
-- *uncover-live* : liveness analysis
-- *build-interference* : generate an interference graph (which variables interfere with each other)
-- *allocate-registers* : graph-coloring, and generate code to `movq` things into the registers `rbx,rcx,rdx...` (also for spills)
* **patch-instructions** - e.g., instructions such as `movq` requires the second argument to be a register.
* **print-x86** - code gen


To run the tests, simply invoke `make test` from the top-level directory. (Assumes a Racket binary)


Authors: Caner Derici ([cderici](https://github.com/cderici)) and Ryan Scott ([RyanGlScott](https://github.com/RyanGlScott))