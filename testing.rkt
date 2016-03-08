#lang racket

(require "utilities.rkt" "interp.rkt" "typecheck.rkt")

(provide all-tests passes->compiler)

; (debug-level 2)

; [Pass] -> Compiler
(define passes->compiler
  (lambda (wrap-program passes)
    (foldl (match-lambda**
            [((list _ pass _) q-pass) (compose1 pass q-pass)])
           (if wrap-program
               (λ (e) `(program (type ,(typechecker e)) ,e))
               identity)
           passes)))

(define irange
  (lambda (b e)
    (range b (+ e 1))))

(define tests
  (lambda (caption tc passes interp name range)
    (lambda ()
      ; (interp-tests caption tc passes interp name range)
      (compiler-tests caption tc passes name range))))

(define all-tests
  (lambda (passes)

    (define r0-range (irange 1 4))
    (define r0-tests
      (tests "Jeremy's tests" typechecker passes interp-scheme "r0" r0-range))

    (define r1-range (irange 1 21))
    (define r1-tests
      (tests "Jeremy's tests 2: electric boogaloo" typechecker passes interp-scheme "r1" r1-range))

    (define r1a-range (irange 1 8))
    (define r1a-tests
      (tests "Jeremy's tests 3: stand up and testify" typechecker passes interp-scheme "r1a" r1a-range))

    (define r2-range (irange 1 23))
    (define r2-tests
      (tests "Jeremy's tests 4: 4 Fast 4 Furious" typechecker passes interp-scheme "r2" r2-range))

    (define r2c-range (irange 1 2))
    (define r2c-tests
      (tests "Caner's R2 tests" typechecker passes interp-scheme "r2c" r2c-range))

    (define r3-range (irange 1 15))
    (define r3-tests
      (tests "Jeremy's tests 5: I can't think of a creative subtitle"
             typechecker passes interp-scheme "r3" r3-range))

    (define r3c-range (irange 1 5))
    (define r3c-tests
      (tests "Ryan's R3 tests" typechecker passes interp-scheme "r3c" r3c-range))

    (define r4c-range (irange 1 7)) ; (irange 1 8))
    (define r4c-tests
      (tests "Ryan's R4 tests" typechecker passes interp-scheme "r4c" r4c-range))

    (define r4-range (irange 1 19))
    (define r4-tests
      (tests "Jeremy's R4 tests" typechecker passes interp-scheme "r4" r4-range))

    (define r5c-range (irange 1 2))
    (define r5c-tests
      (tests "Ryan's R5 tests" typechecker passes interp-scheme "r5c" r5c-range))

    (define uniquify-range (irange 1 5))
    (define uniquify-tests
      (tests "uniquify" typechecker passes interp-scheme "uniquify" uniquify-range))

    (define flatten-range (irange 1 3))
    (define flatten-tests
      (tests "flatten" typechecker passes interp-scheme "flatten" flatten-range))

    (define tc-range (irange 1 12))
    (define tc-tests
      (tests "typecheck" typechecker passes interp-scheme "tc" tc-range))

    (define torture-range (irange 1 3))
    (define torture-tests
      (tests "torture" typechecker passes interp-scheme "torture" torture-range))

    (r0-tests)
    (r1-tests)
    (r1a-tests)
    (r2-tests)
    (r2c-tests)
    (r3-tests)
    (r3c-tests)
    (r4-tests)
    (r4c-tests)
    (r5c-tests)
    (uniquify-tests)
    (flatten-tests)
    (tc-tests)
    ;(torture-tests)
    (display "all tests passed!") (newline)))
