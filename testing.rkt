#lang racket

(require "utilities.rkt" "interp.rkt")

(provide all-tests passes->compiler)

; [Pass] -> Compiler
(define passes->compiler
  (lambda (wrap-program passes)
    (foldl (match-lambda**
            [((list _ pass _) q-pass) (compose1 pass q-pass)])
           (if wrap-program
               (curry list `program)
               identity)
           passes)))


;; are we gonna use these ??

;; (define uniquify->print            (passes->compiler #t uniquify-passes))
;; (define flatten->print             (passes->compiler #t flatten-passes))
;; (define select-instructions->print (passes->compiler #f select-instructions-passes))
;; (define assign-homes->print        (passes->compiler #f assign-homes-passes))
;; (define patch-instructions->print  (passes->compiler #f patch-instructions-passes))

(define irange
  (lambda (b e)
    (range b (+ e 1))))

(define tests
  (lambda (caption passes interp name range)
    (lambda ()
      (interp-tests caption passes interp name range)
      (compiler-tests caption passes name range)

      )))

(define all-tests
  (lambda (passes)

    (define uniquify-passes            passes)
    (define flatten-passes             (drop uniquify-passes 1))
    (define select-instructions-passes (drop flatten-passes 1))
    (define assign-homes-passes        (drop select-instructions-passes 1))
    (define patch-instructions-passes  (drop assign-homes-passes 1))


    (define r0-range (irange 1 4))
    (define r0-tests
      (tests "Jeremy's tests" uniquify-passes interp-scheme "r0" r0-range))

    (define r1-range (irange 1 19))
    (define r1-tests
      (tests "Jeremy's tests 2: electric boogaloo" uniquify-passes interp-scheme "r1" r1-range))

    (define r1a-range (irange 1 8))
    (define r1a-tests
      (tests "Jeremy's tests 3: stand up and testify" uniquify-passes interp-scheme "r1a" r1a-range))
    
    (define uniquify-range (irange 1 5))
    (define uniquify-tests
      (tests "uniquify" uniquify-passes interp-scheme "uniquify" uniquify-range))

    (define flatten-range (irange 1 3))
    (define flatten-tests
      (tests "flatten" flatten-passes interp-scheme "flatten" flatten-range))

    (define torture-range (irange 1 2))
    (define torture-tests
      (tests "torture" uniquify-passes interp-scheme "torture" torture-range))

    (r0-tests)
    (r1-tests)
    (r1a-tests)
    (uniquify-tests)
    (flatten-tests)
    (torture-tests)
    (display "all tests passed!") (newline)))
