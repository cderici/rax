#lang racket

(require "utilities.rkt" "interp.rkt")

(provide all-tests)

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


;; removes extra program line if there is one
(define call-with-caution
  (lambda (func)
    (lambda (sexp)
      (match  sexp
        [`(program (program (,v ...) ,assgn ... (return ,e)))
         (func `(program ,v ,@assgn (return ,e)))]
        [else (func sexp)]))))

(define cautious-passes
  (lambda (passes)
    (map (lambda (pass)
           (list (car pass)
                 (call-with-caution (cadr pass))
                 (caddr pass)))
         passes)))

(define tests
  (lambda (caption passes interp name range)
    (lambda ()
      (interp-tests caption
                    (cautious-passes passes)
                    (call-with-caution interp)
                    name range)
      ;(compiler-tests caption passes        name range)
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

    (define r1-range (irange 1 5))
    (define r1-tests
      (tests "arithmetic with let" uniquify-passes interp-scheme "r1" r1-range))

    (define flatten-range (irange 1 3))
    (define flatten-tests
      (tests "flatten" flatten-passes interp-scheme "flatten" flatten-range))

    (define select-instructions-range (irange 1 3))
    (define select-instructions-tests
      (tests "select-instructions" select-instructions-passes interp-C "select" select-instructions-range))
    
    (r0-tests)
    (r1-tests)
    (flatten-tests)
    (select-instructions-tests)
    (display "all tests passed!") (newline)
    ))
