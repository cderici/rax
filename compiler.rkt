#lang racket

(require "utilities.rkt" "interp.rkt")

(module+ test
  (require rackunit))

(define uniquify
  (lambda (alist)
    (lambda (e)
      (match e
        [(? symbol?) (let ([idNewID (assv e alist)])
                       (if (not idNewID)
                           (error 'uniquify "something's wrong")
                           (cdr idNewID)))]
        [(? integer?) e]
        [`(let ([,x ,e]) ,body) (let ([newID (gensym)])
                                  `(let ([,newID ,((uniquify alist) e)]) ,((uniquify (cons (cons x newID) alist)) body)))]
        [`(program ,e) `(program ,((uniquify alist) e))]
        [`(,op ,es ...) `(,op ,@(map (uniquify alist) es))]))))

(define (getVars assignments)
  (foldr (lambda (assgn vars)
           (cons (cadr assgn) vars)) '() assignments))

(define (change-var newVar oldVar assignments)
  (cond
    ((null? assignments) (error 'change-var "there should be at least one assignment here"))
    ((eqv? oldVar (cadr (car assignments)))
     (cons `(assign ,newVar ,(caddr (car assignments))) (cdr assignments)))
    (else (cons (car assignments) (change-var newVar oldVar (cdr assignments))))))

(define flatten
  (lambda (vars)
    (lambda (e)
      (match e
        [(? symbol?) (values e '())]
        [(? integer?) (values e '())]
        [`(let ([,x ,e]) ,body)
         (let-values ([(flat-e assgn-e) ((flatten vars) e)]
                      [(flat-body assgn-body) ((flatten (cons x vars)) body)])
           (cond
             ;; flat-e is newly created
             ((and (symbol? flat-e) (not (memv flat-e vars)))
              (values flat-body (append (change-var x flat-e assgn-e) assgn-body)))
             ;; flat-e is a previous variable
             ((and (symbol? flat-e) (memv flat-e vars))
              (if (not (null? assgn-e)) (error 'flatten "flat-e is a previous variable, but e is compound, what's going on?")
                  (values flat-body (cons `(assign ,x ,flat-e) assgn-body))))
             ;; flat-e is an integer
             (else
              (values flat-body (cons `(assign ,x ,flat-e) assgn-body)))))
         ]
        
        [`(program ,e) (let-values ([(final-exp assignments) ((flatten vars) e)])
                         (let ([vars (getVars assignments)])
                           `(program ,vars ,@assignments (return ,final-exp))))]
        [`(,op ,es ...)
         (let-values ([(flats assignments) (map2 (flatten vars) es)])
           (let ((newVar (gensym)))
             (values newVar (append (apply append assignments) (list `(assign ,newVar (,op ,@flats)))))))]))))
        



(define r1-passes `(("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)))
                    ;; ("select instructions" ,select-instructions ,interp-x86)
                    ;; ("assign homes" ,assign-homes ,interp-x86)
                    ;; ("patch instructions" ,patch-instructions ,interp-x86)
                    ;; ("print x86" ,print-x86 #f)))

(interp-tests "arithmetic with let" r1-passes interp-scheme "r1" (list 1 2))
(display "all tests passed!") (newline)
