#lang racket

(require "utilities.rkt")


(define (getVars assignments)
  (foldr (lambda (assgn vars)
           (match assgn
             [`(assign ,var ,val) (cons var vars)]
             [`(if (eq? ,exp1 ,exp2) ,thns ,elss)
              (let* ([thnVars (getVars thns)]
                     [elsVars (getVars elss)]
                     [allVars (append thnVars elsVars vars)]
                     [exp1-maybe (if (symbol? exp1) (cons exp1 allVars) allVars)]
                     [exp2-maybe (if (symbol? exp2) (cons exp2 exp1-maybe) exp1-maybe)])
                ;; we run remove-duplicates at the top level, so don't worry about the uniqueness
                exp2-maybe)]))
         '() assignments))


(define (change-var newVar oldVar assignments)
  (cond
    [(null? assignments) '()]; (error 'change-var (format "there should be at least one assignment here, I'm trying to change ~a, with ~a" oldVar newVar)))
    [else
     (match (car assignments)
       [`(assign ,var ,val)
        (if (eqv? var oldVar)
            (cons `(assign ,newVar ,val) (cdr assignments))
            (cons (car assignments) (change-var newVar oldVar (cdr assignments))))]
       [`(if (eq? ,e1 ,e2) ,thns ,elss)
        (cons `(if (eq? ,(if (eqv? e1 oldVar) newVar e1) ,(if (eqv? e2 oldVar) newVar e2))
                   ,(change-var newVar oldVar thns)
                   ,(change-var newVar oldVar elss))
              (change-var newVar oldVar (cdr assignments)))]
       [else (error 'change-var (format "unhandled case : ~a" (car assignments)))])]))

;; R3 -> C1
(define flatten
  (lambda (vars)
    (lambda (e)
      (match e
        [`(program (type ,t) ,e)
         (let-values ([(final-exp assignments) ((flatten vars) e)])
           (let ([vars (remove-duplicates (getVars assignments))])
             `(program ,vars (type ,t) ,@assignments (return ,final-exp))))]
        ;; values
        [(? boolean?) (values e '())]
        [(? symbol?) (values e '())]
        [(? integer?) (values e '())]
        ;; let
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
              (values flat-body (cons `(assign ,x ,flat-e) assgn-body)))))]
        ;; and
        [`(and ,exp1 ,exp2) ((flatten vars) `(if ,exp1 ,exp2 #f))]
        ;; if - optimizing
        [`(if ,cnd ,thn ,els)
           (match cnd
             [(? boolean?)
              (let-values ([(flat-cnd statements-cnd) ((flatten vars) cnd)]
                           [(flat-thn statements-thn) ((flatten vars) thn)]
                           [(flat-els statements-els) ((flatten vars) els)])
                (if cnd
                    (values flat-thn statements-thn)
                    (values flat-els statements-els)))]
             [(? symbol?)
              ((flatten vars) `(if (eq? #t ,cnd) ,thn ,els))]
             ;; if 'not' flipping the branches
             [`(not ,exp) ((flatten vars) `(if ,exp ,els ,thn))]
             ;; getting rid of let
             [`(let ([,var ,exp]) ,body)
              (let-values ([(flat-exp statements-exp) ((flatten vars) exp)]
                           [(flat-new-if statements-new-if) ((flatten vars) `(if ,body ,thn ,els))])
                (let ([new-exp-statements (if (null? statements-exp)
                                              `((assign ,var ,flat-exp))
                                              (change-var var flat-exp statements-exp))])
                  (values flat-new-if (append new-exp-statements
                                              statements-new-if))))]
             ;; cnd is 'and'
             [`(and ,exp1 ,exp2)
              ((flatten vars) `(if (if ,exp1 ,exp2 #f) ,thn ,els))]
             ;; cnd is already an eq?
             [`(eq? ,e1 ,e2)
              (let-values ([(flat-e1 statements-e1) ((flatten vars) e1)]
                           [(flat-e2 statements-e2) ((flatten vars) e2)]
                           [(flat-thn statements-thn) ((flatten vars) thn)]
                           [(flat-els statements-els) ((flatten vars) els)])
                (let ([newIfVar (gensym `if.)])
                  (values newIfVar (append statements-e1
                                           statements-e2
                                           `((if (eq? ,flat-e1 ,flat-e2)
                                                 ,(append statements-thn `((assign ,newIfVar ,flat-thn)))
                                                 ,(append statements-els `((assign ,newIfVar ,flat-els)))))))))]

             ;; another 'if' in there
             [`(if ,cnd-inner ,thn-inner ,els-inner)
              ((flatten vars) `(if ,cnd-inner
                                   (if ,thn-inner ,thn ,els)
                                   (if ,els-inner ,thn ,els)))]
                           
             [else
              (error 'optimizing-if (format "there is an unhandled conditional case : (if ~a ..." cnd))])]
        ;; +, -, (read), not, eq?
        [`(,op ,es ...)
         (let-values ([(flats assignments) (map2 (flatten vars) es)])
           (let ((newVar (gensym `tmp.)))
             (values newVar (append (apply append assignments)
                                    (list `(assign ,newVar (,op ,@flats)))))))]))))
