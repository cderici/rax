#lang racket

(require "utilities.rkt" "has-types.rkt")

(provide (rename-out [flatten-wrapper flatten])
         getVars)

(define (getVars assignments)
  (remove-duplicates
   (foldr (lambda (assgn vars)
            (match assgn
              [`(assign ,var ,val) (append (cons var (getVars (list val))) vars)]
              [`(has-type (if (has-type (eq? ,exp1 ,exp2) Boolean) ,thns ,elss) ,t)
               (let* ([thnVars (getVars thns)]
                      [elsVars (getVars elss)]
                      [allVars (append thnVars elsVars vars)]
                      [exp1-maybe (if (symbol? exp1) (cons exp1 allVars) allVars)]
                      [exp2-maybe (if (symbol? exp2) (cons exp2 exp1-maybe) exp1-maybe)])
                 ;; we run remove-duplicates at the top level, so don't worry about the uniqueness
                 exp2-maybe)]
              [`(define (,f ,arg-types ...) : ,t ,vars* ,body ...) (append vars* vars)]
              
              [`(has-type ,e ,t)
               (if (symbol? e) (cons e vars) (append (getVars (list e)) vars))]

              [`(,op ,arg ...) (append (getVars arg) vars)]
              
              [else vars]))
          '() assignments)))


(define (change-var newVar oldVar-e assignments)
  (cond
    [(null? assignments) '()]; (error 'change-var (format "there should be at least one assignment here, I'm trying to change ~a, with ~a" oldVar newVar)))
    [else
     (match oldVar-e
       [`(has-type ,oldVar ,_)
        (match (car assignments)
          [`(assign ,var ,val)
           (if (eqv? var oldVar)
               (cons `(assign ,newVar ,val) (cdr assignments))
               (cons (car assignments) (change-var newVar oldVar-e (cdr assignments))))]
          [`(has-type (if (has-type (eq? ,e1 ,e2) Boolean) ,thns ,elss) ,t)
           (cons `(has-type (if (has-type (eq? ,(if (equal? e1 oldVar-e) newVar e1)
                                               ,(if (equal? e2 oldVar-e) newVar e2)) Boolean)
                                ,(change-var newVar oldVar-e thns)
                                ,(change-var newVar oldVar-e elss)) ,t)
                 (change-var newVar oldVar-e (cdr assignments)))]
          [else (error 'change-var (format "unhandled case : ~a" (car assignments)))])])]))

(define flatten-wrapper
  (lambda (top-level-program)
    (match top-level-program
      [`(program (type ,t) ,defines ... ,body)
       (let-values ([(final-exp assignments) ((flatten '()) body)])
         (let ([vars (getVars assignments)]
               [flat-defines (map (flatten '()) defines)]) ;; note that a single value is returned for each define
           `(program ,vars (type ,t) (defines ,@flat-defines) ,@assignments (return ,final-exp))))]
      [else (error 'flatten "invalid R_n input ast structure")])))

;; R5 -> C3
(define flatten
  (lambda (vars)
    (lambda (e)
      (match e
        [`(void)      (values e '())]
        [(? boolean?) (values e '())]
        [(? symbol?)  (values e '())]
        [(? integer?) (values e '())]
        [`(define (,f-name ,args ...) ;; args -> (arg-name : arg-type) ...
            : ,return-type ,body)
         (let-values ([(func-final-exp func-assignments) ((flatten '()) body)])
           (let ([vars (getVars func-assignments)])
             `(define (,f-name ,@args) :  ,return-type ,vars ,@func-assignments (return ,func-final-exp))))]
        
        ;; ;; function-ref
        ;; [`(function-ref ,f)
        ;;  (let ((newVar (gensym `tmp.)))
        ;;    (values newVar (list `(assign ,newVar (function-ref ,f)))))]
        ;; let
        [`(has-type (let ([,x ,e]) ,body) ,t)
         (match-let*-values
          ([(flat-e assgn-e) ((flatten vars) e)]
           [(flat-body assgn-body) ((flatten (cons x vars)) body)]
           [(`(has-type ,flat-e-e ,_)) flat-e])
          (cond
            ;; flat-e is newly created
            ((and (symbol? flat-e-e) (not (memv flat-e-e vars)))
             (values flat-body (append assgn-e `((assign ,x ,flat-e)) assgn-body)))
            ;; flat-e is a previous variable
            ((and (symbol? flat-e-e) (memv flat-e-e vars))
             (if (not (null? assgn-e)) (error 'flatten "flat-e is a previous variable, but e is compound, what's going on?")
                 (values flat-body (cons `(assign ,x ,flat-e) assgn-body))))
            ;; flat-e is an integer
            (else
             (values flat-body (cons `(assign ,x ,flat-e) assgn-body)))))]
        ;; and
        [`(has-type (and ,exp1 ,exp2) ,t) ((flatten vars) `(has-type (if ,exp1 ,exp2 (has-type #f Boolean)) ,t))]
        ;; if - optimizing
        [`(has-type (if ,cnd ,thn ,els) ,t)
         (match cnd           
           ;; if 'not' flipping the branches
           [`(has-type (not ,exp) Boolean) ((flatten vars) `(has-type (if ,exp ,els ,thn) ,t))]
           ;; getting rid of let
           [`(has-type (let ([,var ,exp]) ,body) Boolean)
            (let-values ([(flat-exp statements-exp) ((flatten vars) exp)]
                         [(flat-new-if statements-new-if) ((flatten vars) `(has-type (if ,body ,thn ,els) ,t))])
              (values flat-new-if (append statements-exp
                                          `((assign ,var ,flat-exp))
                                          statements-new-if)))]

              ;; (let ([new-exp-statements (if (null? statements-exp)
              ;;                               `((assign ,var ,flat-exp))
              ;;                               (change-var var flat-exp statements-exp))])
              ;;   (values flat-new-if (append new-exp-statements
           ;;                               statements-new-if))))]
           
           ;; cnd is 'and'
           [`(has-type (and ,exp1 ,exp2) Boolean)
            ((flatten vars) `(has-type (if (has-type (if ,exp1 ,exp2 (has-type #f Boolean)) Boolean) ,thn ,els) ,t))]
           ;; cnd is already an eq?
           [`(has-type (eq? ,e1 ,e2) Boolean)
            (let-values ([(flat-e1 statements-e1) ((flatten vars) e1)]
                         [(flat-e2 statements-e2) ((flatten vars) e2)]
                         [(flat-thn statements-thn) ((flatten vars) thn)]
                         [(flat-els statements-els) ((flatten vars) els)])
              (let ([newIfVar (gensym `if.)])
                (values `(has-type ,newIfVar ,t)
                        (append statements-e1
                                statements-e2
                                `((has-type (if (has-type (eq? ,flat-e1 ,flat-e2) Boolean)
                                                ,(append statements-thn `((assign ,newIfVar ,flat-thn)))
                                                ,(append statements-els `((assign ,newIfVar ,flat-els)))) ,t))))))]
           
           ;; another 'if' in there
           [`(has-type (if ,cnd-inner ,thn-inner ,els-inner) Boolean)
            ((flatten vars) `(has-type (if ,cnd-inner
                                           (has-type (if ,thn-inner ,thn ,els) ,t)
                                           (has-type (if ,els-inner ,thn ,els) ,t)) ,t))]
           ;; cnd is an app
           [(or `(has-type (app ,_ ...) Boolean) `(has-type (vector-ref ,_ ,_) Boolean))
            ;; just producing the same if, keeping the else to be alerted when we have a new type of cnd
            (let-values ([(flat-cnd statements-cnd) ((flatten vars) cnd)]
                         [(flat-thn statements-thn) ((flatten vars) thn)]
                         [(flat-els statements-els) ((flatten vars) els)])
              (let ([newIfVar (gensym `if.)])
                (values `(has-type ,newIfVar ,t)
                        (append statements-cnd
                                `((has-type (if (has-type (eq? ,flat-cnd (has-type #t Boolean)) Boolean)
                                                ,(append statements-thn `((assign ,newIfVar ,flat-thn)))
                                                ,(append statements-els `((assign ,newIfVar ,flat-els)))) ,t))))))]
           [`(has-type ,n Boolean)
            (cond
              ((boolean? n)
               (match-let*-values
                ([(flat-cnd statements-cnd) ((flatten vars) cnd)]
                 [(flat-thn statements-thn) ((flatten vars) thn)]
                 [(flat-els statements-els) ((flatten vars) els)]
                 [(`(has-type ,cnd-e Boolean)) cnd])
                (if cnd-e
                    (values flat-thn statements-thn)
                    (values flat-els statements-els))))
              ((symbol? n)
               ((flatten vars) `(has-type (if (has-type (eq? (has-type #t Boolean) ,cnd) Boolean) ,thn ,els) ,t)))
              (else (error 'optimizing-if (format "check this : ~a" e))))]
           
           [else
            (error 'optimizing-if (format "there is an unhandled conditional case : (if ~a ..." cnd))])]
        
        ;; +, -, (read), not, eq?
        [`(has-type (,op ,es ...) ,t-cnd)
         (let-values ([(flats assignments) (map2 (flatten vars) es)])
           (let ((newVar (gensym `tmp.)))
             (values `(has-type ,newVar ,t-cnd)
                     (append (apply append assignments)
                             (list `(assign ,newVar (has-type (,op ,@flats) ,t-cnd)))))))]
        ;; values
        [`(has-type ,n ,t)
         (cond
           [(or (equal? n `(void))
                (boolean? n)
                (symbol? n)
                (integer? n))
            (values e '())]
           [else (error 'flatten-values (format "check : ~a\n" e))])]
        
        ;; +, -, (read), not, eq?
        [`(,op ,es ...)
         (begin (displayln "heyy" (current-output-port))
                (let-values ([(flats assignments) (map2 (flatten vars) es)])
                  (let ((newVar (gensym `tmp.)))
                    (values newVar (append (apply append assignments)
                                           (list `(assign ,newVar (,op ,@flats))))))))]))))
