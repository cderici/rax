#lang racket

(require "utilities.rkt" "interp.rkt")

(module+ test
  (require rackunit))

;; R1 -> R1
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

;; R1 -> C0
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


;; C0 -> x86*
;; doesn't change the (program (vars) assignments ... return) structure
(define select-instructions
  (lambda (c0-e)
    (match c0-e
      [`(assign ,var ,rhs)
       (match rhs
         [(? symbol?) `((movq (var ,rhs) (var ,var)))]
         [(? integer?) `((movq (int ,rhs) (var ,var)))]
         [`(read) `((callq read_int) (movq (reg rax) (var ,var)))]
         [`(- ,arg) `((movq (,(if (integer? arg) 'int 'var) arg) (var ,var)) (negq (var ,var)))]
         [`(+ ,arg1 ,arg2)
          (cond
            [(equal? arg1 var) `((addq arg1 var))]
            [(equal? arg2 var) `((addq arg2 var))]
            [else
             `((movq (,(if (integer? arg1) 'int 'var) ,arg1) (var ,var))
               (addq (,(if (integer? arg2) 'int 'var) ,arg2) (var ,var)))
             ])]
         [else (error 'select-instructions "don't know how to handle this rhs~a")])
       ]
      [`(return ,e) `((movq (,(if (integer? e) 'int 'var) ,e) (reg rax)))]
      [`(program (,vars ...) ,assignments ... (return ,final-e))
       `(program ,vars ,@(foldr append '() (map select-instructions assignments)) ,@(select-instructions `(return ,final-e)))])))

(define (varToStackPos expression listHomes)
  (match expression
    [`(var ,varID) (let ((stackPos (assv varID listHomes)))
                     `(stack ,(cdr stackPos)))]
    [else expression]))

;; x86* -> x86*
(define assign-homes
  (lambda (listHomes)
    (lambda (x86-e)
      (match x86-e
        [`(,bin-instr ,arg1 ,arg2) `(,bin-instr ,(varToStackPos arg1 listHomes)
                                                ,(varToStackPos arg2 listHomes))]
        [`(,unary-instr ,arg) `(,unary-instr ,(varToStackPos arg listHomes))]
        [`(program (,vars ...)  ,instructions ...)
         (let ((frame-size (ceiling (/ (length vars) 2)))
               ;; every-one's on the stack!
               (homes (map cons vars (build-list (length vars) (lambda (x) (* (add1 x) -8))))))
           `(program ,frame-size ,@(map (assign-homes homes) instructions)))]))))

; x86* -> x86
(define patch-instr
  (lambda (x86-e)
    (match x86-e
      [`(,op (stack ,n1) (stack ,n2))
       `((movq (stack ,n1) (reg rax))
         (,op  (reg rax)   (reg ,n2)))]
      [`(program ,i ,instrs ...)
       `(program ,i ,@(foldr append `() (map patch-instr instrs)))]
      [_ `(,x86-e)])))

(define r1-passes `(("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("assign homes" ,(assign-homes '()) ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    #; ("print x86" ,print-x86 #f)))

(interp-tests "arithmetic with let" r1-passes interp-scheme "r1" (list 1 2 3))
(display "all tests passed!") (newline)
