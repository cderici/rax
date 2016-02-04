#lang racket

(require "utilities.rkt" "interp.rkt" "testing.rkt"
         "assign-homes.rkt" "typecheck.rkt")

(provide r1-passes
         uniquify
         flatten
         select-instructions
         assign-homes
         register-allocation
         patch-instr
         print-x86-64
         typechecker
         )


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
        [`(let ([,x ,e]) ,body) (let ([newID (gensym x)])
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
           (let ((newVar (gensym `tmp)))
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
         [`(- ,arg) `((movq (,(if (integer? arg) 'int 'var) ,arg) (var ,var)) (negq (var ,var)))]
         [`(+ ,arg1 ,arg2)
          (cond
            [(equal? arg1 var) `((addq ,arg1 ,var))]
            [(equal? arg2 var) `((addq ,arg2 ,var))]
            [else
             `((movq (,(if (integer? arg1) 'int 'var) ,arg1) (var ,var))
               (addq (,(if (integer? arg2) 'int 'var) ,arg2) (var ,var)))
             ])]
         [else (error 'select-instructions "don't know how to handle this rhs~a")])
       ]
      [`(return ,e) `((movq (,(if (integer? e) 'int 'var) ,e) (reg rax)))]
      [`(program (,vars ...) ,assignments ... (return ,final-e))
       `(program ,vars ,@(foldr append '() (map select-instructions assignments)) ,@(select-instructions `(return ,final-e)))])))

; x86* -> x86
(define patch-instr
  (lambda (x86-e)
    (match x86-e
      [`(movq (reg ,r) (reg ,r)) `()]
      [`(,op (stack ,n1) (stack ,n2))
       `((movq (stack ,n1) (reg rax))
         (,op  (reg rax)   (stack ,n2)))]
      [`(program ,i ,instrs ...)
       `(program ,i ,@(foldr append `() (map patch-instr instrs)))]
      [_ `(,x86-e)])))

; x86* -> actual, honest-to-goodness x86-64
(define print-x86-64
  (lambda (x86-e)
    (match x86-e
      [`(program ,i ,instrs ...)
       (let ([wcsr (written-callee-save-regs instrs)])
         (foldr string-append ""
                `(,(format "\t.globl ~a\n" (label "main"))
                  ,(label "main:\n")
                  ;; Prelude
                  ,(display-instr "pushq" "%rbp")
                  ,(display-instr "movq" "%rsp, %rbp")
                  ,(save-callee-regs instrs i wcsr)
                  "\n"
                  ,(foldr string-append "" (map print-x86-64-instr instrs))
                  "\n"
                  ;; Conclusion
                  ,(display-instr "movq" "%rax, %rdi")
                  ,(display-instr "callq" (label "print_int"))
                  ,(restore-callee-regs instrs i wcsr)
                  ,(display-instr "movq" "$0, %rax") ; Make sure the exit code is 0!
                  ,(display-instr "popq" "%rbp")
                  ,(display-instr "retq" ""))))])))

(define save-callee-regs
  (λ (instrs i wcsr)
    (string-append
     (if (null? i) "" (display-instr "subq" "$~a, %rsp" i))
     (car (foldr (λ (wcs state)
                   (match state
                     [`(,str . ,offset)
                      (cons
                       (string-append
                        (display-instr "movq" "%~a, -~a(%rbp)" wcs offset) str)
                       (- offset 8))]))
                 `("" . ,i) wcsr)))))

(define restore-callee-regs
  (λ (instrs i wcsr)
    (string-append
     (car (foldr (λ (wcs state)
                   (match state
                     [`(,str . ,offset)
                      (cons
                       (string-append
                        (display-instr "movq" "-~a(%rbp), %~a" offset wcs) str)
                       (- offset 8))]))
                 `("" . ,i) wcsr))
     (if (null? i) "" (display-instr "addq" "$~a, %rsp" i)))))

(define print-x86-64-instr
  (match-lambda
    [`(,op ,a1 ,a2) (display-instr "~a" "~a, ~a"
                                   (symbol->string op)
                                   (print-x86-64-arg a1)
                                   (print-x86-64-arg a2))]
    [`(callq ,l) (display-instr "callq" "~a"
                                (label l))]
    [`(,op ,a) (display-instr "~a" "~a"
                              (symbol->string op)
                              (print-x86-64-arg a))]
    [`(,unary) (symbol->string unary)]))

(define print-x86-64-arg
  (match-lambda
    [`(int ,i)   (format "$~a" i)]
    [`(reg ,r)   (format "%~a" r)]
    [`(stack ,s) (format "~a(%rbp)" s)]))

(define display-instr
  (match-lambda*
    [(list-rest instr-name instr-body args)
     (apply format (foldr string-append ""
                          `("\t"
                            ,instr-name
                            "\t"
                            ,instr-body
                            "\n"))
            args)]))

(define label
  (lambda (l)
    (match (system-type 'os)
      [`macosx (string-append "_" l)]
      [_ l])))

; [Pass]
(define r1-passes `(("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ; ("assign homes" ,(assign-homes `()) ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

