#lang racket

(require "utilities.rkt" "interp.rkt" "testing.rkt"
         "flatten.rkt" "assign-homes.rkt" "typecheck.rkt" "uncover-types.rkt")

(provide r1-passes
         r2-passes
         uniquify
         flatten
         select-instructions
         assign-homes
         register-allocation
         patch-instr
         print-x86-64
         typechecker
         )


;; R2 -> R2
(define uniquify
  (lambda (alist)
    (lambda (e)
      (match e
        [(? integer?) e]
        [(? boolean?) e]
        [(? symbol?) (let ([idNewID (assv e alist)])
                       (if (not idNewID)
                           (error 'uniquify "something's wrong")
                           (cdr idNewID)))]
        [`(let ([,x ,e]) ,body) (let ([newID (gensym x)])
                                  `(let ([,newID ,((uniquify alist) e)]) ,((uniquify (cons (cons x newID) alist)) body)))]
        [`(program ,e) `(program (type ,(typechecker e)) ,((uniquify alist) e))]
        [`(,op ,es ...) `(,op ,@(map (uniquify alist) es))]))))

;; C2 -> C2
;; expose-allocation (after flatten)
(define expose-allocation
  (lambda (heap-size-bytes var-types)
    (lambda (e)
      (match e
        [`(assign ,lhs (vector ,e ...))
         (let* ([len (length e)]
                [bytes (+ 8 (* len 8))])
           `((if (collection-needed? ,bytes)
                 ((collect ,bytes))
                 ())
             (assign ,lhs (allocate ,len ,(cdr (assv lhs var-types))))
             ,@(map (lambda (vector-element position)
                      (let ([void-var (string->symbol (string-append "void." (number->string position)))])
                        `(assign ,void-var (vector-set! ,lhs ,position ,vector-element))))
                    e (range len))))]
        
        [`(program (,vars ...) (type ,t) ,assignments ... (return ,final-e))
         (let* ([var-types (uncover-types e)]
                [new-assignments (foldr append null (map (expose-allocation heap-size-bytes var-types) assignments))])
           `(program ,var-types (type ,t) (initialize 10000 ,heap-size-bytes) ,new-assignments (return ,final-e)))]

        [else `(,e)]))))

;; C1 -> x86_1*
;; doesn't change the (program (vars) assignments ... return) structure
(define select-instructions
  (match-lambda
    ;; assign
    [`(assign ,var ,rhs)
     (match rhs
       [(? symbol?) `((movq (var ,rhs) (var ,var)))]
       [(? integer?) `((movq (int ,rhs) (var ,var)))]
       [(? boolean?) `((movq (int ,(if rhs 1 0)) (var ,var)))]
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
       [`(not ,arg) ;; arg : var|bool (kudos to the typechecker)
        (cond
          [(boolean? arg) `((movq (int ,(if arg 1 0)) (var ,var)) (xorq (int 1) (var ,var)))]
          [(symbol? arg) `((movq (var ,arg) (var ,var)) (xorq (int 1) (var ,var)))]
          [else (error 'select-instructions "we shouldn't have as arg to 'not' any form other than boolean or var(symbol)")])]
       [`(eq? ,arg1 ,arg2)
        ;; TODO : refactor
        (let ([arg1-instr (cond [(boolean? arg1) `(int ,(if arg1 1 0))]
                                [(integer? arg1) `(int ,arg1)]
                                [(symbol? arg1) `(var ,arg1)])]
              [arg2-instr (cond [(boolean? arg2) `(int ,(if arg2 1 0))]
                                [(integer? arg2) `(int ,arg2)]
                                [(symbol? arg2) `(var ,arg2)])])
          `((cmpq ,arg1-instr ,arg2-instr)
            (sete (byte-reg al))
            (movzbq (byte-reg al) (var ,var))))]
       [else (error 'select-instructions "don't know how to handle this rhs~a")])]
    ;; if
    [`(if (eq? ,exp1 ,exp2) ,thns ,elss)
     (let ([exp1-inst (cond [(boolean? exp1) `(int ,(if exp1 1 0))]
                            [(integer? exp1) `(int ,exp1)]
                            [(symbol? exp1) `(var ,exp1)])]
           [exp2-inst (cond [(boolean? exp2) `(int ,(if exp2 1 0))]
                            [(integer? exp2) `(int ,exp2)]
                            [(symbol? exp2) `(var ,exp2)])])
       `((if (eq? ,exp1-inst ,exp2-inst)
             ,(foldr append null (map select-instructions thns))
             ,(foldr append null (map select-instructions elss)))))]
    ;; return
    [`(return ,e)
     (let ([e-int (if (integer? e)
                      `(int ,e)
                      (if (boolean? e)
                          (if e `(int 1) `(int 0))
                          `(var ,e)))])
       `((movq ,e-int (reg rax))))]
    ;; program
    [`(program (,vars ...) (type ,t) ,assignments ... (return ,final-e))
     `(program ,vars (type ,t) ,@(foldr append '() (map select-instructions assignments)) ,@(select-instructions `(return ,final-e)))]))

; x86_1* (with if-statments) -> x86_1* (without if-statements)
(define lower-conditionals
  (match-lambda
    [`(if (eq? ,e1 ,e2) ,thns ,elss)
     (let ([thenlabel (genlabel `then)]
           [endlabel  (genlabel `end)])
       `((cmpq ,e1 ,e2)
         (je ,thenlabel)
         ,@(append-map lower-conditionals elss)
         (jmp ,endlabel)
         (label ,thenlabel)
         ,@(append-map lower-conditionals thns)
         (label ,endlabel)))]
    [`(program ,i (type ,t) ,instrs ...)
     `(program ,i (type ,t) ,@(append-map lower-conditionals instrs))]
    [x `(,x)]))

; x86* -> x86
(define patch-instr
  (match-lambda
    [`(cmpq ,arg1 (int ,i)) ; Second argument to cmpq can't be immediate value
     `((movq (int ,i) (reg rax))
       (cmpq ,arg1 (reg rax)))]
    [`(movq (reg ,r) (reg ,r)) ; Kill redundant moves
     `()]
    [`(,op (stack ,n1) (stack ,n2)) ; Both arguments can't be memory locations
     `((movq (stack ,n1) (reg rax))
       (,op  (reg rax)   (stack ,n2)))]
    [`(program ,i (type ,t) ,instrs ...)
     `(program ,i (type ,t) ,@(append-map patch-instr instrs))]
    [x86-e `(,x86-e)]))

; x86* -> actual, honest-to-goodness x86-64
(define print-x86-64
  (lambda (x86-e)
    (match x86-e
      [`(program ,i (type ,t) ,instrs ...)
       (let ([wcsr (written-callee-save-regs instrs)])
         (foldr string-append ""
                `(,(format "\t.globl ~a\n" (label `main))
                  ,(symbol->string (label `main))
                  ":\n"
                  ;; Prelude
                  ,(display-instr "pushq" "%rbp")
                  ,(display-instr "movq" "%rsp, %rbp")
                  ,(save-callee-regs instrs i wcsr)
                  "\n"
                  ,(foldr string-append "" (map print-x86-64-instr instrs))
                  "\n"
                  ;; Conclusion
                  ,(display-instr "movq" "%rax, %rdi")
                  ,(display-instr "callq" (print-returned-value t))
                  ,(restore-callee-regs instrs i wcsr)
                  ,(display-instr "movq" "$0, %rax") ; Make sure the exit code is 0!
                  ,(display-instr "popq" "%rbp")
                  ,(display-instr "retq" ""))))])))

(define print-returned-value
  (lambda (ty)
    (symbol->string
     (match ty
       [`Integer (label `print_int)]
       [`Boolean (label `print_bool)]
       [_        (error (format "Don't know how to print value of type ~a" ty))]))))

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
    [`(label ,sym) (string-append (symbol->string sym) ":\n")]
    [`(callq ,l) (display-instr "callq" "~a"
                                (label l))]
    [`(,op ,a) (display-instr "~a" "~a"
                              (symbol->string op)
                              (print-x86-64-arg a))]
    [`(,unary) (symbol->string unary)]))

(define print-x86-64-arg
  (lambda (e)
    (match e
      [(? symbol?) (symbol->string e)]
      [`(int ,i)   (format "$~a" i)]
      [`(reg ,r)   (format "%~a" r)]
      [`(stack ,s) (format "~a(%rbp)" s)])))

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
      [`macosx (string->symbol (string-append "_" (symbol->string l)))]
      [_ l])))

(define genlabel
  (compose1 gensym label))

; [Pass]
(define r1-passes `(("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ; ("assign homes" ,(assign-homes `()) ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

; [Pass]
(define r2-passes `(("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))
