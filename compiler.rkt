#lang racket

(require "utilities.rkt" "interp.rkt" "testing.rkt"
         "flatten.rkt" "assign-homes.rkt" "typecheck.rkt"
         "uncover-types.rkt" "select-inst.rkt")

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
        [`(program (type ,t) ,e) `(program (type ,t) ,((uniquify alist) e))]
        [`(,op ,es ...) `(,op ,@(map (uniquify alist) es))]))))

(define void-count -1)

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
                      (let ([void-var (string->symbol (string-append "void." (begin (set! void-count (add1 void-count))
                                                                                    (number->string void-count))))])
                        `(assign ,void-var (vector-set! ,lhs ,position ,vector-element))))
                    e (range len))))]
        
        [`(program (,vars ...) (type ,t) ,assignments ... (return ,final-e))
         (let* ([var-types (uncover-types e)]
                [new-assignments (foldr append null (map (expose-allocation heap-size-bytes var-types) assignments))]
                [new-vars (getVars new-assignments)]
                [new-var-types (uncover-types `(program ,new-vars (type ,t) ,@new-assignments (return ,final-e)))])
           `(program ,new-var-types (type ,t) (initialize 10000 ,heap-size-bytes) ,@new-assignments (return ,final-e)))]

        [else `(,e)]))))


(define (uncover-live-roots assignments current-lives out)
  (cond
    ((empty? assignments) (reverse out))
    (else (match (car assignments)
            [`(assign ,var (allocate ,n (Vector ,some-type)))
             (uncover-live-roots (cdr assignments) (cons var current-lives) (cons (car assignments) out))]
            [`(if (collection-needed? ,n) ((collect ,n)) ())
             (uncover-live-roots (cdr assignments) current-lives
                                 (cons `(if (collection-needed? ,n)
                                            ((call-live-roots ,current-lives (collect ,n)))
                                            ()) out))]
            [else (uncover-live-roots (cdr assignments) current-lives (cons (car assignments) out))]))))

(define uncover-call-live
  (lambda (e)
    (match e
      [`(program ,var-types (type ,t) (initialize ,s ,h) ,assignments ... (return ,final-e))
       (let ([vars-without-types (map car var-types)]
             [new-assignments (uncover-live-roots assignments '() '())])
       `(program ,vars-without-types (type ,t) (initialize ,s ,h) ,@new-assignments (return ,final-e)))])))
       


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
       [`Integer     (label `print_int)]
       [`Boolean     (label `print_bool)]
       [`(Vector ,_) (label `print_vector)] ; TODO: This probably isn't right
       [`Void        (label `print_void)]
       [_            (error (format "Don't know how to print value of type ~a" ty))]))))

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
      [(or `(reg ,r) `(byte-reg ,r))  (format "%~a" r)]
      [`(offset (reg ,r) ,n) (format "~a(%~a)" n r)]
      [`(offset (stack ,s) ,n) (format "~a(%rbp)" (+ n s))] ;; keeping this separate cause I'm not sure if I'm doing the right thing
                 
      ;; keeping them seperate to easily see if we need any other global-value
      [`(global-value rootstack_begin) (format "~a(%rip)" (label 'rootstack_begin))]
      [`(global-value free_ptr) (format "~a(%rip)" (label 'free_ptr))]
      [`(global-value fromspace_end) (format "~a(%rip)" (label 'fromspace_end))]
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
(define r2-passes `(; Implicit typecheck pass occurs at beginning
                    ("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))
