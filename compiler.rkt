#lang racket

(require "utilities.rkt" "interp.rkt" "testing.rkt"
         "flatten.rkt" "assign-homes.rkt" "typecheck.rkt"
         "uncover-types.rkt" "select-inst.rkt")

(provide r1-passes
         r2-passes
         r3-passes
         r4-passes
         uniquify
         flatten
         select-instructions
         assign-homes
         register-allocation
         patch-instr
         print-x86-64
         typechecker
         )

(define prim-names (set `void `read `and `+ `- `not `if `eq?
                        `vector `vector-ref `vector-set!))

;; R4 -> R4
(define uniquify
  (lambda (alist)
    (lambda (e)
      (match e
        [`(void)      e]
        [(? integer?) e]
        [(? boolean?) e]
        [(? symbol?) (let ([idNewID (assv e alist)])
                       (if (not idNewID)
                           (error 'uniquify "something's wrong")
                           (cdr idNewID)))]
        [`(let ([,x ,e]) ,body) (let ([newID (gensym x)])
                                  `(let ([,newID ,((uniquify alist) e)]) ,((uniquify (cons (cons x newID) alist)) body)))]
        [`(define ,(list fun `[,args : ,tys] ...) : ,ty-ret ,body)
         (let* ([new-args    (map gensym args)]
                [assocs      (map cons args new-args)]
                [new-arg-tys (map (λ (a t) `[,a : ,t]) new-args tys)])
           `(define (,fun ,@new-arg-tys) : ,ty-ret
              ,((uniquify (append assocs alist)) body)))]
        [`(program (type ,t) ,defines ... ,e)
         (let* ([def-names (map def-name defines)]
                [alist^    (append (map cons def-names def-names) alist)])
           `(program (type ,t)
                     ,@(map (uniquify alist^) defines)
                     ,((uniquify alist^) e)))]
        [`(,op ,es ...)
         #:when (set-member? prim-names op)
         `(,op ,@(map (uniquify alist) es))]
        [(list rator rands ...)
         `(,((uniquify alist) rator)
           ,(map (uniquify alist) rands))]))))

(define def-name
  (match-lambda
    [`(define (,fun ,_ ...) : ,_ ,_) fun]))

(define void-count -1)

;; R4 -> R4
(define reveal-functions
  (lambda (locals)
    (match-lambda
      [(and f (? symbol?)) (if (set-member? locals f)
                               f
                               `(function-ref ,f))]
      [`(let ([,x ,e]) ,body)
       `(let ([,x ,((reveal-functions locals) e)])
          ,((reveal-functions (set-add x locals)) body))]
      [`(if ,cnd ,thn ,els)
       `(if ,((reveal-functions locals) cnd)
            ,((reveal-functions locals) thn)
            ,((reveal-functions locals) els))]
      [`(define ,(and args (list fun `[,arg1 : ,ty1] ...)) : ,ty-ret ,body)
       `(define ,args : ,ty-ret
          ,((reveal-functions (set-union (list->set arg1) locals)) body))]
      [`(program (type ,t) ,defines ... ,body)
       `(program (type ,t)
                 ,@(map (reveal-functions locals) defines)
                 ,((reveal-functions locals) body))]
      [`(program ,defines ... ,body) ; for debugging purposes
       `(program ,@(map (reveal-functions locals) defines)
                 ,((reveal-functions locals) body))]
      [(list op args ...)
       #:when (set-member? prim-names op)
       `(,op ,@(map (reveal-functions locals) args))]
      [(list rator rands ...)
       `(app ,((reveal-functions locals) rator)
             ,@(map (reveal-functions locals) rands))]
      [e e])))

;; C3 -> C3
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
            [`(assign ,var (allocate ,n (Vector ,some-type ...)))
             (uncover-live-roots (cdr assignments) (cons var current-lives) (cons (car assignments) out))]
            [`(if (collection-needed? ,n) ((collect ,n)) ())
             (uncover-live-roots (cdr assignments) current-lives
                                 (cons `(if (collection-needed? ,n)
                                            ((call-live-roots ,current-lives (collect ,n)))
                                            ()) out))]
            [else (uncover-live-roots (cdr assignments) current-lives (cons (car assignments) out))]))))

;; C3 -> C3
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
    [`(movzbq ,arg1 ,(and arg2 (or `(stack ,_) `(global-value ,_) `(offset ,_ ,_))))
     `((movzbq ,arg1 (reg rax))
       (movq (reg rax) ,arg2))]
    [`(,op ,(and arg1 (or `(stack ,_) `(global-value ,_) `(offset ,_ ,_)))
           ,(and arg2 (or `(stack ,_) `(global-value ,_) `(offset ,_ ,_))))
     ; Both arguments can't be memory locations
     `((movq ,arg1 (reg rax))
       (,op  (reg rax) ,arg2))]
    [`(program ,i (type ,t) ,instrs ...)
     `(program ,i (type ,t) ,@(append-map patch-instr instrs))]
    [x86-e `(,x86-e)]))

; x86* -> actual, honest-to-goodness x86-64
(define print-x86-64
  (match-lambda
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
                ,(print-by-type t)
                ,(restore-callee-regs instrs i wcsr)
                ,(display-instr "movq" "$0, %rax") ; Make sure the exit code is 0!
                ,(display-instr "popq" "%rbp")
                ,(display-instr "retq" ""))))]))

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

; [Pass]
(define r3-passes `(; Implicit typecheck pass occurs at beginning
                    ("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)
                    ("expose-allocation" ,(expose-allocation 1280 `()) ,interp-C)
                    ("uncover-call-live-roots" ,uncover-call-live ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

; [Pass]
(define r4-passes `(; Implicit typecheck pass occurs at beginning
                    ("uniquify" ,(uniquify '()) ,interp-scheme)
                    ;("reveal-functions" ,(reveal-functions (set)) ,interp-scheme)
                    ("flatten" ,(flatten '()) ,interp-C)
                    ("expose-allocation" ,(expose-allocation 1280 `()) ,interp-C)
                    ("uncover-call-live-roots" ,uncover-call-live ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))
