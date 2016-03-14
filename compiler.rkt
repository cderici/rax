#lang racket

(require "utilities.rkt" "interp.rkt" "testing.rkt"
         "flatten.rkt" "assign-homes.rkt" "typecheck.rkt"
         "uncover-types.rkt" "select-inst.rkt")

(provide r1-passes
         r2-passes
         r3-passes
         r4-passes
         r5-passes
         convert-to-closures
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

;; R5 -> R5
(define uniquify
  (λ (alist)
    (λ (e)
      (match e
        [`(has-type (let ([,x ,e]) ,body) ,t)         
         (let ([newID (gensym x)])
           `(has-type (let ([,newID ,((uniquify alist) e)]) ,((uniquify (cons (cons x newID) alist)) body)) ,t))]
        [`(has-type (lambda: ([,args : ,tys] ...) : ,ty-ret ,body) ,t)
         (let* ([new-args (map (curry gensym) args)]
                [assocs (map cons args new-args)]
                [new-arg-tys (map (λ (a t) `[,a : ,t]) new-args tys)])
         `(has-type (lambda: (,@new-arg-tys) : ,ty-ret ,((uniquify (append assocs alist)) body)) ,t))]
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
        [`(has-type (,op ,es ...) ,t)
         #:when (set-member? prim-names op)
         `(has-type (,op ,@(map (uniquify alist) es)) ,t)] 
        [`(has-type (,rator ,rands ...) ,t)
         `(has-type (,((uniquify alist) rator)
                     ,@(map (uniquify alist) rands)) ,t)]
        [`(has-type ,n ,t)
         (cond
           [(symbol? n)
            (let ([idNewID (assv n alist)])
              (if (not idNewID)
                  (error 'uniquify "something's wrong")
                  `(has-type ,(cdr idNewID) ,t)))]
           [else e])]))))

(define def-name
  (match-lambda
    [`(define (,fun ,_ ...) : ,_ ,_) fun]))

(define void-count -1)

;; R5 -> R5
(define reveal-functions
  (λ (locals)
    (match-lambda
      [(and f (? symbol?)) (if (set-member? locals f)
                               f
                               `(function-ref ,f))]
      [`(let ([,x ,e]) ,body)
       `(let ([,x ,((reveal-functions locals) e)])
          ,((reveal-functions (set-add locals x)) body))]
      [`(if ,cnd ,thn ,els)
       `(if ,((reveal-functions locals) cnd)
            ,((reveal-functions locals) thn)
            ,((reveal-functions locals) els))]
      [`(lambda: ([,args : ,tys] ...) : ,ty-ret ,body)
       (let ([arg-tys (map (λ (a t) `[,a : ,t]) args tys)])
         `(lambda: (,@arg-tys) : ,ty-ret ,((reveal-functions (foldr (λ (a l) (set-add l a)) locals args)) body)))]
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

(define (flatten-uncover-types types-nested out)
  (cond
    ((null? types-nested) (reverse out))
    (else (let ([f (car types-nested)])
            (cond
              [(symbol? f) (flatten-uncover-types '() (cons types-nested out))]
              [(or (list? f) (pair? f)) (flatten-uncover-types (cdr types-nested) (flatten-uncover-types (car types-nested) out))]
              [else (error 'flatten-uncover-types (format "check this out : ~a \n\nin\n\n ~a" f types-nested))])))))


(define shallow-flatten
  (curry append-map identity))

; R5 -> R5
(define convert-to-closures
  (match-lambda
    [`(program (type ,t) ,defines ... ,body)
     (match-let ([(list (cons converted-defs lam-defs1) ...) (map closure-worker defines)]
                 [(cons body^ lam-defs2) (closure-worker body)])
       `(program (type ,t)
                 ,@(append converted-defs
                           (shallow-flatten lam-defs1)
                           lam-defs2)
                 ,body^))]))

; R5 -> (pairof R5 defines)
(define closure-worker
  (match-lambda
    [`(define ,(list fun args ...) : ,ty-ret ,body)
     (match-let* ([clos              (gensym 'clos_dummy_param)]
                  [new-args          (cons `[,clos : _] args)]
                  [(cons body^ defs) (closure-worker body)]
                  )
       (cons `(define (,fun ,@new-args) : ,ty-ret ,body^)
             defs))]
    [(list `app rator rands ...)
     (match-let ([(cons rator^ defs1)            (closure-worker rator)]
                 [(list (cons rands^ defs2) ...) (map closure-worker rands)]
                 [tmp                            (gensym 'closure_app_temp)])
       (cons `(let ([,tmp ,rator^])
                (app (vector-ref ,tmp 0) ,tmp ,@rands^))
             (append defs1 (shallow-flatten defs2))))]
    [`(function-ref ,f) (cons `(vector (function-ref ,f)) `())]
    [`(let ([,x ,e]) ,body)
     (match-let ([(cons e^    defs1) (closure-worker e)]
                 [(cons body^ defs2) (closure-worker body)])
       (cons `(let ([,x ,e^]) ,body^)
             (append defs1 defs2)))]
    [`(if ,cnd ,thn ,els)
     (match-let ([(cons cnd^ defs1) (closure-worker cnd)]
                 [(cons thn^ defs2) (closure-worker thn)]
                 [(cons els^ defs3) (closure-worker els)])
       (cons `(if ,cnd^ ,thn^ ,els^)
             (append defs1 defs2 defs3)))]
    [(and lam `(lambda: ,(list args ...) : ,ty-ret ,body))
     (match-let* ([name (gensym "lam")]
                  [clos (gensym "clos_param_lam")]
                  [freevars (fvs lam)]
                  [(cons body^ defs) (closure-worker body)]
                  [(cons body^^ _)
                   (foldr (match-lambda**
                           [(freevar (cons b n))
                            (cons `(let ([,freevar (vector-ref ,clos ,n)]) ,b)
                                  (- n 1))])
                          (cons body^ (length freevars))
                          freevars)])
       (cons `(vector (function-ref ,name) ,@freevars)
             (cons `(define (,name [,clos : _] ,@args) : ,ty-ret
                      ,body^^) defs)))]
    [(list op args ...)
     #:when (set-member? prim-names op)
     (match-let ([(list (cons args^ defs) ...) (map closure-worker args)])
       (cons `(,op ,@args^)
             (shallow-flatten defs)))]
    [exp (cons exp `())]))

; Exp -> [Var]
; (Invariant: output is sorted in ascending order, no duplicates)
(define fvs
  (letrec
      ; Exp -> Set Var
      ([freevars
        (λ (exp)
          (match exp
            [(? symbol?) (set exp)]
            [`(lambda: ([,xs : ,ty-args] ...) : ,ty-ret ,body)
             (set-subtract (freevars body) (list->set xs))]
            [`(let ([,x ,e]) ,body)
             (set-subtract (set-union (freevars e) (freevars body)) (set x))]
            [`(if ,cnd ,thn ,els)
             (set-union (freevars cnd)
                        (freevars thn)
                        (freevars els))]
            [`(function-ref ,f) (freevars f)]
            [(list `app rator rands ...)
             (foldr set-union (set) (map freevars (cons rator rands)))]
            [(list op args ...)
             #:when (set-member? prim-names op)
             (foldr set-union (set) (map freevars args))]
            [_ (set)]))])
    (λ (e)
      (sort (set->list (freevars e)) symbol<?))))

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
             (assign ,lhs (allocate ,len ,(cdr (let ([j (assv lhs var-types)])
                                                 (if (not j) (error 'expose-allocation (format "not found var-type of : ~a" lhs)) j)))))
             ,@(map (lambda (vector-element position)
                      (let ([void-var (string->symbol (string-append "void." (begin (set! void-count (add1 void-count))
                                                                                    (number->string void-count))))])
                        `(assign ,void-var (vector-set! ,lhs ,position ,vector-element))))
                    e (range len))))]

        [`(define (,f ,arg-types ...) : ,t ,vars* ,body ...)
         (let* ([new-body (foldr append null (map (expose-allocation heap-size-bytes var-types) body))]
                [new-vars (getVars new-body)])
           `(define (,f ,@arg-types) : ,t ,(remove-duplicates (append new-vars vars*)) ,@new-body))]

        [`(program (,vars ...) (type ,t) (defines ,defs ...) ,main-assignments ... (return ,final-e))
         (let* ([var-types (flatten-uncover-types (uncover-types e) '())]
                [new-defines (map (expose-allocation heap-size-bytes var-types) defs)]
                [new-main-assignments (foldr append null (map (expose-allocation heap-size-bytes var-types) main-assignments))]
                [new-vars (remove-duplicates (append (getVars new-main-assignments) (foldr append null (map getVars new-defines))))]
                [new-var-types (flatten-uncover-types (uncover-types `(program ,new-vars (type ,t) (defines ,@new-defines) ,@new-main-assignments (return ,final-e))) '())])
           `(program ,new-var-types (type ,t) (defines ,@new-defines) (initialize 10000 ,heap-size-bytes) ,@new-main-assignments (return ,final-e)))]

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
      [`(define (,f ,arg-types ...) : ,t ,vars* ,body ...)
       (let ([new-body (uncover-live-roots body '() '())])
         `(define (,f ,@arg-types) : ,t ,vars* ,@new-body))]

      [`(program ,var-types (type ,t) (defines ,defs ...) (initialize ,s ,h) ,assignments ... (return ,final-e))
       (let ([vars-without-types (map car var-types)]
             [new-defines (map uncover-call-live defs)]
             [new-assignments (uncover-live-roots assignments '() '())])
         `(program ,vars-without-types (type ,t) (defines ,@new-defines) (initialize ,s ,h) ,@new-assignments (return ,final-e)))])))



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
    [`(define (,f) ,i ,instrs ...)
     `(define (,f) ,i ,@(append-map lower-conditionals instrs))]
    [`(program ,i (type ,t) (defines ,defn ...) ,instrs ...)
     `(program ,i (type ,t) (defines ,@(map lower-conditionals defn)) ,@(append-map lower-conditionals instrs))]
    [x `(,x)]))

; x86* -> x86
(define patch-instr
  (match-lambda
    [`(cmpq ,arg1 (int ,i)) ; Second argument to cmpq can't be immediate value
     `((movq (int ,i) (reg rax))
       (cmpq ,arg1 (reg rax)))]
    [`(movq (reg ,r) (reg ,r)) ; Kill redundant moves
     `()]
    [`(,(and op (or `movzbq `leaq)) ,arg1 ,(and arg2 (or `(stack ,_) `(global-value ,_) `(offset ,_ ,_))))
     `((,op ,arg1 (reg rax))
       (movq (reg rax) ,arg2))]
    [`(,op (offset (stack ,i) ,n) ,arg2)
     (append `((movq (stack ,i) (reg r11)))
             (patch-instr `(,op (offset (reg r11) ,n) ,arg2)))]
    [`(,op ,arg1 (offset (stack ,i) ,n))
     (append `((movq (stack ,i) (reg r11)))
             (patch-instr `(,op ,arg1 (offset (reg r11) ,n))))]
    [`(,op ,(and arg1 (or `(stack ,_) `(global-value ,_) `(offset ,_ ,_)))
           ,(and arg2 (or `(stack ,_) `(global-value ,_) `(offset ,_ ,_))))
     ; Both arguments can't be memory locations
     `((movq ,arg1 (reg rax))
       (,op  (reg rax) ,arg2))]
    [`(define (,f) ,i ,instrs ...)
     `(define (,f) ,i ,@(append-map patch-instr instrs))]
    [`(program ,i (type ,t) (defines ,defn ...) ,instrs ...)
     `(program ,i (type ,t) (defines ,@(map patch-instr defn)) ,@(append-map patch-instr instrs))]
    [x86-e `(,x86-e)]))

; x86* -> actual, honest-to-goodness x86-64
(define print-x86-64
  (match-lambda
    [`(define (,f) ,i ,instrs ...)
     (let ([wcsr (written-callee-save-regs instrs)])
       (apply string-append
              `(,(format "\t.globl ~a\n" (label f))
                ,(symbol->string (label f))
                ":\n"

                ,(display-instr "pushq" "%rbp")
                ,(display-instr "movq" "%rsp, %rbp")
                ,(save-callee-regs instrs i wcsr)
                "\n"
                ,(apply string-append (map print-x86-64-instr instrs))
                "\n"
                ,(restore-callee-regs instrs i wcsr)
                ,(display-instr "popq" "%rbp")
                ,(display-instr "retq" ""))))]
    [`(program ,i (type ,t) (defines ,defn ...) ,instrs ...)
     (let ([wcsr (written-callee-save-regs instrs)])
       (apply string-append
              `(,(string-join (map print-x86-64 defn) "\n\n")
                "\n"
                ,(format "\t.globl ~a\n" (label `main))
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
     (if (zero? i) "" (display-instr "subq" "$~a, %rsp" i)) ;; this was (if (null? i) .... isn't i a number?
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
     (if (zero? i) "" (display-instr "addq" "$~a, %rsp" i))))) ;; this was (if (null? i) .... isn't i a number?

(define print-x86-64-instr
  (match-lambda
    [`(,op ,a1 ,a2) (display-instr "~a" "~a, ~a"
                                   (symbol->string op)
                                   (print-x86-64-arg a1)
                                   (print-x86-64-arg a2))]
    [`(label ,sym) (string-append (symbol->string sym) ":\n")]
    [`(callq ,l) (display-instr "callq" "~a"
                                (label l))]
    [`(indirect-callq ,arg) (display-instr "callq" "*~a" (print-x86-64-arg arg))]
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
      [`(offset (stack ,s) ,n) (error "wtf r u doin")]

      ;; keeping them seperate to easily see if we need any other global-value
      [`(global-value rootstack_begin) (format "~a(%rip)" (label 'rootstack_begin))]
      [`(global-value free_ptr) (format "~a(%rip)" (label 'free_ptr))]
      [`(global-value fromspace_end) (format "~a(%rip)" (label 'fromspace_end))]
      [`(stack ,s) (format "~a(%rbp)" s)]

      [`(function-ref ,l) (format "~a(%rip)" (label l))]
      [`(stack-arg ,i)    (format "~a(%rsp)" i)])))

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
      [`macosx (string->symbol
                (string-append "_" (symbol->string (sanitize-label l))))]
      [_ (sanitize-label l)])))

(define sanitize-label
  (compose1 string->symbol
            list->string
            (curry append-map
                   (λ (c) (if (or (char-alphabetic? c)
                                  (char-numeric? c)
                                  (char=? c #\_))
                              `(,c)
                              ((compose1 string->list
                                         number->string
                                         char->integer) c))))
            string->list
            symbol->string))

(define genlabel
  (compose1 gensym label))

; [Pass]
(define r1-passes `(("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,flatten ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ; ("assign homes" ,(assign-homes `()) ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

; [Pass]
(define r2-passes `(; Implicit typecheck pass occurs at beginning
                    ("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,flatten ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

; [Pass]
(define r3-passes `(; Implicit typecheck pass occurs at beginning
                    ("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("flatten" ,flatten ,interp-C)
                    ("expose-allocation" ,(expose-allocation 12800 `()) ,interp-C)
                    ("uncover-call-live-roots" ,uncover-call-live ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

; [Pass]
(define r4-passes `(; Implicit typecheck pass occurs at beginning
                    ("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("reveal-functions" ,(reveal-functions (set)) ,interp-scheme)
                    ("flatten" ,flatten ,interp-C)
                    ("expose-allocation" ,(expose-allocation 12800 `()) ,interp-C)
                    ("uncover-call-live-roots" ,uncover-call-live ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

; [Pass]
(define r5-passes `(; Implicit typecheck pass occurs at beginning
                    ("uniquify" ,(uniquify '()) ,interp-scheme)
                    ("reveal-functions" ,(reveal-functions (set)) ,interp-scheme)
                    ("convert-to-closures" ,convert-to-closures ,interp-scheme)
                    ("flatten" ,flatten ,interp-C)
                    ("expose-allocation" ,(expose-allocation 12800 `()) ,interp-C)
                    ("uncover-call-live-roots" ,uncover-call-live ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))
