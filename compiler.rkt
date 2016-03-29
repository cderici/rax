#lang racket

(require "utilities.rkt" "interp.rkt" "testing.rkt"
         "flatten.rkt" "assign-homes.rkt" "typecheck.rkt"
         "uncover-types.rkt" "select-inst.rkt" "has-types.rkt")

(provide r1-passes
         r2-passes
         r3-passes
         r4-passes
         r5-passes
         r6-passes
         r7-passes
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

;; R7 -> R6 (come on, it's in the freaking name)
(define r7->r6
  (λ (expr)
    (match expr
      [`(program ,defs ... ,e)  `(program ,@(map r7->r6 defs)
                                          ,(r7->r6 e))]
      [(or (? fixnum?) `(read)) `(inject ,expr Integer)]
      [(? boolean?)             `(inject ,expr Boolean)]
      [`(+ ,e1 ,e2)             `(inject
                                  (+ (project ,(r7->r6 e1) Integer)
                                     (project ,(r7->r6 e2) Integer))
                                  Integer)]
      [`(- ,e)                  `(inject
                                  (- (project ,(r7->r6 e) Integer))
                                  Integer)]
      [`(not ,e)                `(eq? ,(r7->r6 e) (inject #f Boolean))]
      [`(vector-ref ,e1 ,e2)    `(let ([tmp1 (project ,(r7->r6 e1) (Vectorof Any))])
                                   (let ([tmp2 (project ,(r7->r6 e2) Integer)])
                                     (vector-ref tmp1 tmp2)))]
      [`(vector-set! ,v ,i ,e)  `(let ([tmp1 (project ,(r7->r6 v) (Vectorof Any))])
                                   (let ([tmp2 (project ,(r7->r6 i) Integer)])
                                     (inject (vector-set! tmp1 tmp2 ,(r7->r6 e))
                                             Void)))]
      [`(if ,e1 ,e2 ,e3)        `(if (eq? ,(r7->r6 e1) (inject #f Boolean))
                                     ,(r7->r6 e2)
                                     ,(r7->r6 e3))]
      [`(eq? ,e1 ,e2)           `(eq? ,(r7->r6 e1) ,(r7->r6 e2))]
      [`(and ,e1 ,e2)           `(let ([tmp ,(r7->r6 e1)])
                                   (if (eq? tmp (inject #f Boolean))
                                       tmp
                                       ,(r7->r6 e2)))]
      [`(let ([,x ,e1]) ,e2)    `(let ([,x ,(r7->r6 e1)])
                                   ,(r7->r6 e2))]
      [`(define (,f ,args ...) ,e)
       `(let ([typed-args (map type-as-any args)])
          `(define (,f ,@typed-args) : Any ,(r7-to-r6 e)))]
      [`(lambda (,xs ...) ,e)
       (let ([typed-xs (map type-as-any xs)])
         `(lambda ,typed-xs : Any ,(r7->r6 e)))]
      [`(vector ,e ...)
       (let ([e^ (map r7->r6 e)])
         `(inject (vector ,@e^) (Vectorof Any)))]
      [`(app ,e-rator ,e-rands ...)
       (let ([anys (map (const `Any) e-rands)])
         `(app (project ,(r7->r6 e-rator) (,@anys -> Any))
               ,@(map r7->r6 e-rands)))]
      [_ expr])))

(define type-as-any
  (λ (x) `[x : Any]))

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
      [`(has-type (let ([,x ,e]) ,body) ,t)
       `(has-type (let ([,x ,((reveal-functions locals) e)])
                    ,((reveal-functions (set-add locals x)) body)) ,t)]
      [`(has-type (if ,cnd ,thn ,els) ,t)
       `(has-type (if ,((reveal-functions locals) cnd)
                      ,((reveal-functions locals) thn)
                      ,((reveal-functions locals) els)) ,t)]
      [`(has-type (lambda: ([,args : ,tys] ...) : ,ty-ret ,body) ,t)
       (let ([arg-tys (map (λ (a t) `[,a : ,t]) args tys)])
         `(has-type (lambda: (,@arg-tys) : ,ty-ret ,((reveal-functions (foldr (λ (a l) (set-add l a)) locals args)) body)) ,t))]
      
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
      
      [`(has-type (,op ,args ...) ,t)
       #:when (set-member? prim-names op)
       `(has-type (,op ,@(map (reveal-functions locals) args)) ,t)]
      [`(has-type (,rator ,rands ...) ,t)
       `(has-type (app ,((reveal-functions locals) rator)
                       ,@(map (reveal-functions locals) rands)) ,t)]
      [`(has-type ,n ,t)
       (if (symbol? n)
           (if (set-member? locals n)
               `(has-type ,n ,t)
               `(has-type (function-ref (has-type ,n ,t)) ,t))
           `(has-type ,n ,t))]
      [e e])))

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
    [`(define ,(list fun `[,xs : ,ty-args] ...) : ,ty-ret ,body)
     (match-let* ([clos              (gensym 'clos_dummy_param)]
                  [args              (map (λ (x ty-arg) `[,x : ,(closurize-fun-ty ty-arg)]) xs ty-args)]
                  [new-args          (cons `[,clos : _] args)]
                  [new-ty-ret        (closurize-fun-ty ty-ret)]
                  [(cons body^ defs) (closure-worker body)])
       (cons `(define (,fun ,@new-args) : ,new-ty-ret ,body^)
             defs))]
    [`(has-type (app ,rator ,rands ...) ,t)
     (match-let* ([(cons rator^ defs1)               (closure-worker rator)]
                  [(list (cons rands^ defs2) ...)    (map closure-worker rands)]
                  [tmp                               (gensym 'closure_app_temp)]
                  [`(has-type ,_ (Vector ,rator^-t)) rator^]
                  [t^                                (closurize-fun-ty t)])
       (cons `(has-type (let ([,tmp ,rator^])
                          (has-type (app (has-type (vector-ref (has-type ,tmp (Vector ,rator^-t)) (has-type 0 Integer))
                                                   ,rator^-t)
                                         (has-type ,tmp _) ,@rands^)
                                    ,t^))
                        ,t^)
             (append defs1 (shallow-flatten defs2))))]
    [`(has-type (function-ref (has-type ,f (,ty-args1 ... -> ,ty-ret1))) (,ty-args2 ... -> ,ty-ret2))
     (let ([ty-args1^ (map closurize-fun-ty ty-args1)]
           [ty-ret1^  (closurize-fun-ty     ty-ret1)]
           [ty-args2^ (map closurize-fun-ty ty-args2)]
           [ty-ret2^  (closurize-fun-ty     ty-ret2)])
       (cons `(has-type (vector (has-type (function-ref (has-type ,f (,@ty-args1^ -> ,ty-ret1)))
                                          (_ ,@ty-args2^ -> ,ty-ret2^)))
                        (Vector (_ ,@ty-args2^ -> ,ty-ret2^)))
             `()))]
    [`(has-type (let ([,x ,e]) ,body) ,t)
     (match-let ([(cons e^    defs1) (closure-worker e)]
                 [(cons body^ defs2) (closure-worker body)]
                 [t^                 (closurize-fun-ty t)])
       (cons `(has-type (let ([,x ,e^]) ,body^) ,t^)
             (append defs1 defs2)))]
    [`(has-type (if ,cnd ,thn ,els) ,t)
     (match-let ([(cons cnd^ defs1) (closure-worker cnd)]
                 [(cons thn^ defs2) (closure-worker thn)]
                 [(cons els^ defs3) (closure-worker els)]
                 [t^                (closurize-fun-ty t)])
       (cons `(has-type (if ,cnd^ ,thn^ ,els^) ,t^)
             (append defs1 defs2 defs3)))]
    [(and lam `(has-type (lambda: ([,xs : ,ty-args] ...) : ,ty-ret ,body) ,t))
     (match-let* ([name (gensym "lam")]
                  [clos (gensym "clos_param_lam")]
                  [ty-args^ (map closurize-fun-ty ty-args)]
                  [args (map (λ (x ty-arg) `[,x : ,ty-arg]) xs ty-args^)]
                  [ty-ret^ (closurize-fun-ty ty-ret)]
                  [t^      (closurize-fun-ty t)]
                  [freevars (fvs lam)]
                  [(cons body^ defs) (closure-worker body)]
                  [(cons body^^ _)
                   (foldr (match-lambda**
                           [((cons freevar-e freevar-t) (cons b n))
                            (cons `(has-type (let ([,freevar-e (has-type (vector-ref
                                                                          (has-type ,clos _)
                                                                          (has-type ,n Integer))
                                                                         ,freevar-t)]) ,b) ,ty-ret)
                                  (- n 1))])
                          (cons body^ (length freevars))
                          freevars)])
       (cons `(has-type (vector (has-type (function-ref (has-type ,name
                                                                  (,@ty-args^ -> ,ty-ret^)))
                                          (_ ,@ty-args^ -> ,ty-ret^)) ,@(map has-typify freevars))
                        ,t^)
             (cons `(define (,name [,clos : _] ,@args) : ,ty-ret^
                      ,body^^) defs)))]
    [`(has-type (,op ,args ...) ,t)
     #:when (set-member? prim-names op)
     (match-let ([(list (cons args^ defs) ...) (map closure-worker args)]
                 [t^                           (closurize-fun-ty t)])
       (cons `(has-type (,op ,@args^) ,t^)
             (shallow-flatten defs)))]
    [`(has-type ,e ,t)
     (cons `(has-type ,e ,(closurize-fun-ty t))
           `())]))

(define has-typify
  (match-lambda
    [(cons e t) `(has-type ,e ,t)]))

; Type -> Type
(define closurize-fun-ty
  (match-lambda
    [`(,ty-args ... -> ,ty-res) `(Vector (_ ,@ty-args -> ,ty-res))]
    [`(Vector ,tys ...) `(Vector ,@(map closurize-fun-ty tys))]
    [ty ty]))

; Exp -> [(Var, Type)]
; (Invariant: output is sorted in ascending order by variables, no duplicate variable names)
(define fvs
  (letrec
      ; Exp -> Set (Var, Type)
      ([freevars
        (λ (exp)
          (match exp
            [`(has-type (lambda: ([,xs : ,ty-args] ...) : ,ty-ret ,body) ,t)
             (set-subtract (freevars body) (list->set (map cons xs ty-args)))]
            [`(has-type (let ([,x (has-type ,e ,e-t)]) ,body) ,t)
             (set-subtract (set-union (freevars e) (freevars body)) (set (cons x e-t)))]
            [`(has-type (if ,cnd ,thn ,els) ,t)
             (set-union (freevars cnd)
                        (freevars thn)
                        (freevars els))]
            [`(has-type (function-ref ,f) ,t) (freevars f)]
            [`(has-type (app ,rator ,rands ...) ,t)
             (foldr set-union (set) (map freevars (cons rator rands)))]
            [`(has-type (,op ,args ...) ,t)
             #:when (set-member? prim-names op)
             (foldr set-union (set) (map freevars args))]
            [`(has-type ,x ,t)
             (if (symbol? x)
                 (set (cons x t))
                 (set))]
            [_ (set)]))])
    (λ (e)
      (sort (set->list (freevars e))
            (λ (x y) symbol<? (car x) (car y))))))

;; C3 -> C3
;; expose-allocation (after flatten)
(define expose-allocation
  (λ (heap-size-bytes)
    (λ (e)
      (match e
        [`(has-type ,e ,t)
         `((has-type ,((expose-allocation heap-size-bytes) e) ,t))]
        [`(if ,c ,t ,e)
         `(if ,c
              ,(foldr append null (map (expose-allocation heap-size-bytes) t))
              ,(foldr append null (map (expose-allocation heap-size-bytes) e)))]
        [`(assign ,lhs (has-type (vector ,e ...) ,t))
         (let* ([len (length e)]
                [bytes (+ 8 (* len 8))])
           `((if (collection-needed? ,bytes)
                 ((collect ,bytes))
                 ())
             (assign ,lhs (allocate ,len ,t))
             ,@(map (λ (vector-element position)
                      (let ([void-var (string->symbol (string-append "void." (begin (set! void-count (add1 void-count))
                                                                                    (number->string void-count))))])
                        `(assign ,void-var (vector-set! ,lhs ,position ,vector-element))))
                    e (range len))))]
        
        [`(define (,f ,arg-types ...) : ,t ,vars* ,body ...)
         (let* ([new-body (foldr append null (map (expose-allocation heap-size-bytes) body))]
                [new-vars (getVars new-body)])
           `(define (,f ,@arg-types) : ,t ,(remove-duplicates (append new-vars vars*)) ,@new-body))]
        
        [`(program (,vars ...) (type ,t) (defines ,defs ...) ,main-assignments ... (return ,final-e))
         (let* ([new-defines (map (expose-allocation heap-size-bytes) defs)]
                [new-main-assignments (foldr append null (map (expose-allocation heap-size-bytes) main-assignments))]
                [new-vars (remove-duplicates (append (getVars new-main-assignments) (foldr append null (map getVars new-defines))))])
           `(program ,new-vars (type ,t) (defines ,@new-defines) (initialize 10000 ,heap-size-bytes) ,@new-main-assignments (return ,final-e)))]
        
        [else `(,e)]))))

(define (uncover-live-roots assignments current-lives out)
  (cond
    ((empty? assignments) (reverse out))
    (else (match (car assignments)
            [`(has-type ,e ,t)
             (let ([e-uncovered (uncover-live-roots (list e) current-lives '())])
               (uncover-live-roots (cdr assignments) current-lives (cons `(has-type ,@e-uncovered ,t) out)))]
            [`(assign ,var (allocate ,n (Vector ,some-type ...)))
             (uncover-live-roots (cdr assignments) (cons var current-lives) (cons (car assignments) out))]
            
            [`(if (collection-needed? ,n) ((collect ,n)) ())
             (uncover-live-roots (cdr assignments) current-lives
                                 (cons `(if (collection-needed? ,n)
                                            ((call-live-roots ,current-lives (collect ,n)))
                                            ()) out))]
            [`(if ,c ,t ,e)
             (let ([t-uncovered (uncover-live-roots t current-lives '())]
                   [e-uncovered (uncover-live-roots e current-lives '())])
               (uncover-live-roots (cdr assignments) current-lives (cons `(if ,c ,t-uncovered ,e-uncovered) out)))]
            [else (uncover-live-roots (cdr assignments) current-lives (cons (car assignments) out))]))))

;; C3 -> C3
(define uncover-call-live
  (λ (e)
    (match e
      [`(define (,f ,arg-types ...) : ,t ,vars* ,body ...)
       (let ([new-body (uncover-live-roots body '() '())])
         `(define (,f ,@arg-types) : ,t ,vars* ,@new-body))]
      
      [`(program ,vars-without-types (type ,t) (defines ,defs ...) (initialize ,s ,h) ,assignments ... (return ,final-e))
       (let ([new-defines (map uncover-call-live defs)]
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
                    ("expose-allocation" ,(expose-allocation 12800) ,interp-C)
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
                    ("expose-allocation" ,(expose-allocation 12800) ,interp-C)
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
                    ("expose-allocation" ,(expose-allocation 12800) ,interp-C)
                    ("uncover-call-live-roots" ,uncover-call-live ,interp-C)
                    ("select instructions" ,select-instructions ,interp-x86)
                    ("register-allocation" ,(register-allocation 5) ,interp-x86)
                    ("lower-conditionals" ,lower-conditionals ,interp-x86)
                    ("patch instructions" ,patch-instr ,interp-x86)
                    ("print x86" ,print-x86-64 #f)))

(define r6-passes `todo)
(define r7-passes `todo)