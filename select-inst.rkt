#lang racket

(require "has-types.rkt")

(provide select-instructions)

(define arg-registers '(rsi rdx rcx r8 r9)) ;; rdi is used for passing the rootstack variable

(define toplevels '())
(define toplevel-names '())

(define (clean-vars-hack vars)
  (filter (λ (var) (and (symbol? var) (not (memv var toplevel-names)))) vars))

(define select-instructions
  (compose1
   (match-lambda
     [`(program (,vars ...) (type ,t) (defines ,defs ...) ,assignments+return ...)
      (begin
        (set! toplevels defs)
        (set! toplevel-names (map (λ (def) (car (list-ref def 1))) defs))
        (let-values ([(new-defines define-vars max-stack) (process-defines defs)]
                     [(new-assignments+return added-vars) (select-instructions-inner assignments+return (gensym 'rootstack.) '())])
          `(program (,(clean-vars-hack (remove-duplicates (append vars added-vars))) ,max-stack) (type ,t) (defines ,@new-defines) ,@new-assignments+return)))])
   strip-has-types)) ; Discard types; they're no longer needed

(define (process-defines defines)
  (cond
    ((null? defines) (values null null -1))
    (else
     (let-values
         ([(new-define new-vars max-stack-needed) (select-instructions-inner (list (car defines)) 'dummy '())]
          [(rest-defines rest-vars rest-max-stack-needed) (process-defines (cdr defines))])
       (values (cons new-define rest-defines)
               (remove-duplicates (append new-vars rest-vars))
               (max max-stack-needed rest-max-stack-needed))))))

(define (encode-arg arg)
  (cond
    ((equal? arg `(void)) `(int 0))
    ((boolean? arg) `(int ,(if arg 1 0)))
    ((integer? arg) `(int ,arg))
    ((symbol? arg) `(var ,arg))
    (else (error 'encode-arg (format "something's wrong with the argument ~a" arg)))))

(define (find-top-calls body toplevels)
  (cond
    ((empty? body) '())
    (else
     (match (car body)
       [`(assign ,var (function-ref ,f))
        (append (filter (λ (top) (eqv? f (car (list-ref top 1)))) toplevels)
                (find-top-calls (cdr body) toplevels))]
       [else (find-top-calls (cdr body) toplevels)]))))

(define (tagof T)
  (match T
    ['Integer          #b000]
    ['Boolean          #b001]
    [`(Vector ,args ...)   #b010]
    [`(Vectorof ,args ...) #b010]
    [`(,in ... -> ,out) #b011]
    ['Void             #b100]
    [else (error 'tagof "undefined type : ~a" T)]))

(define select-instructions-inner
  (lambda (assignments+return current-rootstack-var added-vars)
    (cond
      ((empty? assignments+return) (values '() added-vars))
      (else
       (match (car assignments+return)
         [`() '()]
         ;; define
         [`(define (,f ,arg-types ...) : ,t ,local-vars ,body ...) ;; REFACTOR : treat rootstack-local-var as an arg
          (let* ([rootstack-local-var (gensym 'rslocal.)]
                 [arg-names (map (λ (arg) (car arg)) arg-types)]
                 [num-vars (length arg-names)]
                 [stack-places-num (if (<= num-vars 5) 0 (- num-vars 5))]
                 [register-num (if (>= num-vars 5) 5 num-vars)]
                 [pass-arg-places (append (map (λ (reg) `(reg ,reg)) (take arg-registers register-num))
                                          (build-list stack-places-num (λ (x) `(stack ,(* 8 (add1 (add1 x)))))))]
                 
                 [init             `((movq (reg rdi) (var ,rootstack-local-var))
                                     ,@(map (lambda (var plc) `(movq ,plc (var ,var))) arg-names pass-arg-places))]
                 [maxStack (let* ([topCallDefs (find-top-calls body toplevels)]
                                  [max-stacks (cons 0 (map (λ (def) (let ([num-var (length (cdr (list-ref def 1)))])
                                                                      (if (<= num-var 5) 0 (- num-var 5)))) topCallDefs))])
                             (apply max max-stacks))])
            (let-values ([(new-body new-vars) (select-instructions-inner body rootstack-local-var '())])
              (values `(define (,f) ,(add1 num-vars) (,(cons rootstack-local-var (append arg-names new-vars local-vars)) ,maxStack) ,@init ,@new-body)
                      new-vars
                      stack-places-num)))]
         
         ;; assign
         [`(assign ,var ,rhs)
          (let-values ([(new-assignments new-added-vars)
                        (select-instructions-inner (cdr assignments+return) current-rootstack-var added-vars)])
            (match rhs
              [`(void)      (values (append `((movq (int 0) (var ,var))) new-assignments) new-added-vars)]
              [(? symbol?)  (values (append `((movq (var ,rhs) (var ,var))) new-assignments) new-added-vars)]
              [(? integer?) (values (append `((movq (int ,rhs) (var ,var))) new-assignments) new-added-vars)]
              [(? boolean?) (values (append `((movq (int ,(if rhs 1 0)) (var ,var))) new-assignments) new-added-vars)]
              [`(read) (values (append `((callq read_int) (movq (reg rax) (var ,var))) new-assignments) new-added-vars)]
              [`(- ,arg) (values (append `((movq (,(if (integer? arg) 'int 'var) ,arg) (var ,var)) (negq (var ,var))) new-assignments) new-added-vars)]
              [`(+ ,arg1 ,arg2)
               (values (append 
                        (cond
                          [(equal? arg1 var) `((addq ,arg1 ,var))]
                          [(equal? arg2 var) `((addq ,arg2 ,var))]
                          [else
                           `((movq (,(if (integer? arg1) 'int 'var) ,arg1) (var ,var))
                             (addq (,(if (integer? arg2) 'int 'var) ,arg2) (var ,var)))
                           ])
                        new-assignments)
                       new-added-vars)]
              [`(not ,arg) ;; arg : var|bool (kudos to the typechecker)
               (values (append 
                        (cond
                          [(boolean? arg) `((movq (int ,(if arg 1 0)) (var ,var)) (xorq (int 1) (var ,var)))]
                          [(symbol? arg) `((movq (var ,arg) (var ,var)) (xorq (int 1) (var ,var)))]
                          [else (error 'select-instructions "we shouldn't have as arg to 'not' any form other than boolean or var(symbol)")])
                        new-assignments)
                       new-added-vars)]
              [`(,comp-op ,arg1 ,arg2)
               #:when (memv comp-op '(< <= > >=))
               (let ([arg1-instr (encode-arg arg1)]
                     [arg2-instr (encode-arg arg2)]
                     [setter (match comp-op
                               ['< 'setl]['<= 'setle]['> 'setg]['>= 'setge])])
                 (values (append
                          `((cmpq ,arg1-instr ,arg2-instr)
                            (,setter (byte-reg al))
                            (movzbq (byte-reg al) (var ,var)))
                          new-assignments)
                         new-added-vars))]
              [`(eq? ,arg1 ,arg2)
               ;; TODO : refactor
               (let ([arg1-instr (encode-arg arg1) #;(cond [(equal? arg1 `(void)) `(int 0)]
                                                           [(boolean? arg1) `(int ,(if arg1 1 0))]
                                                           [(integer? arg1) `(int ,arg1)]
                                                           [(symbol? arg1)  `(var ,arg1)])]
                     [arg2-instr (encode-arg arg2) #;(cond [(equal? arg2 `(void)) `(int 0)]
                                                           [(boolean? arg2) `(int ,(if arg2 1 0))]
                                                           [(integer? arg2) `(int ,arg2)]
                                                           [(symbol? arg2)  `(var ,arg2)])])
                 (values (append `((cmpq ,arg1-instr ,arg2-instr)
                                   (sete (byte-reg al))
                                   (movzbq (byte-reg al) (var ,var)))
                                 new-assignments)
                         new-added-vars))]
              
              ;; inject
              [`(inject ,e ,T)
               (let* ([e-inst (encode-arg e)]
                      [new-instructions (if (or (equal? T 'Integer) (equal? T 'Boolean) (equal? T 'Void))
                                            `((movq ,e-inst (var ,var))
                                              (salq (int 3) (var ,var))
                                              (orq (int ,(tagof T)) (var ,var)))
                                            `((movq ,e-inst (var ,var)) ;; Vector or Function
                                              (orq (int ,(tagof T)) (var ,var))))])
                 (values (append new-instructions new-assignments)
                         (append new-added-vars added-vars)))]
              
              ;; project
              [`(project ,e ,T)              
               (let* ([e-inst (encode-arg e)]
                      [new-instructions (if (or (equal? T 'Integer) (equal? T 'Boolean) (equal? T 'Void))
                                            `((movq ,e-inst (var ,var))
                                              (andq (int 7) (var ,var)) ;; 7 is for anding with 111
                                              (if (eq? (var ,var) (int ,(tagof T)))
                                                  ((movq ,e-inst (var ,var))
                                                   (sarq (int 3) (var ,var)))
                                                  ((callq exit))))
                                            `((movq ,e-inst (var ,var))
                                              (andq (int 7) (var ,var))
                                              (if (eq? (var ,var) (int ,(tagof T)))
                                                  ((movq (int 3) (var ,var))
                                                   (notq (var ,var))
                                                   (andq ,e-inst (var ,var)))
                                                  ((callq exit)))))])
                 (values (append new-instructions new-assignments)
                         (append new-added-vars added-vars)))]
              
              ; TAGS
              
              ; Integer : 000
              ; Boolean : 001
              ; Vector  : 010
              ; Vectorof: 010
              ; ... -> ... : 011
              ; void : 100
              
              ;; boolean?
              [`(boolean? ,e) ;; e is tagged val
               (let ([e-inst (encode-arg e)])
                 (values (append
                          `((movq ,e-inst (var ,var))
                            (andq (int 7) (var ,var))
                            (if (eq? ,var (int 1)) (int 1) (int 0))))
                         added-vars))]
              
              ;; integer?
              [`(integer? ,e) ;; e is tagged val
               (let ([e-inst (encode-arg e)])
                 (values (append
                          `((movq ,e-inst (var ,var))
                            (andq (int 7) (var ,var))
                            (if (eq? ,var (int 0)) (int 1) (int 0))))
                         added-vars))]
              ;; vector?
              [`(vector? ,e) ;; e is tagged val
               (let ([e-inst (encode-arg e)])
                 (values (append
                          `((movq ,e-inst (var ,var))
                            (andq (int 7) (var ,var))
                            (if (eq? ,var (int 2)) (int 1) (int 0))))
                         added-vars))]
              
              ;; procedure?
              [`(procedure? ,e) ;; e is tagged val
               (let ([e-inst (encode-arg e)])
                 (values (append
                          `((movq ,e-inst (var ,var))
                            (andq (int 7) (var ,var))
                            (if (eq? ,var (int 3)) (int 1) (int 0))))
                         added-vars))]
              
              [`(void? ,e) ;; e is tagged val
               (let ([e-inst (encode-arg e)])
                 (values (append
                          `((movq ,e-inst (var ,var))
                            (andq (int 7) (var ,var))
                            (if (eq? ,var (int 4)) (int 1) (int 0))))
                         added-vars))]
              
              ;; function-ref
              [`(function-ref ,f)
               (values (append `((leaq (function-ref ,f) (var ,var))) new-assignments) new-added-vars)]

              
              
              ;; function application
              [`(app ,fun ,args ...)
               (let* ([move-rootstack `((movq (var ,current-rootstack-var) (reg rdi)))]
                      [num-vars (length args)]
                      [stack-places-num (if (<= num-vars 5) 0 (- num-vars 5))]
                      [register-num (if (>= num-vars 5) 5 num-vars)]
                      [passing-to-places (append (map (lambda (reg) `(reg ,reg)) (take arg-registers register-num))
                                                 (build-list stack-places-num (lambda (n) `(stack-arg ,(- (* 8 (add1 n)) 8)))))]
                      [move-arguments `(,@(map (lambda (param passing-to) `(movq ,(encode-arg param) ,passing-to)) args passing-to-places))])
                 (values (append 
                          `(,@move-rootstack
                            ,@move-arguments
                            (indirect-callq (var ,fun))
                            (movq (reg rax) (var ,var)))
                          new-assignments)
                         new-added-vars))]
              
              ;; (allocate n (Vector type))
              [`(allocate ,len (Vector ,types ...))
               (let* ([not-forward-ptr-bit 1]
                      [length len]
                      [pointer-mask
                       (string->number
                        (string-append "#b" ;; constructing a native binary, like #b1010
                                       (foldr string-append ""
                                              (reverse
                                               (map (lambda (type)
                                                      (match type
                                                        [`(Vector ,something ...) "1"]
                                                        [else "0"])) types)))))]
                      [tag (bitwise-ior not-forward-ptr-bit
                                        (arithmetic-shift length 1)
                                        (arithmetic-shift pointer-mask 7))])
                 
                 (values (append
                          `((movq (global-value free_ptr) (var ,var))
                            (addq (int ,(* 8 (+ len 1))) (global-value free_ptr))
                            (movq (int ,tag) (offset (var ,var) 0)))
                          new-assignments)
                         new-added-vars))]
              ;; vector-ref
              [`(vector-ref ,vec ,n)  ;; ASSUMPTION: vec is always var
               (values (append `((movq (offset (var ,vec) ,(* 8 (+ n 1))) (var ,var))) new-assignments) new-added-vars)]
              ;; vector-set!
              [`(vector-set! ,vec ,n ,arg)
               (let ([arg-exp
                      (match arg
                        [`(void)      `(int 0)]
                        [(? integer?) `(int ,arg)]
                        [(? boolean?) `(int ,(if arg 1 0))]
                        [(? symbol?) `(var ,arg)]
                        [else (error 'select-intr/vector-set! "wtf?")])])
                 ;; should we check the type of the arg?
                 (values (append 
                          `((movq ,arg-exp (offset (var ,vec) ,(* 8 (+ n 1))))
                            (movq (int 0) (var ,var)))
                          new-assignments)
                         new-added-vars))]
              
              [else (error 'select-instructions (format "don't know how to handle this rhs~a" rhs))]))]
         
         ;; initialize
         [`(initialize ,rootlen ,heaplen)
          (let-values ([(new-assignments new-added-vars)
                        (select-instructions-inner (cdr assignments+return) current-rootstack-var added-vars)])
            (values
             (append `((movq (int ,rootlen) (reg rdi))
                       (movq (int ,heaplen) (reg rsi))
                       (callq initialize)
                       (movq (global-value rootstack_begin) (var ,current-rootstack-var))) new-assignments)
             (cons current-rootstack-var new-added-vars)))]
         
         [`(call-live-roots (,root-vars ...) (collect ,bytes))
          (let ([new-rootstack-var (gensym 'rootstack.)])
            (let-values ([(new-assignments new-added-vars)
                          (select-instructions-inner (cdr assignments+return) new-rootstack-var added-vars)])
              (values
               (append
                `(;; pushing all the live roots onto the root stack
                  ,@(map (lambda (root-var offset) `(movq (var ,root-var) (offset (var ,current-rootstack-var) ,offset)))
                         root-vars (build-list (length root-vars) (lambda (x) (* x 8))))
                  
                  (movq (var ,current-rootstack-var) (var ,new-rootstack-var))
                  (addq (int ,(* 8 (length root-vars))) (var ,new-rootstack-var))
                  (movq (var ,new-rootstack-var) (reg rdi))
                  (movq (int ,bytes) (reg rsi))
                  (callq collect)
                  
                  ;; moving live roots back to the actual stack
                  ,@(map (lambda (offset root-var) `(movq (offset (var ,current-rootstack-var) ,offset) (var ,root-var)))
                         (build-list (length root-vars) (lambda (x) (* x 8))) root-vars))
                new-assignments)
               (cons new-rootstack-var added-vars))))]
         
         ;; (if (collection-needed? n) ((call-live-roots (,vars ...) (collect n))) ())
         [`(if (collection-needed? ,bytes) ,thns ,elss)
          
          (let ([end-data-var (gensym 'end-data.)]
                [less-than-var (gensym 'lt.)])
            (let-values ([(thns-new-ass thns-added-vars) (select-instructions-inner thns current-rootstack-var added-vars)]
                         [(elss-new-ass elss-added-vars) (select-instructions-inner elss current-rootstack-var added-vars)]
                         [(new-assignments new-added-vars) (select-instructions-inner (cdr assignments+return) current-rootstack-var added-vars)])
              (values
               (append
                `((movq (global-value free_ptr) (var ,end-data-var))
                  (addq (int ,bytes) (var ,end-data-var))
                  (cmpq (global-value fromspace_end) (var ,end-data-var))
                  (setl (byte-reg al))
                  (movzbq (byte-reg al) (var ,less-than-var))
                  (if (eq? (int 0) (var ,less-than-var))
                      ,thns-new-ass
                      ,elss-new-ass))
                new-assignments)
               (cons end-data-var (cons less-than-var (append thns-added-vars added-vars elss-added-vars new-added-vars))))))]
         
         ;; if
         [`(if (eq? ,exp1 ,exp2) ,thns ,elss)
          (let ([exp1-inst (cond [(eqv? exp1 `(void)) `(int 0)]
                                 [(boolean? exp1)     `(int ,(if exp1 1 0))]
                                 [(integer? exp1)     `(int ,exp1)]
                                 [(symbol? exp1)      `(var ,exp1)])]
                [exp2-inst (cond [(eqv? exp2 `(void)) `(int 0)]
                                 [(boolean? exp2)     `(int ,(if exp2 1 0))]
                                 [(integer? exp2)     `(int ,exp2)]
                                 [(symbol? exp2)      `(var ,exp2)])])
            (let-values ([(out-thns added-thns) (select-instructions-inner thns current-rootstack-var added-vars)]
                         [(out-elss added-elss) (select-instructions-inner elss current-rootstack-var added-vars)]
                         [(new-assignments new-added-vars) (select-instructions-inner (cdr assignments+return) current-rootstack-var added-vars)])
              (values
               (append
                `((if (eq? ,exp1-inst ,exp2-inst)
                      ,out-thns
                      ,out-elss)) new-assignments)
               (append added-thns added-elss new-added-vars added-vars))))]
         
         ;; return
         [`(return ,e)
          (let ([e-int (if (eqv? e `(void))
                           `(int 0)
                           (if (integer? e)
                               `(int ,e)
                               (if (boolean? e)
                                   (if e `(int 1) `(int 0))
                                   `(var ,e))))])
            (let-values ([(new-assignments new-added-vars)
                          (select-instructions-inner (cdr assignments+return) current-rootstack-var added-vars)])
              (values
               (append `((movq ,e-int (reg rax))) new-assignments)
               (if (equal? (car e-int) 'var) (cons e new-added-vars) new-added-vars))))])))))
