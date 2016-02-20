#lang racket

(provide select-instructions)


(define select-instructions
  (match-lambda
    [`(program (,vars ...) (type ,t) ,assignments+return ...)
     (let-values ([(new-assignments+return added-vars) (select-instructions-inner assignments+return (gensym 'rootstack.) '() '())])
       `(program ,(remove-duplicates (append vars added-vars)) (type ,t) ,@new-assignments+return))]))


;; C2 -> x86_1*
;; doesn't change the (program (vars) assignments ... return) structure
(define select-instructions-inner
  (lambda (assignments+return rootstack-var added-vars out-assignments)
    (cond
      ((empty? assignments+return) (values (reverse out-assignments) added-vars))
      (else 
       (match (car assignments+return)  
         [`() '()]
         ;; assign
         [`(assign ,var ,rhs)
          (select-instructions-inner
           (cdr assignments+return)
           rootstack-var
           added-vars
           (append
            (reverse 
             (match rhs
               [`(void)      `((movq (int 0)             (var ,var)))]
               [(? symbol?)  `((movq (var ,rhs)          (var ,var)))]
               [(? integer?) `((movq (int ,rhs)          (var ,var)))]
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
                (let ([arg1-instr (cond [`(void)         `(int 0)]
                                        [(boolean? arg1) `(int ,(if arg1 1 0))]
                                        [(integer? arg1) `(int ,arg1)]
                                        [(symbol? arg1)  `(var ,arg1)])]
                      [arg2-instr (cond [`(void)         `(int 0)]
                                        [(boolean? arg2) `(int ,(if arg2 1 0))]
                                        [(integer? arg2) `(int ,arg2)]
                                        [(symbol? arg2)  `(var ,arg2)])])
                  `((cmpq ,arg1-instr ,arg2-instr)
                    (sete (byte-reg al))
                    (movzbq (byte-reg al) (var ,var))))]
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
                  
                  `((movq (global-value free_ptr) (var ,var))
                    (addq (int ,(* 8 (+ len 1))) (global-value free_ptr))
                    (movq (int ,tag) (offset (var ,var) 0))))]
               ;; vector-ref
               [`(vector-ref ,vec ,n)  ;; ASSUMPTION: vec is always var
                `((movq (offset (var ,vec) ,(* 8 (+ n 1))) (var ,var)))]
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
                  `((movq ,arg-exp (offset (var ,vec) ,(* 8 (+ n 1))))))]
               
               [else (error 'select-instructions "don't know how to handle this rhs~a")])) out-assignments))]
         ;; initialize
         [`(initialize ,rootlen ,heaplen)
          (select-instructions-inner
           (cdr assignments+return)
           rootstack-var
           (cons rootstack-var added-vars)
           (append (reverse `((movq (int ,rootlen) (reg rdi))
                              (movq (int ,heaplen) (reg rsi))
                              (callq initialize)
                              (movq (global-value rootstack_begin) (var ,rootstack-var)))) out-assignments))]
         
         
         [`(call-live-roots (,root-vars ...) (collect ,bytes))
          (let ([new-rootstack-var (gensym 'rootstack.)])
            (select-instructions-inner
             (cdr assignments+return)
             new-rootstack-var
             (cons new-rootstack-var added-vars)
             (append
              (reverse 
               `(;; pushing all the live roots onto the root stack
                 ,@(map (lambda (root-var offset) `(movq (var ,root-var) (offset (var ,rootstack-var) ,offset)))
                        root-vars (build-list (length root-vars) (lambda (x) (* x 8))))
                 
                 (movq (var ,rootstack-var) (var ,new-rootstack-var))
                 (addq (int ,(length root-vars)) (var ,new-rootstack-var))
                 (movq (var ,new-rootstack-var) (reg rdi))
                 (movq (int ,bytes) (reg rsi))
                 (callq collect)
                 
                 ;; moving live roots back to the actual stack
                 ,@(map (lambda (offset root-var) `(movq (offset (var ,rootstack-var) ,offset) (var ,root-var)))
                        (build-list (length root-vars) (lambda (x) (* x 8))) root-vars))) out-assignments)))]
         
         
         ;; (if (collection-needed? n) ((call-live-roots (,vars ...) (collect n))) ())     
         [`(if (collection-needed? ,bytes) ,thns ,elss)
          (let ([end-data-var (gensym 'end-data.)]
                [less-than-var (gensym 'lt.)])
            (let-values ([(elss-new-ass elss-added-vars) (select-instructions-inner elss rootstack-var added-vars '())]
                         [(thns-new-ass thns-added-vars) (select-instructions-inner thns rootstack-var added-vars '())])
              (select-instructions-inner
               (cdr assignments+return)
               rootstack-var
               (cons end-data-var (cons less-than-var (append elss-added-vars thns-added-vars added-vars)))
               (append
                (reverse `((movq (global-value free_ptr) (var ,end-data-var))
                           (addq (int ,bytes) (var ,end-data-var))
                           (cmpq (var ,end-data-var) (global-value fromspace_end))
                           (setl (byte-reg al))
                           (movzbq (byte-reg al) (var ,less-than-var))
                           (if (eq? (int 0) (var ,less-than-var))
                               ,elss-new-ass
                               ,thns-new-ass))) out-assignments))))]
         
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
            (select-instructions-inner
             (cdr assignments+return)
             rootstack-var
             added-vars
             (append
              (reverse
               (let-values ([(out-thns added-thns) (select-instructions-inner thns rootstack-var added-vars '())]
                            [(out-elss added-elss) (select-instructions-inner elss rootstack-var added-vars '())])
                 `((if (eq? ,exp1-inst ,exp2-inst)
                       ,out-thns
                       ,out-elss)))) out-assignments)))]         
         [`(return ,e)
          (let ([e-int (if (eqv? e `(void))
                           `(int 0)
                           (if (integer? e)
                               `(int ,e)
                               (if (boolean? e)
                                   (if e `(int 1) `(int 0))
                                   `(var ,e))))])
            (select-instructions-inner
             (cdr assignments+return)
             rootstack-var
             added-vars
             (append 
              `((movq ,e-int (reg rax))) out-assignments)))])))))
