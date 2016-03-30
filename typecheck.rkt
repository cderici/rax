#lang racket

(provide typechecker)

(require "utilities.rkt")

(define type-predicates (set `boolean? `integer? `vector? `procedure?))

(define is-ftype
  (match-lambda
    [`Boolean              #t]
    [`Integer              #t]
    [`(Vector Any Any ...) #t]
    [`(Vectorof Any)       #t]
    [`(Any ... -> Any)     #t]
    [_                     #f]))

; R5 -> Type
(define typecheck
  (λ (env)
    (λ (expr)
      (match expr
        [(? fixnum?)
         `(has-type ,expr Integer)]
        [(? boolean?)
         `(has-type ,expr Boolean)]
        [`(vector ,exp1 ,exps ...)
         (match-let
             ([(and es (list `(has-type ,_ ,ts) ...))
               (map (typecheck env) (cons exp1 exps))])
           `(has-type (vector ,@es) (Vector ,@ts)))]
        [(? symbol?)
         `(has-type ,expr ,(lookup expr env))]
        [`(function-ref ,(and s (? symbol?)))
         `(has-type (function-ref ,s) ,(lookup s env))]
        [`(void)
         `(has-type ,expr Void)]
        [`(read)
         `(has-type ,expr Integer)]
        [`(inject ,e ,fty)
         (if (is-ftype fty)
             (match-let* ([(and e^ `(has-type ,_ ,ty)) ((typecheck env) e)])
               (if (equal? ty fty)
                   `(has-type (inject ,e^ ,fty) Any)
                   (type-error fty ty e expr)))
             (ftype-error fty expr))]
        [`(project ,e ,fty)
         (if (is-ftype fty)
             (match-let* ([(and e^ `(has-type ,_ ,ty)) ((typecheck env) e)])
               (if (equal? ty `Any)
                   `(has-type (project ,e^ ,fty) ,fty)
                   (type-error `Any ty e expr)))
             (ftype-error fty expr))]
        [`(,pred ,e)
         #:when (set-member? type-predicates pred)
         (match-let* ([(and e^ `(has-type ,_ ,ty)) ((typecheck env) e)])
           (if (equal? ty `Any)
               `(has-type (,pred ,e^) Boolean)
               (type-error `Any ty e expr)))]
        [`(lambda: ,(and args `([,xs : ,ty-args] ...)) : ,ty-ret ,body)
         (match-let* ([new-env (append (map cons xs ty-args) env)]
                      [(and body^ `(has-type ,_ ,ty-body)) ((typecheck new-env) body)])
           (if (equal? ty-ret ty-body)
               `(has-type (lambda: ,args : ,ty-ret ,body^) (,@ty-args -> ,ty-ret))
               (type-error ty-ret ty-body body expr)))]
        [`(let ([,x ,e]) ,body)
         (match-let* ([(and e^ `(has-type ,_ ,t)) ((typecheck env) e)]
                      [new-env (cons (cons x t) env)]
                      [(and body^ `(has-type ,_ ,t-body)) ((typecheck new-env) body)])
           `(has-type (let ([,x ,e^]) ,body^) ,t-body))]
        [`(- ,e)
         (tc-unary-expr  `-   `Integer `Integer e env expr)]
        [`(+ ,e1 ,e2)
         (tc-binary-expr `+   `Integer `Integer e1 e2 env expr)]
        [`(not ,e)
         (tc-unary-expr  `not `Boolean `Boolean e env expr)]
        [`(and ,e1 ,e2)
         (tc-binary-expr `and `Boolean `Boolean e1 e2 env expr)]
        [`(if ,c ,t ,f)
         (match ((typecheck env) c)
           [(and c^ `(has-type ,_ Boolean))
            (match-let ([(and t^ `(has-type ,_ ,t-ty)) ((typecheck env) t)]
                        [(and f^ `(has-type ,_ ,f-ty)) ((typecheck env) f)])
              (if (equal? t-ty f-ty)
                  `(has-type (if ,c^ ,t^ ,f^) ,t-ty)
                  (type-error t-ty f-ty f expr)))]
           [actual-ty (type-error `Boolean actual-ty c expr)])]
        [`(eq? ,e1 ,e2)
         ; Bit of an odd case, since it can take
         ; two booleans or two fixnums
         (match-let ([(and e1^ `(has-type ,_ ,e1-ty)) ((typecheck env) e1)]
                     [(and e2^ `(has-type ,_ ,e2-ty)) ((typecheck env) e2)])
           (if (equal? e1-ty e2-ty)
               `(has-type (eq? ,e1^ ,e2^) Boolean)
               (error (format (unlines `("Type error:"
                                         "\tExpected:\ttwo equal types"
                                         "\tActual:\t\t~a"
                                         "\t\t\t~a"
                                         "In the subexpressions:\t~a"
                                         "\t\t\t~a"
                                         "In the expression:\t~a"))
                              e1-ty e2-ty e1 e2 expr))))]
        [`(vector-ref ,vec-exp ,ix)
         (match ((typecheck env) ix)
           [(and ix^ `(has-type ,_ ,actual-ty))
            (match actual-ty
              [`Integer
               (match ((typecheck env) vec-exp)
                 [(and vec-exp^ `(has-type ,_ ,actual-ty))
                  (match actual-ty
                    [`(Vector ,ty1 ,tys ...)
                     `(has-type (vector-ref ,vec-exp^ ,ix^) ,(list-ref (cons ty1 tys) ix))]
                    [`(Vectorof ,ty)
                     `(has-type (vector-ref ,vec-exp^ ,ix^) ,ty)]
                    [_ (type-error `(Vector ...) actual-ty vec-exp expr)])])]
              [_ (type-error `Integer actual-ty ix expr)])])]
        [`(vector-set! ,vec-exp ,ix ,new-val)
         (match ((typecheck env) ix)
           [(and ix^ `(has-type ,_ ,actual-ty))
            (match actual-ty
              [`Integer
               (match ((typecheck env) vec-exp)
                 [(and vec-exp^ `(has-type ,_ ,actual-ty))
                  (match actual-ty
                    [`(Vector ,ty1 ,tys ...)
                     (match-let ([(and new-val^ `(has-type ,_ ,new-val-ty))
                                  ((typecheck env) new-val)]
                                 [old-val-ty (list-ref (cons ty1 tys) ix)])
                       (if (equal? old-val-ty new-val-ty)
                           `(has-type (vector-set! ,vec-exp^ ,ix^ ,new-val^) Void)
                           (type-error old-val-ty new-val-ty new-val expr)))]
                    [`(Vectorof ,ty)
                     (match-let ([(and new-val^ `(has-type ,_ ,new-val-ty))
                                  ((typecheck env) new-val)])
                       (if (equal? ty new-val-ty)
                           `(has-type (vector-set! ,vec-exp^ ,ix^ ,new-val^) Void)
                           (type-error ty new-val-ty new-val expr)))]
                    [_ (type-error `(Vector ...) actual-ty vec-exp expr)])])]
              [_ (type-error `Integer actual-ty ix expr)])])]
        [`(define ,(and args (list fun `[,arg1 : ,ty1] ...)) : ,ty-ret ,body)
         (match-let ([(and body^ `(has-type ,_ ,actual-ty-ret))
                      ((typecheck (append (map cons arg1 ty1) env)) body)])
           (if (equal? ty-ret actual-ty-ret)
               `(define ,args : ,ty-ret ,body^)
               (type-error ty-ret actual-ty-ret body expr)))]
        [`(program ,defs ... ,body)
         (let* ([def-types (map extract-define-type defs)]
                [dup-name  (check-duplicates def-types #:key car)])
           (if dup-name
               (error (format "Duplicate defines for `~a`" (car dup-name)))
               (match-let ([defs^ (map (typecheck (append def-types env)) defs)]
                           [(and body^ `(has-type ,_ ,ret-ty))
                            ((typecheck (append def-types env)) body)])
                 `(program (type ,ret-ty)
                           ,@defs^
                           ,body^))))]
        [`(app ,exp-rator ,exp-rands ...)
         (match-let ([(and exp-rator^ `(has-type ,_ ,ty-rator))
                      ((typecheck env) exp-rator)]
                     [(and exp-rands^ (list `(has-type ,_ ,tys-rands) ...))
                      (map (typecheck env) exp-rands)])
           (match ty-rator
             [(list tys-rator-args ... -> ty-rator-ret)
              (if (equal? tys-rator-args tys-rands)
                  `(has-type (app ,exp-rator^ ,@exp-rands^) ,ty-rator-ret)
                  (type-error-fun-args exp-rator
                                       `(,@tys-rator-args -> ,ty-rator-ret)
                                       tys-rands
                                       expr))]
             [actual-ty (type-error `(,@tys-rands -> ...)
                                    actual-ty
                                    exp-rator
                                    expr)]))]))))

; (define ...) -> Pair Name Type
(define extract-define-type
  (match-lambda
    [`(define ,(list fun `[,arg1 : ,ty1] ...) : ,ty-ret ,body)
     (cons fun `(,@ty1 -> ,ty-ret))]))

(define num-fun-arg-types
  (match-lambda
    [(list ty1 ... -> ty-ret) (length ty1)]))

(define tc-unary-expr
  (λ (op arg-ty res-ty e env expr)
    (match ((typecheck env) e)
      [(and e^ `(has-type ,_ ,actual-ty))
       (if (equal? actual-ty arg-ty)
           `(has-type (,op ,e^) ,res-ty)
           (type-error arg-ty actual-ty e expr))])))

(define tc-binary-expr
  (λ (op arg-ty res-ty e1 e2 env expr)
    (match ((typecheck env) e1)
      [(and e1^ `(has-type ,_ ,actual-ty))
       (if (equal? actual-ty arg-ty)
           (match ((typecheck env) e2)
             [(and e2^ `(has-type ,_ ,actual-ty))
              (if (equal? actual-ty arg-ty)
                  `(has-type (,op ,e1^ ,e2^) ,res-ty)
                  (type-error arg-ty actual-ty e2 expr))])
           (type-error arg-ty actual-ty e1 expr))])))

(define ftype-error
  (λ (ty expr)
    (error (format (unlines `("Expected an ftype, but given ~a"
                              "In the expression:\t~a"))
                   ty expr))))

(define type-error
  (λ (expected-ty actual-ty subexpr expr)
    (error (format (unlines `("Type error:"
                              "\tExpected:\t~a"
                              "\tActual:\t\t~a"
                              "In the subexpression:\t~a"
                              "In the expression:\t~a"))
                   expected-ty actual-ty subexpr expr))))

(define type-error-fun-args
  (λ (fun fun-ty actual-tys expr)
    (error (format (unlines `("Type error:"
                              "\tThe function `~a` is applied to the types ~a"
                              "\tBut the type of `~a` is ~a"
                              "In the expression:\t~a"))
                   fun actual-tys fun fun-ty expr))))

(define unlines
  (λ (ls)
    (foldr (λ (s1 s2)
             (string-append (string-append s1 "\n")
                            s2))
           "" ls)))

(define typechecker (typecheck `()))
