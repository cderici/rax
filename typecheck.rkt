#lang racket

(provide typechecker)

(require "utilities.rkt")

; R3 -> Type
(define typecheck
  (λ (env)
    (λ (expr)
      (match expr
        [(? fixnum?)  `Integer]
        [(? boolean?) `Boolean]
        [`(vector ,exp1 ,exps ...)
         (let ([ts (map (typecheck env) (cons exp1 exps))])
           `(Vector ,@ts))]
        [(? symbol?)  (lookup expr env)]
        [`(void)      `Void]
        [`(read)      `Integer]
        [`(let ([,x ,e]) ,body)
         (let* ([t ((typecheck env) e)]
                [new-env (cons (cons x t) env)])
           ((typecheck new-env) body))]
        [`(- ,e)
         (tc-unary-expr `Integer `Integer e env expr)]
        [`(+ ,e1 ,e2)
         (tc-binary-expr `Integer `Integer e1 e2 env expr)]
        [`(not ,e)
         (tc-unary-expr `Boolean `Boolean e env expr)]
        [`(and ,e1 ,e2)
         (tc-binary-expr `Boolean `Boolean e1 e2 env expr)]
        [`(if ,c ,t ,f)
         (match ((typecheck env) c)
           [`Boolean
            (let ([t-ty ((typecheck env) t)]
                  [f-ty ((typecheck env) f)])
              (if (equal? t-ty f-ty)
                  t-ty
                  (type-error t-ty f-ty f expr)))]
           [actual-ty (type-error `Boolean actual-ty c expr)])]
        [`(eq? ,e1 ,e2)
         ; Bit of an odd case, since it can take
         ; two booleans or two fixnums
         (let ([e1-ty ((typecheck env) e1)]
               [e2-ty ((typecheck env) e2)])
           (if (equal? e1-ty e2-ty)
               `Boolean
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
           [`Integer
            (match ((typecheck env) vec-exp)
              [`(Vector ,ty1 ,tys ...)
               (list-ref (cons ty1 tys) ix)]
              [actual-ty (type-error `(Vector ...) actual-ty vec-exp expr)])]
           [actual-ty (type-error `Integer actual-ty ix expr)])]
        [`(vector-set! ,vec-exp ,ix ,new-val)
         (match ((typecheck env) ix)
           [`Integer
            (match ((typecheck env) vec-exp)
              [`(Vector ,ty1 ,tys ...)
               (let ([new-val-ty ((typecheck env) new-val)]
                     [old-val-ty (list-ref (cons ty1 tys) ix)])
                 (if (equal? old-val-ty new-val-ty)
                     `Void
                     (type-error old-val-ty new-val-ty new-val expr)))]
              [actual-ty (type-error `(Vector ...) actual-ty vec-exp expr)])]
           [actual-ty (type-error `Integer actual-ty ix expr)])]
        [`(program ,body)
         `(program (type ,((typecheck `()) body))
                   ,body)]
        [`(program ,defs ... ,body)
         `(program (type ,((typecheck (map extract-define-type defs)) body))
                   ,@defs
                   ,body)]
        [`(,exp-rator ,exp-rands ...)
         (let ([ty-rator  ((typecheck env) exp-rator)]
               [tys-rands (map (typecheck env) exp-rands)])
           (match ty-rator
             [(list tys-rator-args ... -> ty-rator-ret)
              (if (equal? tys-rator-args tys-rands)
                  ty-rator-ret
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
  (λ (arg-ty res-ty e env expr)
    (match ((typecheck env) e)
      [(== arg-ty) res-ty]
      [actual-ty (type-error arg-ty actual-ty e expr)])))

(define tc-binary-expr
  (λ (arg-ty res-ty e1 e2 env expr)
    (match ((typecheck env) e1)
      [(== arg-ty)
       (match ((typecheck env) e2)
         [(== arg-ty) res-ty]
         [actual-ty (type-error arg-ty actual-ty e2 expr)])]
      [actual-ty (type-error arg-ty actual-ty e1 expr)])))

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