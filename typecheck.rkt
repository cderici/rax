#lang racket

(provide typechecker)

(require "utilities.rkt")

(define typecheck
  (λ (env)
    (λ (expr)
      (match expr
        [(? fixnum?)  `Integer]
        [(? boolean?) `Boolean]
        [(? symbol?)  (lookup expr env)]
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
              (if (eqv? t-ty f-ty)
                  t-ty
                  (type-error t-ty f-ty f expr)))]
           [actual-ty (type-error `Boolean actual-ty c expr)])]
        [`(eq? ,e1 ,e2)
         ; Bit of an odd case, since it can take
         ; two booleans or two fixnums
         (let ([e1-ty ((typecheck env) e1)]
               [e2-ty ((typecheck env) e2)])
           (if (eqv? e1-ty e2-ty)
               (match e1-ty
                 ; I'm not sure if eq? will be extended in the future to
                 ; support more things than Boolean or Integer, but for
                 ; now, we'll just hardcode the possible types
                 [(or `Boolean `Integer) `Boolean]
                 [_ (type-error `Boolean e1-ty e1 expr)])
               (error (format (unlines `("Type error:"
                                         "\tExpected:\teither two Booleans or two Integers"
                                         "\tActual:\t\t~a"
                                         "\t\t\t~a"
                                         "In the subexpressions:\t~a"
                                         "\t\t\t~a"
                                         "In the expression:\t~a"))
                              e1-ty e2-ty e1 e2 expr))))]
        [`(program ,body)
         (begin
           ((typecheck `()) body) ; Make sure everything is well typed...
           expr)]                  ; ...then proceed as normal
        ))))

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

(define unlines
  (λ (ls)
    (foldr (λ (s1 s2)
             (string-append (string-append s1 "\n")
                            s2))
           "" ls)))

(define typechecker (typecheck `()))