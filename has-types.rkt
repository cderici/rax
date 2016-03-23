#lang racket

(provide strip-has-types)

(define strip-has-types
  (λ (e)
    (match e
      [`(program ,vars (type ,t) (defines ,defs ...) (initialize ,s ,h) ,assignments ... (return ,final-e))
       (let ([new-defines     (map strip-has-types defs)]
             [new-assignments (map strip-has-types assignments)]
             [new-final-e     (strip-has-types final-e)])
         `(program ,vars (type ,t) (defines ,@new-defines) (initialize ,s ,h) ,@new-assignments (return ,new-final-e)))]
      [`(define (,f ,arg-types ...) : ,t ,local-vars ,body ...)
       `(define (,f ,@arg-types) : ,t ,local-vars ,@(map strip-has-types body))]
      [`(assign ,var (has-type ,e ,t))
       `(assign ,var ,(strip-has-types e))]
      [`(has-type (if (has-type (eq? ,e1 ,e2) Boolean)
                      ,thns ,elss) ,t)
       `(if (eq? ,(strip-has-types e1) ,(strip-has-types e2))
            ,(map strip-has-types thns)
            ,(map strip-has-types elss))]
      
      ; RGS: I don't think this case is strictly necessary, but
      ; I'll keep it as a sanity check
      [`(return (has-type ,e ,t))
       `(return ,(strip-has-types e))]
      
      [`(has-type (,op ,args ...) ,t)
       `(,op ,@(map strip-has-types args))]
      
      [`(has-type ,n ,t) (strip-has-types n)]
      
      [`(,op ,args ...)
       `(,op ,@(map strip-has-types args))]
      
      [else e])))