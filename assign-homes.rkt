#lang racket

(provide assign-homes)

(define (varToStackPos expression listHomes)
  (match expression
    [`(var ,varID) (let ((stackPos (assv varID listHomes)))
                     `(stack ,(cdr stackPos)))]
    [else expression]))

;; x86* -> x86*
(define assign-homes
  (lambda (listHomes)
    (lambda (x86-e)
      (match x86-e
        [`(,bin-instr ,arg1 ,arg2) `(,bin-instr ,(varToStackPos arg1 listHomes)
                                                ,(varToStackPos arg2 listHomes))]
        [`(,unary-instr ,arg) `(,unary-instr ,(varToStackPos arg listHomes))]
        [`(program (,vars ...)  ,instructions ...)
         (let ((frame-size (* 16 (ceiling (/ (length vars) 2))))
               ;; every-one's on the stack!
               (homes (map cons vars (build-list (length vars) (lambda (x) (* (add1 x) -8))))))
           `(program ,frame-size ,@(map (assign-homes homes) instructions)))]))))
