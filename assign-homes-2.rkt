#lang racket

(require "utilities.rkt")

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

; x86* -> x86*
(define uncover-live
  (match-lambda
    [`(program (,vars ...) ,instrs ...)
     (let
         ([live-afters
           (drop (foldr
                  uncover-live-help
                  `(,(set))
                  ; ^ We're a bit dishonest here in that we're matching up instruction
                  ; k with live-after set k-1 (since this empty set we pass is
                  ; live-after set k). But that's okay, we'll just end up creating one
                  ; extra live-after set which is guaranteed to be empty, so we drop it.
                  instrs) 1)])
       `(program (,@vars ,live-afters) ,@instrs))]))

; Instruction -> Set Variable -> Set Variable
(define uncover-live-help
  (lambda (instr-k+1 live-after-set)
    (match live-after-set
      [(list-rest live-after-k+1 live-after-rest)
       (let* ([live-before-k+1
               ; L_before(k+1) = (L_after(k+1) - W(k+1)) U R(k + 1)
               (set-union (set-subtract live-after-k+1
                                        (written-variables instr-k+1))
                          (read-variables instr-k+1))]
              [live-after-k live-before-k+1])
         (cons live-after-k live-after-set))])))

; Instruction -> Set Variable
(define read-variables
  (match-lambda
    [`(,(or `addq `subq) ,arg1 ,arg2)
     (set-union (variable arg1)
                (variable arg2))]
    [`(,movq ,arg1 ,_) (variable arg1)]
    [_                 (set)]))

; Instruction -> Set Variable
(define written-variables
  (match-lambda
    [`(,op ,_ ,arg2) (variable arg2)]
    [_               (set)]))

; Arg -> Set Variable
(define variable
  (match-lambda
    [`(,(or `var `reg) ,name) (set name)]
    [`(int ,_)                (set)]))

; Arg -> (Int | Symbol) [not-particularly well-typed]
(define arg-payload
  (match-lambda
    [`(,_ ,payload) payload]))

; x86* -> x86*
(define build-interference
  (match-lambda
    [`(program (,vars ... ,live-afters) ,instrs ...)
     (let* ([graph (foldl (curry add-edge-interference)
                          (make-graph vars)
                          instrs
                          live-afters)])
       `(program (,@vars ,graph) ,@instrs))]))

; Instruction -> Set Variable -> Graph -> Graph
(define add-edge-interference
  (lambda (instr live-after-set graph)
    (match instr
      [`(movq ,s ,d)
       (let [(s-pl (arg-payload s))
             (d-pl (arg-payload d))]
         (sequence-fold
          (λ (gr v)
            (if (or (eqv? v s-pl) (eqv? v d-pl))
                gr
                (begin
                  (add-edge gr d-pl v)
                  gr)))
          graph
          live-after-set))]
      [`(,(or `addq `subq) ,_ ,d)
       (let [(d-pl (arg-payload d))]
         (sequence-fold
          (λ (gr v)
            (if (eqv? v d-pl)
                gr
                (begin
                  (add-edge gr d-pl v)
                  gr)))
          graph
          live-after-set))]
      [`(callq ,label)
       (sequence-fold
        (λ (gr v)
          (sequence-fold
           (λ (gr^ r)
             (begin
               (add-edge gr^ r v)
               gr^))
           gr
           callee-save))
        graph
        live-after-set)])))