#lang racket

(require "utilities.rkt")

(provide
 register-allocation
 (rename-out [assign-homes-old assign-homes]))


(define (register-allocation num-of-registers)
  (lambda (x86*-prog)
    ((allocate-registers num-of-registers) (build-interference (uncover-live x86*-prog)))))

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
      [(or `(,(or `addq `subq) ,_ ,d) `(negq ,d))
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


; name : symbol
; color: number
; satur: (listof color)
(struct node (name color satur))

;; just for debugging
(define (node->list n) (list (node-name n) (node-color n) (node-satur n)))

(define colored? node-color)

(define (prep vars)
  (map (lambda (var) (node var #f '())) vars))

(define (choose-max-satur nodes)
  (argmax (lambda (n) (length (node-satur n))) nodes))

(define (update-saturation nd new-color)
  (node (node-name nd) (node-color nd) (cons new-color (node-satur nd))))

;; highly inefficient (recreates the list)
;; TODO: change (listof nodes) to a hash (any mutable data structure)
(define (update-saturations var-nodes adj-node-names color updated-nodes)
  (cond
    [(empty? var-nodes) updated-nodes]
    [(set-member? adj-node-names (node-name (car var-nodes)))
     (update-saturations (cdr var-nodes) adj-node-names color
                         (cons (update-saturation (car var-nodes) color) updated-nodes))]
    [else (update-saturations (cdr var-nodes) adj-node-names color (cons (car var-nodes) updated-nodes))]))

;; choose-color : Symbol (listof nodes) (listof color) Graph -> color (number)
(define (choose-color nodeName var-nodes saturation move-graph)
  (let* ([maxSatur (apply max (if (empty? saturation) '(0) saturation))]
         [candidates (range 0 (+ 2 maxSatur))]
         [chooseFrom (remq* saturation candidates)]
         
         [move-related-node-names (adjacent move-graph nodeName)]
         [move-related-node-colors (foldr (lambda (nd colors)
                                            (if (and (colored? nd)
                                                     (set-member? move-related-node-names (node-name nd)))
                                                (cons (node-color nd) colors)
                                                colors))
                                          '() var-nodes)]
         )
    (if (empty? move-related-node-colors)
        (apply min chooseFrom)
        (car move-related-node-colors))
    ))

;; graph-coloring : Graph (listof node) Graph <accummulator> : (listof <colored>node)
;; greedy coloring of the nodes in the given graph using saturation info (most-constrained-first heuristic)
;; produces -> list of node (colored)
(define (graph-coloring inter-graph var-nodes move-graph mapping)
  (cond
    [(empty? var-nodes) mapping]
    [else (let* ([maxSaturatedNode (choose-max-satur var-nodes)]
                 [maxNodeName (node-name maxSaturatedNode)]
                 [maxNodeSatur (node-satur maxSaturatedNode)]
                 [nodeColor (choose-color maxNodeName var-nodes maxNodeSatur move-graph)]
                 
                 [newVars (remf (lambda (node) (symbol=? maxNodeName (node-name node))) var-nodes)]
                 [updatedVars (update-saturations newVars (adjacent inter-graph maxNodeName) nodeColor '())]
                 )
            (graph-coloring inter-graph updatedVars move-graph (cons (node maxNodeName nodeColor maxNodeSatur) mapping)))]))

;; find-homes-to-colors
;; given the graph and number of registers to use, produces 3 things
;; produces howmany stack slots needed AND list of colored nodes AND an association list of (<color> . <register/stackLocation>)
;; exmpl output-> (values (listof <colored>node) '((0 . rdx) (1 . -8) (2 . -16)))
(define (find-homes-to-colors inter-graph var-nodes move-graph num-of-registers)
  (let* ([color-map (graph-coloring inter-graph var-nodes move-graph '())]
         [numColors (if (empty? color-map) 0 (add1 (node-color (argmax node-color color-map))))]
         [colors (range 0 numColors)]
         
         ;; just to have the kinds of registers in hand
         [dont-touch-regs '(rsp rbp rax)]
         [caller-save-regs '(rax rdx rcx rsi rdi r8 r9 r10 r11)]
         [callee-save-regs '(rsp rbp rbx r12 r13 r14 r15)]
         [all-registers (append caller-save-regs callee-save-regs)]
         ;; disregarding caller/callee saveness
         [usable-regs (take (remq* dont-touch-regs all-registers) num-of-registers)]
         
         [numUsableRegs (length usable-regs)])
    
    (if (<= numColors numUsableRegs)
        ;; case-> the usable registers are enough to hold our variables
        (values 0 color-map (map cons colors (take usable-regs numColors)))
        ;; case-> we need some stack vars
        (let-values ([(regColors stackColors) (split-at colors numUsableRegs)])
          (values
           (- numColors numUsableRegs)
           color-map
           (append (map cons regColors (take usable-regs numUsableRegs))
                   (map cons stackColors (build-list (- numColors numUsableRegs) (lambda (x) (* (add1 x) -8))))))))))

;; varToLocStmnt
(define (varToLocStmnt nodes-colors color-location)
  (lambda (var-expr)
    (match var-expr
      [`(var ,varID)
       (let* ([color-of-node* (assv varID nodes-colors)]
              [color-of-node (if (not color-of-node*) (error 'varToLocStmnt "we have an unmapped node!!!!") (cdr color-of-node*))]
              [home-of-node* (assv color-of-node color-location)]
              [home-of-node (if (not home-of-node*) (error 'varToLocStmnt "we have an unmapped color!!!") (cdr home-of-node*))])
         (if (symbol? home-of-node)
             ;; it's a register
             `(reg ,home-of-node)
             (if (number? home-of-node)
                 ;; then it's a stack position
                 `(stack ,home-of-node)
                 (error 'varToLocStmnt "what the heck! we have a location that's neither reg, nor stack pos!"))))]
      [else var-expr] ;; var-expr can also be a (reg ...) expr (rax from a (read) etc.)
      )))


(define (assign-homes inter-graph var-nodes instructions move-graph num-of-registers)
  (let-values ([(num-of-stack-slots color-map color-homes) (find-homes-to-colors inter-graph var-nodes move-graph num-of-registers)])
    (let ([vars-colors (map (lambda (node) (cons (node-name node) (node-color node))) color-map)])
      (values num-of-stack-slots
              (match-lambda
                [`(,bin-instr ,arg1 ,arg2) `(,bin-instr ,((varToLocStmnt vars-colors color-homes) arg1)
                                                        ,((varToLocStmnt vars-colors color-homes) arg2))]
                [`(,unary-instr ,arg) `(,unary-instr ,((varToLocStmnt vars-colors color-homes) arg))]
                [else (error 'assign-homes "we have an expression that's netiher binary nor unary!")])))))

(define (construct-move-graph! instructions graph)
  (cond
    ((empty? instructions) graph)
    (else (match (car instructions)
            [`(movq (var ,v1) (var ,v2)) (begin
                                           (add-edge graph v1 v2)
                                           (construct-move-graph! (cdr instructions) graph))]
            [else (construct-move-graph! (cdr instructions) graph)]))))

(define allocate-registers
  (lambda (numOfRegs)
    (match-lambda
      [`(program (,formals ... ,graph) ,instructions ...)
       (let* ([var-nodes (prep formals)]
              [move-graph (construct-move-graph! instructions (make-graph formals))])
         (let-values ([(num-of-stack-slots mapping-function)
                       (assign-homes graph var-nodes instructions move-graph numOfRegs)])
           `(program ,(* 16 (ceiling (/ num-of-stack-slots 2)))
                     ,@(map mapping-function instructions))))])))

;(define vars '(v w x  rax  y z))
(define vars '(v w x y z))

(define eGraph (make-graph vars))
(add-edge eGraph 'v 'w)
(add-edge eGraph 'w 'x)
(add-edge eGraph 'y 'w)
(add-edge eGraph 'z 'w)
(add-edge eGraph 'y 'z)
(add-edge eGraph 'x 'y)
;(add-edge eGraph 'y 'rax)


(define exampleProg
  `(program (v w x y z ,eGraph)
            (movq (int 1) (var v))
            (movq (int 46) (var w))
            (movq (var v) (var x))
            (addq (int 7) (var x))
            (movq (var x) (var y))
            (addq (int 4) (var y))
            (movq (var x) (var z))
            (addq (var w) (var z))
            (movq (var z) (reg rax))
            (subq (var y) (reg rax))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; A1 STUFF
(define (varToStackPos expression listHomes)
  (match expression
    [`(var ,varID) (let ((stackPos (assv varID listHomes)))
                     `(stack ,(cdr stackPos)))]
    [else expression]))

;; x86* -> x86*
(define assign-homes-old
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
           `(program ,frame-size ,@(map (assign-homes-old homes) instructions)))]))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; A1 STUFF
