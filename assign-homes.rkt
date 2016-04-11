#lang racket

(require "utilities.rkt")

(provide
 prep
 construct-move-graph!
 find-homes-to-colors
 node->list

 build-interference
 uncover-live
 allocate-registers
 written-callee-save-regs
 dont-touch-reg-set
 (rename-out [assign-homes assign-homes-new])
 register-allocation
 (rename-out [assign-homes-old assign-homes]))

(define our-caller-save (set-remove caller-save 'r11))
(define our-callee-save callee-save)

(define dont-touch-reg-set (set `rsp `rbp `rax))
(define touchable-reg-list (append (reverse (set->list our-caller-save)) (reverse (set->list our-callee-save))))

;; x86* -> x86*
(define (register-allocation num-of-registers)
  (lambda (x86*-prog)
    ((allocate-registers num-of-registers) (build-interference (uncover-live x86*-prog)))))

(define (top-defs-liveness defs new-defs)
  (cond
    ((empty? defs) (reverse new-defs))
    (else
     (let ([new-def (match (car defs)
                      [`(define (,f) ,num-vars (,vars ,maxStack) ,instrs ...)
                       (let-values ([(live-afters new-instrs last-before-dummy)
                                     (compute-liveness-sets (reverse instrs) (set) '() '())])
                         `(define (,f) ,num-vars ((,@vars ,live-afters) ,maxStack) ,@new-instrs))])])
       (top-defs-liveness (cdr defs)
                          (cons new-def new-defs))))))

(define uncover-live
  (match-lambda
    [`(program ((,vars ...) ,maxStack) (type ,t) (defines ,defn ...) ,instrs ...)
     (let-values
         ([(live-afters new-instrs last-before-ignore)
           ;; new-instrs are in correct order (by tail recursion)
           (compute-liveness-sets (reverse instrs) (set) '() '())])
       (let ([new-defs (top-defs-liveness defn '())])
         `(program ((,@vars ,live-afters) ,maxStack) (type ,t) (defines ,@new-defs) ,@new-instrs)))]))

;; instrs are given reversed
(define (compute-liveness-sets instrs live-before-k+1 live-afters new-instrs)
  (cond
    ((empty? instrs) (values live-afters new-instrs live-before-k+1))
    (else
     (let* (;; the live-after-k (current live after) is
            ;; the live-before-k+1 (previous live before)
            [live-after-k live-before-k+1])
       (let-values ([(live-before-k new-instr)
                     (compute-live-before-k (car instrs) live-after-k)])
         (compute-liveness-sets (cdr instrs)
                                live-before-k
                                (cons live-after-k live-afters)
                                (cons new-instr new-instrs)))))))

;; compute the current live-before, given the current live-after (= live-before-k+1)
(define (compute-live-before-k instr-k live-after-k)
  (match instr-k
    [`(if (eq? ,e1 ,e2) ,thns ,elss)
     (let-values
         ([(live-afters-thns new-thns live-before-thns)
           (compute-liveness-sets (reverse thns) live-after-k '() '())]
          [(live-afters-elss new-elss live-before-elss)
           (compute-liveness-sets (reverse elss) live-after-k '() '())])
       ;; L_before(k) = L_thns_before U L_elss_before U Vars(e1) U Vars (e2)
       (values (set-union live-before-thns live-before-elss
                          (variable e1) (variable e2))
               `(if (eq? ,e1 ,e2)
                    ,new-thns ,live-afters-thns ,new-elss ,live-afters-elss)))]
    [`(indirect-callq ,arg)
     (values (set-union (set-subtract live-after-k (written-variables instr-k))
                        (read-variables instr-k)
                        ;; adding caller-save regs to the live afters so they interfere with everything above
                        ;; so nothing will be written on them
                        ;; so no need for caller to save them
                        our-caller-save)

             instr-k)]
    [else
     ; L_before(k) = (L_after(k) - W(k)) U R(k)
     (values (set-union (set-subtract live-after-k (written-variables instr-k))
                        (read-variables instr-k))
             instr-k)]))


; Instruction -> Set Variable
(define read-variables
  (match-lambda
    [`(,(or `addq `subq) ,arg1 ,arg2)
     (set-union (variable arg1)
                (variable arg2))]
    [(or `(movq ,arg1 (offset ,arg2 ,n)) `(movq (offset ,arg1 ,n) ,arg2)) (set-union (variable arg1) (variable arg2))]
    [`(movq ,arg1 ,_) (variable arg1)]
    [`(indirect-callq ,arg) (variable arg)]
    [_                 (set)]))

; Instruction -> Set Variable
(define written-variables
  (match-lambda
    [`(,op ,_ ,arg2) (variable arg2)]
    [_               (set)]))

; Instruction -> Set Symbol
(define written-regs
  (match-lambda
    [`(if ,_ ,thns ,elss)
     (let ([worker (lambda (x y) (set-union (false->empty x) y))])
       (set-union (foldr worker (set) (map written-regs thns))
                  (foldr worker (set) (map written-regs elss))))]
    [`(,op ,_ (reg ,r)) (set r)]
    [_                  #f]))

(define false->empty
  (lambda (x)
    (if x x (set))))

; Arg -> Set Variable
(define variable
  (match-lambda
    [`(,(or `var `reg) ,name) (set name)]
    [`(offset ,var ,n) (variable var)]
    [(or `(byte-reg ,_)
         `(global-value ,_)
         `(int ,_)
         `(stack ,_)
         `(stack-arg ,_)) (set)]))

; Arg -> (Int | Symbol) [not-particularly well-typed]
(define arg-payload
  (match-lambda
    [`(offset (,(or `var `reg) ,payload) ,_) payload]
    [`(,_ ,payload) payload]))

; x86* -> x86*
(define build-interference
  (match-lambda
    [`(define (,f) ,num-vars ((,vars ... ,live-afters) ,maxStack) ,instrs ...)
     (let* ([graph (foldl (curry add-edge-interference)
                          (make-graph vars)
                          instrs
                          live-afters)])
       `(define (,f) ,num-vars ((,@vars ,graph) ,maxStack) ,@instrs))]
    [`(program ((,vars ... ,live-afters) ,maxStack) (type ,t) (defines ,defn ...) ,instrs ...)
     (let* ([new-defs (map build-interference defn)]
            [graph (foldl (curry add-edge-interference)
                          (make-graph vars)
                          instrs
                          live-afters)])
       `(program ((,@vars ,graph) ,maxStack) (type ,t) (defines ,@new-defs) ,@instrs))]))

; Instruction -> Set Variable -> Graph -> Graph
(define add-edge-interference
  (lambda (instr live-after-set graph)
    (match instr
      [(or `(leaq ,s ,d) `(movq ,s ,d) `(movzbq ,s ,d) `(xorq ,s ,d)
           `(sarq ,s ,d) `(salq ,s ,d) `(orq ,s ,d) `(andq ,s ,d))
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
      [`(cmpq ,arg1 ,arg2) graph]
      ;; since we're not writing anything
      [`(,setter (byte-reg al))
       #:when (memv setter '(sete setl setle setg setge)) graph]
      #;[`(sete (byte-reg al)) graph]
      #;[`(setl (byte-reg al)) graph]
      [`(if (eq? ,e1 ,e2) ,thns ,thn-lives ,elss ,els-lives)
       (foldl (curry add-edge-interference)
              (foldl (curry add-edge-interference)
                     graph elss els-lives)
              thns thn-lives)]
      [`(indirect-callq ,arg)
       (let ([arg-pl (arg-payload arg)])
         (sequence-fold
          (λ (gr v)
            (if (eqv? arg-pl v)
                gr
                (begin
                  (add-edge gr arg-pl v)
                  gr)))
          graph
          live-after-set))]
      [`(callq ,label)
       (sequence-fold
        (λ (gr v)
          (sequence-fold
           (λ (gr^ r)
             (if (eqv? r v)
                 gr^
                 (begin
                   (add-edge gr^ r v)
                   gr^)))
           gr
           our-caller-save))
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

(define (pick-a-reg adj-set usable-regs)
  (if (empty? usable-regs)
      false
      (let ([picked-reg (car usable-regs)])
        (if (set-member? adj-set picked-reg)
            (pick-a-reg adj-set (cdr usable-regs)) ; pick again
            picked-reg);; found
        )))



;; produce -> (values color-to-loc-mapping current-usable-regs howmany-stack-locs)
(define (map-colors-to-locations colors colors-names inter-graph all-registers numUsableRegs outVals)
  (let* ((current-map (car outVals)) ;; ((0 . rdx) (1 . -8) (2 . -16)))
         (current-usable-regs (cadr outVals)) ;; list of symbols (registers)
         (current-stack-loc (caddr outVals))) ;; negative number
    (flush-output)
    (cond
      ((empty? colors) outVals)
      ((<= numUsableRegs 0)
       (map-colors-to-locations (cdr colors) colors-names inter-graph all-registers numUsableRegs
                                (list (cons `(,(car colors) . ,(* (+ 1 current-stack-loc) -8)) current-map)
                                      current-usable-regs
                                      (add1 current-stack-loc))))
      (else
       (let* ([c-color (car colors)]
              [var-names-has-c-color  (map cdr (filter (lambda (c-n)
                                                         (= c-color (car c-n))) colors-names))]
              [adj-sets (map (lambda (var-name) (adjacent inter-graph var-name)) var-names-has-c-color)]
              [union-list-of-adjs (foldr (lambda (adjs union)
                                           (set-union adjs union))
                                         (set)
                                         adj-sets)]
              #;[varname (begin (display colors-names)(newline)
                                (cdr (assv c-color colors-names)))]
              #;[adj (adjacent inter-graph varname)]
              [picked-reg (pick-a-reg union-list-of-adjs current-usable-regs)]
              )
         (if (not picked-reg) ; pick-a-reg signaled that we cannot find a register for that color
             ; so we're assigning a stack position for it and continue
             (map-colors-to-locations (cdr colors) colors-names inter-graph all-registers numUsableRegs
                                      (list (cons `(,c-color . ,(* (+ 1 current-stack-loc) -8)) current-map)
                                            current-usable-regs
                                            (add1 current-stack-loc)))
             ; we have a picked-reg, put it and continue
             (map-colors-to-locations (cdr colors) colors-names inter-graph all-registers (sub1 numUsableRegs)
                                      (list (cons `(,c-color . ,picked-reg) current-map)
                                            (remv picked-reg current-usable-regs)
                                            current-stack-loc))))))))

;; find-homes-to-colors
;; given the graph and number of registers to use, produces 3 things
;; produces howmany stack slots needed AND list of colored nodes AND an association list of (<color> . <register/stackLocation>)
;; exmpl output-> (values 0 (listof <colored>node) '((0 . rdx) (1 . -8) (2 . -16)))
(define (find-homes-to-colors inter-graph var-nodes move-graph num-of-registers)
  (let* ([colored-node-list (graph-coloring inter-graph var-nodes move-graph '())]
         [colors-names (map (lambda (nd) (cons (node-color nd) (node-name nd))) colored-node-list)]

         [numColors (if (empty? colored-node-list) 0 (add1 (node-color (argmax node-color colored-node-list))))]
         [colors (range 0 numColors)]

         [all-registers touchable-reg-list]

         [numUsableRegs (if (> num-of-registers (length all-registers))
                            (length all-registers)
                            num-of-registers)]
         )
    (let* ([mapResults (map-colors-to-locations colors colors-names inter-graph all-registers numUsableRegs
                                                (list '() all-registers 0))]
           [color-to-loc-mapping (car mapResults)]
           [current-usable-reg-dummy (cadr mapResults)]
           [howmany-stack-locs (caddr mapResults)]
           )
      (values
       color-to-loc-mapping
       colored-node-list
       howmany-stack-locs
       ))))

;; varToLocStmnt
;; REFACTOR
(define (varToLocStmnt nodes-colors color-location)
  (lambda (var-expr)
    (match var-expr
      [`(var ,varID)
       (let* ([color-of-node* (assv varID nodes-colors)]
              [color-of-node (if (not color-of-node*) (error 'varToLocStmnt (string-append
                                                                             "we have an unmapped node --> "
                                                                             (symbol->string varID)))
                                 (cdr color-of-node*))]
              [home-of-node* (assv color-of-node color-location)]
              [home-of-node (if (not home-of-node*) (error 'varToLocStmnt "we have an unmapped color!!!") (cdr home-of-node*))])
         (if (symbol? home-of-node)
             ;; it's a register
             `(reg ,home-of-node)
             (if (number? home-of-node)
                 ;; then it's a stack position
                 `(stack ,home-of-node)
                 (error 'varToLocStmnt "what the heck! we have a location that's neither reg, nor stack pos!"))))]
      [`(offset (var ,varID) ,n)
       (let* ([color-of-node* (assv varID nodes-colors)]
              [color-of-node (if (not color-of-node*) (error 'varToLocStmnt (string-append
                                                                             "we have an unmapped node --> "
                                                                             (symbol->string varID)))
                                 (cdr color-of-node*))]
              [home-of-node* (assv color-of-node color-location)]
              [home-of-node (if (not home-of-node*) (error 'varToLocStmnt "we have an unmapped color!!!") (cdr home-of-node*))])
         `(offset ,(if (symbol? home-of-node)
                       `(reg ,home-of-node)
                       (if (number? home-of-node)
                           `(stack ,home-of-node)
                           (error 'varToLocStmnt "you have couple of hours of debugging, good luck pal!"))) ,n))]
      [else var-expr] ;; var-expr can also be a (reg ...) expr (rax from a (read) etc.)
      )))


(define (assign-homes inter-graph var-nodes move-graph num-of-registers)
  (let-values ([(color-homes color-map num-of-stack-slots)
                (find-homes-to-colors inter-graph var-nodes move-graph num-of-registers)])
    (let ([vars-colors (map (lambda (node) (cons (node-name node) (node-color node))) color-map)])
      (values num-of-stack-slots
              (match-lambda
                [`(if (eq? ,arg1 ,arg2) ,thns ,thn-lives ,elss ,els-lives)
                 (let*-values ([(num-stack-dummy mapping-func)
                                (assign-homes inter-graph var-nodes move-graph num-of-registers)]
                               [(new-thns) (map mapping-func thns)]
                               [(new-elss) (map mapping-func elss)])
                   `(if (eq? ,((varToLocStmnt vars-colors color-homes) arg1)
                             ,((varToLocStmnt vars-colors color-homes) arg2))
                        ,new-thns
                        ,new-elss))]
                [`(,bin-instr ,arg1 ,arg2) `(,bin-instr ,((varToLocStmnt vars-colors color-homes) arg1)
                                                        ,((varToLocStmnt vars-colors color-homes) arg2))]
                [`(,unary-instr ,arg) `(,unary-instr ,((varToLocStmnt vars-colors color-homes) arg))]
                [else (error 'assign-homes "we have an expression that's netiher binary nor unary!")])))))

(define (construct-move-graph! instructions graph)
  (cond
    ((empty? instructions) graph)
    (else (match (car instructions)
            [`(movq (var ,v1) (var ,v2))
             (begin
               (add-edge graph v1 v2)
               (construct-move-graph! (cdr instructions) graph))]
            [else (construct-move-graph! (cdr instructions) graph)]))))

(define allocate-registers
  (lambda (numOfRegs)
    (flush-output)
    (match-lambda
      [`(define (,f) ,num-vars ((,vars ... ,graph) ,maxStack) ,instrs ...)
       (let* ([var-nodes (prep vars)]
              [move-graph (construct-move-graph! instrs (make-graph vars))])
         (let*-values ([(num-of-stack-slots mapping-function)
                        (assign-homes graph var-nodes move-graph numOfRegs)]
                       [(new-instrs) (map mapping-function instrs)]
                       [(wcsr) (written-callee-save-regs new-instrs)]
                       [(num-of-stack-slots^) (+ num-of-stack-slots (length wcsr) maxStack)])
           `(define (,f) ,(* 16 (ceiling (/ num-of-stack-slots^ 2))) ,@new-instrs)))]
      [`(program ((,formals ... ,graph) ,maxStack) (type ,t) (defines ,defn ...) ,instructions ...)
       (let* ([var-nodes (prep formals)]
              [move-graph (construct-move-graph! instructions (make-graph formals))]
              [new-defs (map (allocate-registers numOfRegs) defn)])
         (let*-values ([(num-of-stack-slots mapping-function)
                        (assign-homes graph var-nodes move-graph numOfRegs)]
                       [(new-instrs) (map mapping-function instructions)]
                       [(wcsr) (written-callee-save-regs new-instrs)]
                       [(num-of-stack-slots^)
                        (+ num-of-stack-slots (length wcsr) maxStack)])
           `(program ,(* 16 (ceiling (/ num-of-stack-slots^ 2)))
                     (type ,t)
                     (defines ,@new-defs)
                     ,@new-instrs)))])))

(define written-callee-save-regs
  (λ (instrs)
    (remove-duplicates
     (filter (curry set-member? our-callee-save)
             (set->list
              (foldr set-union (set)
                     (map written-regs
                          (filter written-regs instrs))))))))

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
            (type Integer)
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
        [`(program (,vars ...) (type ,t) ,instructions ...)
         (let ((frame-size (* 16 (ceiling (/ (length vars) 2))))
               ;; every-one's on the stack!
               (homes (map cons vars (build-list (length vars) (lambda (x) (* (add1 x) -8))))))
           `(program ,frame-size (type ,t) ,@(map (assign-homes-old homes) instructions)))]))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; A1 STUFF
