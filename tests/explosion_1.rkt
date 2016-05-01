(define (make-your-cpu-get-hot [x : Integer]) : Integer
  (if (eq? 0 x) 42 (make-your-cpu-get-hot (+ x (- 1)))))
(let ([a-little-warmer (lambda: () : Integer (make-your-cpu-get-hot 100000))])
  (let ([a (a-little-warmer)])
  (let ([b (a-little-warmer)])
  (let ([c (a-little-warmer)])
    (a-little-warmer)))))
