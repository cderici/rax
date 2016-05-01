(define (ackermann-cps [cont : (Integer -> Integer)]
                       [m    : Integer]
                       [n    : Integer]) : Integer
  (if (eq? m 0)
      (cont (+ n 1))
      (if (eq? n 0)
          (ackermann-cps cont (+ m (- 1)) 1)
          (ackermann-cps
            (lambda: ([x : Integer]) : Integer
              (ackermann-cps cont
                            (+ m (- 1)) x))
            m (+ n (- 1))))))

(define (ackermann [m : Integer]
                   [n : Integer]) : Integer
  (ackermann-cps (lambda: ([x : Integer]) : Integer x) m n))

(ackermann 3 5)
