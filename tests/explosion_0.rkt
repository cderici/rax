(define (explosion [n : Integer]) : Integer
  (explosion (+ n 1)))

(explosion 1)
