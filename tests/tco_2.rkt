(define (foo [f : (Integer -> Integer)]) : Integer
  (f 42))

(define (id [x : Integer]) : Integer
  x)

(foo id)
