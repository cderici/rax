(define (FUNC [v : (Vector Integer)][y : Integer]) : Void
  (vector-set! (vector (vector-ref (vector (vector-ref v 0)))) 0 y))

(FUNC (vector 1) 3)
