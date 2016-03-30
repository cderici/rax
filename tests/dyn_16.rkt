(let ([v (vector #t)])
  (let ([wat (vector-set! v 0 42)])
    (vector-ref v 0)))
