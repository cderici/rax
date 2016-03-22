(let ([v1 (vector 42)])
  (let ([g1 (vector 1)])
    (let ([g2 (vector g1)])
      (vector-ref v1 0))))
