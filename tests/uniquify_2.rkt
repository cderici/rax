(+ (let ([y 15])
     (+ (let ([y (read)]) y)
        (let ([y y]) y)))
   (read))