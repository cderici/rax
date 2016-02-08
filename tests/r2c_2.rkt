(if (let ([y 56])
      (eq? y
           (if (if (if (eq? 4 5)
                       (let ([x 7]) #t)
                       (and (not #f) #f))
                   #f
                   #t)
               45
               56)))
    0
    42)
