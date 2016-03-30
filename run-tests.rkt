#lang racket

(require "compiler.rkt" "testing.rkt")

(define pass r7-passes)

(command-line

 #:args test-files ;; <- a list (because we may not get any input)
 (if (null? test-files)
     (all-tests pass)
     (let ([test-file (car test-files)])
       (if (not (string-contains? test-file "_"))
           (error 'run-tests "single test input should be like r3_4")
           (let* ([parts (string-split test-file "_")]
                  [name (car parts)]
                  [num (string->number (cadr parts))])
             (single-test pass name num))))))

;(all-tests r5-passes)
