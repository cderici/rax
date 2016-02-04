#lang racket
(require racket/pretty)
(provide debug map2 label-name lookup  make-dispatcher assert
         read-fixnum read-program 
	 compile compile-file check-passes interp-tests compiler-tests fix while 
	 make-graph add-edge adjacent vertices print-dot
	 general-registers registers-for-alloc caller-save callee-save
	 arg-registers register->color registers align)

(define debug-state #f)

(define (debug label val)
  (if debug-state
      (begin
	(printf "~a:\n" label)
	(pretty-print val)
	(newline))
      (void)))

(define-syntax-rule (while condition body ...)
  (let loop ()
    (when condition
      body ...
      (loop))))

(define fix (lambda (f) (lambda (x) ((f (fix f)) x))))

;; This function is like map but the function f returns
;; two values using the ``values'' form. Thus, the result
;; of map2 is two lists.
(define (map2 f ls)
  (cond [(null? ls)
         (values '() '())]
        [else
         (let-values ([(x1 x2) (f (car ls))]
                      [(ls1 ls2) (map2 f (cdr ls))])
           (values (cons x1 ls1) (cons x2 ls2)))]))

;; This function prepends an underscore to a label if
;; the current system is Mac OS and leaves it alone otherwise
(define label-name
  (lambda (n)
    (if (eqv? (system-type 'os) 'macosx)
        (string-append "_" n)
        n)))

;; The lookup function takes a key and an association list
;; and returns the corresponding value. It triggers an
;; error if the key is not present in the association list.
;;   
;; The association list may be constructed of either
;; immutable or mutable pairs.
;; 
(define lookup
  (lambda (x ls)
    (cond [(null? ls)
	   (error "lookup failed for " x)]
	  [(and (pair? (car ls)) (eq? x (car (car ls))))
	   (cdr (car ls))]
	  [(and (mpair? (car ls)) (eq? x (mcar (car ls))))
	   (mcdr (car ls))]
	  [else 
	   (lookup x (cdr ls))])))

(define (read-fixnum)
  (define r (read))
  (cond [(fixnum? r) r]
	[else (error 'read "expected an integer")]))

;; Read an entire .rkt file wrapping the s-expressions in
;; a list whose head is 'program.
(define (read-program path)
  (unless (or (string? path) (path? path))
    (error 'read-program "expected a string in ~s" path))
  (unless (file-exists? path)
    (error 'read-program "file doesn't exist in ~s" path))
  (define input-prog
    (call-with-input-file path
      (lambda (f)
        `(program . ,(for/list ([e (in-port read f)]) e)))))
  (when debug-state
    (printf "read program:\n~s\n\n" input-prog))
  input-prog)

(define (make-dispatcher mt)
  (lambda (e . rest)
    (match e
       [`(,tag ,args ...)
	(apply (hash-ref mt tag) (append rest args))]
       [else
	(error "no match in dispatcher for " e)]
       )))

;; The check-passes function takes a compiler name (a string), a
;; typechecker (see below), a description of the passes (see below),
;; and an initial interpreter to apply to the initial expression, and
;; returns a function that takes a test name and runs the passes and
;; the appropriate interpreters to test the correctness of all the
;; passes. This function assumes there is a "tests" subdirectory and a
;; file in that directory whose name is the test name followed by
;; ".rkt". Also, there should be a matching file with the ending ".in"
;; that provides the input for the Scheme program. If any program
;; should not pass typechecking, then there is a file with the name
;; number (whose contents are ignored) that ends in ".tyerr".
;;
;; The description of the passes is a list with one entry per pass.
;; An entry is a list with three things: a string giving the name of
;; the pass, the function that implements the pass (a translator from
;; AST to AST), and a function that implements the interpreter (a
;; function from AST to result value).
;;
;; The typechecker is a function of exactly one argument that EITHER
;; raises an error using the (error) function when it encounters a
;; type error, or returns #f when it encounters a type error. 

(define (check-passes name typechecker passes initial-interp)
  (lambda (test-name)
    (debug "** compiler " name)
    (debug "** checking passes for test " test-name)
    (define input-file-name (format "tests/~a.in" test-name))
    (define program-name (format "tests/~a.rkt" test-name))
    (define sexp (read-program program-name))
    (debug "program:" sexp)
    (define type-error-expected (file-exists? (format "tests/~a.tyerr" test-name)))
    (define typechecks (test-typecheck typechecker sexp))
    
    (cond
     [(and type-error-expected typechecks)
      (error (format "expected type error in compiler '~a', but no error raised by typechecker" name))]
     [type-error-expected 'expected-type-error]
     [typechecks 
      (let loop ([passes passes] [p sexp]
                 [result (if (file-exists? input-file-name)
                             (with-input-from-file input-file-name
                               (lambda () (initial-interp sexp)))
                             (initial-interp sexp))])
        (cond [(null? passes) result]
              [else
               (match (car passes)
                 [`(,pass-name ,pass ,interp)
                  (debug "running pass" pass-name)
                  (define new-p (pass p))
                  (debug pass-name new-p)
                  (cond [interp
                         (let ([new-result
                                ;; if there is an input file with the same name
                                ;; as this test bing current-input-port to that
                                ;; file's input port so that the interpreters
                                ;; can use it as test input.
                                (if (file-exists? input-file-name) 
                                    (with-input-from-file input-file-name
                                      (lambda () (interp new-p)))
                                    (interp new-p))])
                           (cond [result
                                  (cond [(equal? result new-result)
                                         (loop (cdr passes) new-p new-result)]
                                        [else
                                         (display "in program")(newline)
                                         (pretty-print new-p)(newline)
                                         (error (format "differing results in compiler '~a' pass '~a', expected ~a, not" name pass-name result )
                                                new-result)])]
                                 [else ;; no result to check yet
                                  (loop (cdr passes) new-p new-result)]))]
                        [else
                         (loop (cdr passes) new-p result)])])]))
      ]
     [else (error (format "unexpected type error raised by compiler '~a'" name))])))

(define (compile passes)
  (let ([prog-file-name (vector-ref (current-command-line-arguments) 0)])
    ((compile-file passes) prog-file-name)))

;; The compile-file function takes a typechecker and a description of
;; the compiler passes (see the comment for check-passes) and returns
;; a function that, given a program file name (a string ending in
;; ".rkt") that passes typechecking, applies all of the passes and
;; writes the output to a file whose name is the same as the proram
;; file name but with ".rkt" replaced with ".s". The function then
;; returns #t. If the program does not typecheck, the returned
;; function will return #f.
(define (compile-file typechecker passes)
  (lambda (prog-file-name)
    (define file-base (string-trim prog-file-name ".rkt"))
    (define out-file-name (string-append file-base ".s"))
    (call-with-output-file
      out-file-name
      #:exists 'replace
      (lambda (out-file)
        (define sexp (read-program prog-file-name))
        (if (test-typecheck typechecker sexp)
            (let ([x86 (let loop ([passes passes] [p sexp])
                         (cond [(null? passes) p]
                               [else
                                (match (car passes)
                                  [`(,name ,pass ,interp)
                                   (let* ([new-p (pass p)])
                                     (loop (cdr passes) new-p)
                                     )])]))])
              (cond [(string? x86)
                     (write-string x86 out-file)
                     (newline out-file)
                     #t]
                    [else
                     (error "compiler did not produce x86 output")])
              )
            #f)))))

;; The interp-tests function takes a compiler name (a string), a
;; typechecker (see the comment for check-passes) a description of the
;; passes (ditto) a test family name (a string), and a list of test
;; numbers, and runs the compiler passes and the interpreters to check
;; whether the passes correct.
;; 
;; This function assumes that the subdirectory "tests" has a bunch of
;; Scheme programs whose names all start with the family name,
;; followed by an underscore and then the test number, ending in
;; ".rkt". Also, for each Scheme program there is a file with the same
;; number except that it ends with ".in" that provides the input for
;; the Scheme program. If any program should not pass typechecking,
;; then there is a file with the name number (whose contents are
;; ignored) that ends in ".tyerr".

(define (interp-tests name typechecker passes initial-interp test-family test-nums)
  (define checker (check-passes name typechecker passes initial-interp))
  (for ([test-name (map (lambda (n) (format "~a_~a" test-family n)) 
			test-nums)])
       (checker test-name)
       ))

;; The compiler-tests function takes a compiler name (a string), a
;; typechecker (see the comment for check-passes) a description of the
;; passes (ditto), a test family name (a string), and a list of test
;; numbers (see the comment for interp-tests), and runs the compiler
;; to generate x86 (a ".s" file) and then runs gcc to generate machine
;; code, unless a type error is detected. It runs the machine code and
;; stores the result. If the test file has a corresponding .res file,
;; the result is compared against its contents; otherwise, the result
;; is compared against 42. If a type error is detected, it will check
;; if a .tyerr file exists, and report an error if not. It will do the
;; same if a .tyerr file exists but the typechecker does not report an
;; error.

(define (compiler-tests name typechecker passes test-family test-nums)
  (define compiler (compile-file typechecker passes))
  (debug "compiler-tests starting" '())
  (for ([test-name (map (lambda (n) (format "~a_~a" test-family n)) 
			test-nums)])
       (debug "compiler-tests, testing:" test-name)
       (define type-error-expected (file-exists? (format "tests/~a.tyerr" test-name)))
       (define typechecks (compiler (format "tests/~a.rkt" test-name)))
       (if (and (not typechecks) (not type-error-expected))
           (error (format "test ~a failed, unexpected type error" test-name)) 
           '())
       (if typechecks
           (if (system (format "gcc -g -std=c99 runtime.o tests/~a.s" test-name))
               (void) (exit))
           '())
       (let* ([input (if (file-exists? (format "tests/~a.in" test-name))
			 (format " < tests/~a.in" test-name)
			 "")]
              [output (if (file-exists? (format "tests/~a.res" test-name))
                          (call-with-input-file
			      (format "tests/~a.res" test-name)
                            (lambda (f) (string->number (read-line f))))
                          42)]
              [progout (if typechecks (process (format "./a.out~a" input)) 'type-error)]
	      )
	 ;; process returns a list, it's first element is stdout
	 (match progout
           ['type-error (display test-name) (display " ") (flush-output)] ;already know we don't have a false positive
           [`(,in1 ,out ,_ ,in2 ,control-fun)
            (if type-error-expected
                (error (format "test ~a passed typechecking but should not have." test-name)) '())
            (control-fun 'wait)
            (cond [(eq? (control-fun 'status) 'done-ok)
		    (let ([result (string->number (read-line (car progout)))])
		      (if (eq? result output)
			  (begin (display test-name)(display " ")(flush-output))
			  (error (format "test ~a failed, output: ~a" 
					 test-name result))))]
		   [else
		    (error
		     (format "test ~a error in x86 execution, exit code: ~a" 
			     test-name (control-fun 'exit-code)))])
            (close-input-port in1)
            (close-input-port in2)
	     (close-output-port out)])
         )))


;; Takes a function of 1 argument (or #f) and Racket expression, and
;; returns whether the expression is well-typed. If the first argument
;; is #f, that means we aren't providing a typechecker so we simply
;; return true. If not, we apply the typechecker to the expression. We
;; require that a typechecker will EITHER raise an error using the
;; (error) function when it encounters a type error, or that it
;; returns #f when it encounters a type error. This function then
;; returns whether a type error was encountered.
(define test-typecheck 
  (lambda (tcer exp)
    (if (eq? tcer #f) #t
        (let ([res 
               (with-handlers ([exn:fail?
                                (lambda (e) #f)])
                 (tcer exp))])
          (if (eq? res #f) #f #t)))))

(define assert
  (lambda (msg b)
    (if (not b)
	(begin
	  (display "ERROR: ")
	  (display msg)
	  (newline))
	(void))))


;; System V Application Binary Interface
;; AMD64 Architecture Processor Supplement
;; Edited by Jan Hubicˇka, Andreas Jaeger, Mark Mitchell
;; December 2, 2003

(define arg-registers (vector 'rdi 'rsi 'rdx 'rcx 'r8 'r9))

(define caller-save (set 'rdx 'rcx 'rsi 'rdi 'r8 'r9 'r10 'r11 ))
(define callee-save (set 'rbx 'r12 'r13 'r14 'r15))

;; there are 13 general registers:
(define general-registers (vector 'rbx 'rcx 'rdx 'rsi 'rdi
    				  'r8 'r9 'r10 'r11 'r12 
				  'r13 'r14 'r15))

;; registers-for-alloc should always inlcude the arg-registers. -Jeremy 
(define registers-for-alloc general-registers)


(define reg-colors
  '((rax . -1) (__flag . -1)
    (rbx . 0) (rcx . 1) (rdx . 2) (rsi . 3) (rdi . 4)
    (r8 . 5) (r9 . 6) (r10 . 7) (r11 . 8) (r12 . 9) (r13 . 10)
    (r14 . 11) (r15 . 12)))

(define (register->color r)
  (cdr (assq r reg-colors)))

(define registers (set-union (list->set (vector->list general-registers))
			     (set 'rax 'rsp 'rbp '__flag)))

(define (align n alignment)
  (cond [(eq? 0 (modulo n alignment))
	 n]
	[else
	 (+ n (- alignment (modulo n alignment)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Graph ADT

(define (make-graph vertices)
  (make-hash (map (lambda (v) (cons v (set))) vertices)))

(define (add-edge graph u v)
  (hash-set! graph u (set-add (hash-ref graph u (set)) v))
  (hash-set! graph v (set-add (hash-ref graph v (set)) u)))

(define (adjacent graph u)
  (hash-ref graph u))

(define (vertices graph)
  (hash-keys graph))

(define (print-dot graph file-name)
  (if debug-state
      (call-with-output-file file-name #:exists 'replace
	(lambda (out-file)
	  (write-string "strict graph {" out-file) (newline out-file)
	  
	  (for ([v (vertices graph)])
	       (write-string (format "~a;\n" v) out-file))
	  
	  (for ([v (vertices graph)])
	       (for ([u (adjacent graph v)])
		    (write-string (format "~a -- ~a;\n" u v) out-file)))
	  
	  (write-string "}" out-file)
	  (newline out-file)))
      '()))
      
