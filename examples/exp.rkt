#lang seec

(require (only-in racket
                  with-handlers
                  exn:fail?
                  exn-message))

(define-grammar exp
  (exp   ::= boolean natural (S exp) (binop exp exp))
  (binop ::= = and or)
  (type  ::= nat bool))

(define (type-exp e)
  (match e
    [(exp natural) (exp nat)]
    [(exp boolean) (exp bool)]
    [(exp (S n:exp))
     (assert (equal? (type-exp n) (exp nat)))
     (exp nat)]
    [(exp (= l:exp r:exp))
     (assert (equal? (type-exp l) (type-exp r)) "operands of `=` must have same type")
     (exp bool)]
    [(exp (and l:exp r:exp))
     (assert (equal? (type-exp l) (exp bool)) "operands of `and` must have type `bool`")
     (assert (equal? (type-exp r) (exp bool)) "operands of `and` must have type `bool`")
     (exp bool)]
    [(exp (or l:exp r:exp))
     (assert (equal? (type-exp l) (exp bool)) "operands of `or` must have type `bool`")
     (assert (equal? (type-exp r) (exp bool)) "operands of `or` must have type `bool`")
     (exp bool)]))

(define (eval-exp e)
  (match e
    [(exp natural) e]
    [(exp boolean) e]
    [(exp (S n:exp))
     (+ (eval-exp n) 1)]
    [(exp (= l:exp r:exp))
     (if (equal? (eval-exp l) (eval-exp r))
         (exp #t)
         (exp #f))]
    [(exp (and l:exp r:exp))
     (match (list (eval-exp l) (eval-exp r))
       [(list (exp #t) (exp #t)) (exp #t)]
       [_ (exp #f)])]
    [(exp (or l:exp r:exp))
     (match (list (eval-exp l) (eval-exp r))
       [(list (exp #f) (exp #f)) (exp #f)]
       [_ (exp #t)])]))

(define eq-example (exp (= #t #f)))

(define test-exps
  (list (exp 0)
        eq-example
        (exp (or ,eq-example #t))
        (exp (= 0 0))))

(for-each (λ (e)
            (let ([v (instantiate e)])
              (printf "Testing expression ~a of size ~a~n" v (bonsai-depth v))
              (printf "Running the interpreter...~n")
              (printf "~a~n" (instantiate (eval-exp v)))
              (printf "Running the type checker...~n")
              (printf "~a~n~n" (instantiate (type-exp v)))))
          test-exps)

(displayln "Building tree...")
(define t* (time (exp exp 5)))
(displayln "Evaluating...")
(void (time (eval-exp t*)))
(displayln "Type-checking...")
(define-values (v a) (with-asserts (time (type-exp t*))))
(displayln "Searching for ill-typed terms that evaluate successfully...")
(define sol
  (time (optimize #:minimize  (list (bonsai-leaves t*))
                  #:guarantee (assert (! (apply && a))))))
(define t (concretize t* sol))
(displayln "Bad tree:")
(displayln t)
(displayln "Bad tree evaluation:")
(displayln (eval-exp t))
(displayln "Bad tree typing")
(with-handlers ([exn:fail? (λ (e) (printf "Caught expected assertion failure: ~a~n" (exn-message e)))])
  (displayln (type-exp t)))
