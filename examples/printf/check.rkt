#lang seec
(require (file "syntax.rkt"))


(define (test-lookup-offset)
  (displayln "Testing lookup-offset...")
  (define-symbolic* offset integer?)
  (define args (printf-lang vlist 5))
  (assert (< offset (bonsai-ll-length args)))
  (define sol
    (verify (val? (lookup-offset offset args))))
  (if (unsat? sol)
      (displayln "Verified.")
      (begin
        (displayln "Counterexample found.")
        (displayln "Offset...")
        (concretize offset sol)
        (displayln "Vlist...")
        (concretize args sol)
        ))
)
(test-lookup-offset)


(define (test-mem-update)
  (displayln "Testing mem-update")
  (define m (printf-lang mem 5))
  (define l (printf-lang ident 1))
  (define v (printf-lang val 1))
  (assert (mem? m))
  (define sol (verify (mem? (mem-update m l v))))
  (if (unsat? sol)
      (displayln "Verified")
      (displayln "Counterexample found.")))
(test-mem-update)


(define (test-interp-fmt-safe)
  (displayln "Testing interp-fmt-safe")
  (displayln "NOTE: times out when increasing size of vlist beyond 2")
  (define f (printf-lang fmt 5))
  (define args (printf-lang vlist 2))
  (define conf (printf-lang config 5))
  (assert (fmt-consistent-with-vlist? f args))
  (define sol (verify (match (interp-fmt-safe f args conf)
                        [(list str conf+) (conf? conf+)]
                        )))
  (if (unsat? sol)
      (displayln "Verified")
      (begin
        (displayln "Counterexample found.")
        (displayln "fmt...")
        (define f-instance (concretize f sol))
        (displayln f-instance)
        (displayln "args...")
        (define args-instance (concretize args sol))
        (displayln args-instance)
        (displayln "conf...")
        (define conf-instance (concretize conf sol))
        (displayln conf-instance)
        (define res-instance (interp-fmt-safe f-instance args-instance conf-instance))
        (displayln res-instance)
        )))
(test-interp-fmt-safe)


(define (test-interp-fmt-unsafe)
  (displayln "Testing interp-fmt-unsafe")
  (displayln "NOTE: times out when increasing size of vlist beyond 2")
  (define f (printf-lang fmt 5))
  (define args (printf-lang vlist 2))
  (define conf (printf-lang config 5))
  #;(assert (fmt-consistent-with-vlist? f args))
  (define sol (verify (match (interp-fmt-unsafe f args conf)
                        [(list _ conf+) (conf? conf+)]
                        )))
  (if (unsat? sol)
      (displayln "Verified")
      (begin
        (displayln "Counterexample found.")
        (displayln "fmt...")
        (define f-instance (concretize f sol))
        (displayln f-instance)
        (displayln "args...")
        (define args-instance (concretize args sol))
        (displayln args-instance)
        (displayln "conf...")
        (define conf-instance (concretize conf sol))
        (displayln conf-instance)
        (define res-instance (interp-fmt-unsafe f-instance args-instance conf-instance))
        (displayln res-instance)
        (match res-instance
          [(list _ conf+) (conf? conf+)])
        )))
(test-interp-fmt-unsafe)
;;; WHY IS THIS A COUNTEREXAMPLE???

#|
(define fmt-ex (printf-lang (cons (% 0 $ 1 d) nil)))
(define args-ex (printf-lang nil))
(define conf-ex (printf-lang (0 mnil)))
(define res (interp-fmt-unsafe fmt-ex args-ex conf-ex))
(match res
  [(list s conf+) (conf? conf+)])
|#

(define (find-exploit)
  (define f (printf-lang fmt 5))
  (define args (printf-lang vlist 2))
  (define conf (printf-lang config 5))
  (displayln "Searching for a format string that evaluates in the target but not in the source")
  (define sol (verify #:assume (assert (match (interp-fmt-unsafe f args conf)
                                         [(list str conf+) (conf? conf+)]))
                      #:guarantee (assert (fmt-consistent-with-vlist? f args))
                      ))
  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded.")
        (displayln "fmt...")
        (define f-instance (concretize f sol))
        (displayln f-instance)
        (displayln "args...")
        (define args-instance (concretize args sol))
        (displayln args-instance)
        (displayln "conf...")
        (define conf-instance (concretize conf sol))
        (displayln conf-instance)
        (define res-instance (interp-fmt-unsafe f-instance args-instance conf-instance))
        (displayln res-instance)
        (displayln (fmt-consistent-with-vlist? f-instance args-instance))
        )))
(find-exploit)

#|
(define (find-addition)
  (define f (printf-lang fmt 5))
  (define-symbolic y integer?)
  (define-symbolic x integer?)
  (define-symbolic x+y integer?)
  (define conf (printf-lang config 5))
  (displayln "Searching for a format string that performs addition")

  (define (is-addition f x y x+y conf)
    (let ([args (printf-lang (cons ,x (cons ,y (cons ,x+y nil))))])
      (match (interp-fmt-unsafe f args conf)
        [(list str conf+)
         (match (lookup-loc 
         

  (define sol (verify #:assume (assert (match (interp-fmt-unsafe f args conf)
                                         [(list str conf+) (
|#
