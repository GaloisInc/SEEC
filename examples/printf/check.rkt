#lang seec
(require (file "syntax.rkt"))

(define (test-lookup-offset)
  (displayln "Testing lookup-offset...")
  (define-symbolic* offset integer?)
  (define args (printf-lang vlist 5))
  (assert (< offset (vlist-length args)))
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



