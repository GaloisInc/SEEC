#lang seec
(require racket/base)
(require (file "syntax.rkt"))
(require seec/private/bonsai2)

(define (test)
  (displayln "Building...")
  (define f (time (printf-lang fmt 6)))
  (define args (time (printf-lang arglist 4)))
  (define conf (time (printf-lang config 4)))
  (displayln "Interpretation...")
  (define result
    (match (interp-fmt-safe f args conf)
      [(list str conf+)
       str
       ]
      ))
  (displayln "Finding a format string")
  (define sol 
    (time (verify (assert (equal? result ""))))

    )
  (if (unsat? sol)
      (displayln "Synthesis failed")
      (begin
        (displayln "Found result printing the empty string...")
        (define f-instance (concretize f sol))
        )
      )
  #;(if (unsat? sol)
      (displayln "Synthesis failed")
      ; else
      (let ([f-instance (concretize f sol)]
            [args-instance (concretize args sol)]
            [conf-instance (concretize conf sol)]
            )
        (displayln "Found result printing the empty string...")
        (displayln "f...")
        (displayln f-instance)
        (displayln "args...")
        (displayln args-instance)
        (displayln "conf...")
        (displayln conf-instance)
        (interp-fmt-safe f-instance args-instance conf-instance)
        )
      )
)

(test)
;(define test 
;  (interp-fmt-safe (printf-lang (%d 0)
