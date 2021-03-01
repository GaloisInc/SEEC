#lang seec
(require seec/private/util)
(require "tinyC.rkt"
         "tinyC-test.rkt")

#;(define prog (list->seec simple-call-example))
#;(define inputs (tinyC trace 3))
#;(define inputs (seec-singleton 3))
#;(parameterize ([debug? #t])
  (tinyC:display-state (tinyC:run+ prog inputs)))

(let ([g (find-gadget tinyC-lang
                      (λ (p tr) (equal? tr (seec-singleton 3)))
                      #:expr (list->seec simple-call-example)
                      #:context-bound 4
                      #:fresh-witness #f
                      #:forall (list )
                      )])
  (display-gadget g displayln))
; Should find (seec-singleton 3)

