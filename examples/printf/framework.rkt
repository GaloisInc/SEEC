#lang seec
(require (file "syntax.rkt"))

(define (spec-interpret f-ctx)
  (match (second f-ctx)
    [(printf-lang (args:arglist conf:config)) (interp-fmt-safe (first f-ctx) args conf)]
    ))
(define (impl-interpret f-ctx)
  (match (second f-ctx)
    [(printf-lang (args:arglist conf:config)) (interp-fmt-unsafe (first f-ctx) args conf)]
    ))


(define-language specification
  #:grammar printf-lang
  #:expression fmt #:size 2
  ; any way to make the where clause assume consistency with the format?
  #:context context #:size 6 #:where #;(max-context-size 5 2) (λ (x) x)
  #:link cons
  #:evaluate spec-interpret
  )

(define-language implementation
  #:grammar printf-lang
  #:expression fmt #:size 2
  #:context context #:size 6 #:where (λ (x) x)
  #:link cons
  #:evaluate impl-interpret
  )

(define-compiler spec-to-impl
  #:source specification
  #:target implementation
  #:behavior-relation equal?
  #:context-relation equal?
  #:compile (λ (x) x)
  )

#;(define (find-add-constant-gadget)
  (displayln "Trying to find a format string that adds a constant number to the accumulator")
)
#;(begin
  (displayln "Trying to find a trace with different behavior under compilation")
  (define trace (printf-lang interaction 6))
  (define witness (find-changed-behavior abstract-to-concrete trace))
  (display-witness witness))

