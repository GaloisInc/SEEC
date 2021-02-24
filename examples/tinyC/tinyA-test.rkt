#lang seec
(require "tinyC.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt"
         "tinyC-test.rkt")

(module+ test (require rackunit
                       rackunit/text-ui
                       seec/private/util
                       ))



(module+ test


  ; Check declaration->frame
  (define f-example-1 (declaration->frame assign-output-decl))
  (displayln f-example-1)
  (check-equal? (tinyA:frame-size f-example-1)
                2)

  (define f-example-2 (declaration->frame (first simple-call-example)))
  (displayln f-example-2)
  (check-equal? (tinyA:frame-size f-example-2)
                1)

  ; Check evaluation
  (parameterize ([debug? #f])
    (define g-result (tinyA:run assign-output-example (list 1)))
    (display-state g-result)
    (check-equal? (tinyA:state-trace g-result)
                  (list->seec (list 99))))

  (parameterize ([debug? #f])
     (define call-example-output (tinyA:run simple-call-example (list -5)))
     (display-state call-example-output)
     (check-equal? (tinyA:state-trace call-example-output)
                   (list->seec (list -5))))

  (parameterize ([debug? #f])
    (check-equal? (tinyA:state-trace (tinyA:run factorial
                                                (list 3)))
                  (seec-singleton 6)))
  )