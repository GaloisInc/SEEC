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

  ; Currently debugging is not working--why?
  (parameterize ([debug? #t])
    (check-equal? (tinyA:run factorial
                             (list 6))
                  (seec-singleton 6)))
  )
