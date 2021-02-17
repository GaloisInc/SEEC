#lang seec
(require "tinyC.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt"
         "tinyC-test.rkt")

(module+ test (require rackunit
                       rackunit/text-ui
                       racket/contract
                       ))


(module+ test

  (check-equal? (tinyA:run factorial
                           (list 6))
                (seec-singleton 6))
  )

