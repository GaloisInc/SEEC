#lang seec
(provide (all-defined-out))

(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

(define snoc
  (lambda (a b) (cons b a)))
