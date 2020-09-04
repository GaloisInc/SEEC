#lang seec
(provide (all-defined-out))

; lib
(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))

(define id
  (lambda (a)
    a))

(define snoc
  (lambda (a b) (cons b a)))
