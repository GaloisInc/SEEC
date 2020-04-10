#lang seec

(require seec/private/match)
(require (for-syntax syntax/parse))

(define-match-expander negative
  (lambda (stx)
    (syntax-parse stx
      [(_ x)
       #'(? (lambda (t) (< (bonsai-integer-value t) 0)) (bonsai-integer x))])))

(match (bonsai-integer -5)
  [(negative x) x]
  [_ #f])
