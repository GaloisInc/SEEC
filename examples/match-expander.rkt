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

(struct foo (value))

(define-match-expander foom
  (lambda (stx)
    (syntax-parse stx
      [(_ x)
       #'(? foo? (! foo-value x))]))
  (lambda (stx)
    (syntax-parse stx
      [(_ s ...)
       #'(foo s ...)])))

(match (foo 7)
  [(foom x) x])

(match (bonsai-integer 7)
  [(bonsai-integer x) x])
