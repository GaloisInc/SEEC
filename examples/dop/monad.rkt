#lang seec

(require (for-syntax syntax/parse))
(module+ test (require rackunit))

(provide do <-)

(define-syntax (<- stx)
  (raise-syntax-error '<- "Used out of context") stx)

(define (bool-bind m k)
  (if m (k m) #f))

(define-syntax (do stx)
  (syntax-parse stx
    #:literals (<-)
    [(_ e) #'e]
    [(_ (<- x:id e1) e2 more ...)
     (syntax/loc stx
       (bool-bind e1 (lambda (x) (do e2 more ...))))]
    [(_ e1 e2 more ...)
     (syntax/loc stx
       (and e1 (do e2 more ...)))]))

(module+ test
  (check-equal? (do #f) #f)
  (check-equal? (do 5) 5)
  (check-equal? (do #f 5) #f)
  (check-equal? (do 16 5) 5)
  (check-equal? (do (<- x 4) (+ x 1)) 5)
  (check-equal? (do (<- x #f) (+ x 1)) #f)
  (check-equal? (do (<- x 4) (<- y 5) (+ x y)) 9)
  )
