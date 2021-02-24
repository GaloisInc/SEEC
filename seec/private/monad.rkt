#lang seec

(require (for-syntax syntax/parse))
(require "util.rkt")
(module+ test (require rackunit))

(provide do
         <-
         *fail*
         failure/c
         failure?
         any-failure?
         failure-foldl
         )

(define-syntax (<- stx)
  (raise-syntax-error '<- "Used out of context") stx)

(struct failure ())
(define *fail* (failure))
(define (failure/c contract?) (or/c failure? contract?))
(define (bool-bind m k)
  (if (failure? m) m (k m)))

; The failure monad.
; There is no need to wrap a pure value in `pure` or `return`.
;
; do do-syntax ...
;
; where
; 
; do-syntax ::= x <- maybe-failure
;             | maybe-failure
; maybe-failure ::= *fail* | e
;
(define-syntax (do stx)
  (syntax-parse stx
    #:literals (<-)
    [(_ e) #'e]
    [(_ (<- x:id e1) e2 more ...)
     (syntax/loc stx
       (bool-bind e1 (lambda (x) (do e2 more ...))))]
    [(_ x:id <- e1 e2 more ...)
     (syntax/loc stx
       (bool-bind e1 (lambda (x) (do e2 more ...))))]
    [(_ e1 e2 more ...)
     (syntax/loc stx
       (if (failure? e1) e1 (do e2 more ...)))]
    ))

; Given a list lst of failure-monad computations, apply procedure on each
; element, starting at the left, where `proc` is a monadic computation
(define (failure-foldl proc init lst)
  (let ([proc+ (λ (lst-elem acc) (do x <- lst-elem
                                     y <- acc
                                     proc x y))])
    (foldl proc+ init lst)
    ))

; Return #t if any of the elements in lst are *fail*, otherwise return #f
(define (any-failure? lst)
  (let ([proc (λ (lst-elem acc) (or (failure? lst-elem) acc))])
    (foldl proc #f lst)))
   


(module+ test
  (check-equal? (do *fail*) *fail*)
  (check-equal? (do 5) 5)
  (check-equal? (do *fail* 5) *fail*)
  (check-equal? (do 16 5) 5)
  (check-equal? (do (<- x 4) (+ x 1)) 5)
  (check-equal? (do (<- x *fail*) (+ x 1)) *fail*)
  (check-equal? (do (<- x 4) (<- y 5) (+ x y)) 9)
  (check-equal? (do 16 (<- x 3) x) 3)
  (check-equal? (do x <- 4
                    (+ x 1))
                5)
  (check-equal? (do x <- *fail*
                    (+ x 1))
                *fail*)
  (check-equal? (do x <- 4
                    y <- 5
                    (+ x y))
                9)
  (check-equal? (do 16
                    x <- 3
                    x)
                3)

  (check-equal? (any-failure? (list #t 16 22))
                #f)
  (check-equal? (any-failure? (list))
                #f)
  (check-equal? (any-failure? (list #t 16 *fail*))
                #t)

  )
