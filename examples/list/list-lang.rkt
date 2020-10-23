; Cleaned up version of list.rkt

#lang seec

(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(provide (all-defined-out))

#;(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    [_ (raise-argument-error 'bonsai->number "bonsai-integer?" n)]
    ))

(define (snoc a b)
  (cons b a))

(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a list datatype
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar list-api
  (value ::= integer)
  (vallist ::= (value vallist) empty)
  (method ::=  (mcons value) mnil) 
  (interaction ::= (method interaction) empty)
  (observation ::= empty? (lookup value))
  (complete-interaction ::= observation (method complete-interaction)))

(define (value->number n)
  (match n
    [(list-api i:integer) i]
    [_ (raise-argument-error 'value->number "list-api-integer?" n)]
    ))

(define (length-list l)
  (match l
    [(list-api empty) 0]
    [(list-api (v:value l-tl:vallist))
     (+ (length-list l-tl) 1)]))

(define (abstract-cons n l)
  (list-api (,n ,l)))

(define abstract-nil
  (list-api empty))

(define (abstract-empty? l)
  (match l
    [(list-api empty)
     #t]
    [ _
      #f]))

(define (abstract-head n l)
  (match l
    [(list-api (hd:value tl:vallist))
     hd]))

(define (abstract-tail n l)
  (match l
    [(list-api (hd:value tl:vallist))
     tl]))

(define (abstract-nth n l)
  (match l
    [(list-api (hd:value tl:vallist))
     (if (equal? n 0)
         hd
         (abstract-nth (- n 1) tl))]
    [(list-api empty)
     #f]))

(define (abstract-lookup k l)
  (match l
    [(list-api empty)
     #f]
    [(list-api (kc:value tl:vallist))
     (match tl
       [(list-api (vc:value tll:vallist))
        (if (equal? (value->number kc) (value->number k))
            vc
            (abstract-lookup k tll))])]))

 
(define (interpret-interaction ints l)
  (match ints
    [(list-api empty) l]
    [(list-api (m:method intss:interaction))
     (match m
       [(list-api mnil)
        (interpret-interaction intss (list-api empty))]
       [(list-api (mcons n:value))
        (interpret-interaction intss (list-api (,n ,l)))])]))

(define (interpret-complete-interaction ints l)
  (match ints
    [(list-api empty?)
     (abstract-empty? l)]
    [(list-api (lookup k:value))
     (abstract-lookup k l)]
    [(list-api (m:method intss:complete-interaction))     
     (match m
       [(list-api mnil)
        (interpret-complete-interaction intss (list-api empty))]
       [(list-api (mcons n:value))
        (interpret-complete-interaction intss (list-api (,n ,l)))])]))



(define-language list-lang
  #:grammar list-api 
  #:expression vallist #:size 6
  #:context complete-interaction #:size 3
  #:link cons
  #:evaluate (uncurry interpret-complete-interaction))

(define (list-demo)
  (let* ([abc (list-api (1 (2 (3 empty))))]
         [i1 (list-api ((mcons 4) ((mcons 1) empty)))]
         [i2 (list-api (mnil ,i1))]
         [ci1 (list-api (mnil empty?))])
      (displayln (interpret-interaction i1 abc))
      (displayln (interpret-interaction i2 abc))
      (displayln (interpret-complete-interaction ci1 abc))))
