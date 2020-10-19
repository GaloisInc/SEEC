#lang seec
(require (file "lib.rkt"))
(require (file "simp.rkt"))
(provide (all-defined-out))
; Testing grammar and language definitions with integers
; lib

(require racket/contract)
(require (only-in racket/base
                  raise-argument-error))

; SIMP with integer
(define-grammar simp+integer
  (num ::= integer)
  (op ::= + *)
  (exp ::= (op exp exp) var num))

(define/contract (num->integer n)
  (-> simp+integer-num? integer?)
  (match n
    [(simp+integer x:integer) x]
    ))


(define (interp-binop op n1 n2)
  (match op
  [(simp+integer +)
   (+ n1 n2)]
  [(simp+integer *)
   (* n1 n2)]))


; exp -> racket integer
(define/contract (eval-simp+integer v exp)
  (-> (or/c simp+integer-num? #f) simp+integer-exp? integer?)
  (match exp
    [(simp+integer (o:op e1:exp e2:exp))
     (interp-binop o (eval-simp+integer v e1) (eval-simp+integer v e2))]
    [(simp+integer n:num)
     (num->integer n)]
    [(simp+integer var)
     (match v
       [(simp+integer x:integer) x]
       [_ (raise-argument-error 'eval-simp+integer
                                "Expected a simp+integer-num? when evaluating an open term"
                                v)]
       )]
    ))

(define (eval-simp+integer-closed exp)
  (eval-simp+integer #f exp))

(define-language SIMP+INTEGER
  #:grammar simp+integer
  #:expression exp #:size 4
  #:context num #:size 1
  #:link cons
  #:evaluate (uncurry eval-simp+integer))


(define simp+integer-term-1
  (simp+integer 1))
(define simp+integer-term-2
  (simp+integer (+ -3 5)))
(define simp+integer-term-3
  (simp+integer (+ (* -1 -2) 1)))
(define simp+integer-term-4
  (simp+integer (+ var (* 1 var))))


(define test-eval-simp+integer-1
  (eval-simp+integer-closed simp+integer-term-1))
(define test-eval-simp+integer-2
  (eval-simp+integer-closed simp+integer-term-2))
(define test-eval-simp+integer-3
  (eval-simp+integer-closed simp+integer-term-3))
(define test-eval-simp+integer-4
  (eval-simp+integer simp+integer-term-1 simp+integer-term-4))

(define (simp-to-simp+integer e)
  (match e
    [(simp (o:op e1:exp e2:exp))
     (let ([e1+ (simp-to-simp+integer e1)]
           [e2+ (simp-to-simp+integer e2)])
       (simp+integer (,o ,e1+ ,e2+)))]
    [(simp n:num)
     (simp+integer ,(eval-num n))]
    [_
      e]))

(define-compiler SIMP-TO-INTEGER
  #:source SIMP
  #:target SIMP+INTEGER
  #:behavior-relation equal?
  #:context-relation (lambda (p n) (equal? (eval-num p) n))
  #:compile simp-to-simp+integer)

;; no changed or weird component should exist
(define (test-cc-simp-to-integer) (find-changed-component SIMP-TO-INTEGER))
(define (test-wc-simp-to-integer) (find-weird-component SIMP-TO-INTEGER))

