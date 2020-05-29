#lang seec

(define (subst n exp)
  (match exp
    [(nat-exp input) n]
    [(nat-exp v:natural) v]
    [(nat-exp (+ l:exp r:exp))
     (nat-exp (+ ,(subst n l) ,(subst n r)))]))

(define (eval exp)
  (match exp
    [(nat-exp n:natural) n]
    [(nat-exp (+ l:exp r:exp))
     (nat-exp ,(seec-add (eval l)
                         (eval r)))]))

(define-language nat-lang
  #:grammar    nat-exp
  #:expression exp      #:size 3 #:where uses-input?
  #:context    natural  #:size 1
  #:link       subst
  #:evaluate   eval)

(define (with-two-is-seven? exp)
  (define result
    (link-and-evaluate nat-lang (nat-exp 2) exp))
  (and (uses-input? exp)
       (equal? (nat-exp 7) result)))

(require "nat-exp.rkt")

(provide (all-defined-out)
         (all-from-out "nat-exp.rkt"))
