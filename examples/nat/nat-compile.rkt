#lang seec

(require "int-exp.rkt")
; ^ defines:
; (define-grammar int-exp
;   (val   ::= input integer)
;   (exp   ::= (+ exp exp) val
;              (neg? exp exp exp)))
; (define (int-subst n exp) ...)
; (define (int-eval exp) ...)

(define-language int-lang
  #:grammar    int-exp
  #:expression exp      #:size 3
  #:context    integer  #:size 1
  #:link       int-subst
  #:evaluate   int-eval)

(define-compiler nat-to-int
  #:source nat-lang
  #:target int-lang
  #:behavior-relation equal?
  #:compile (lambda (t) t))

(require "nat-lang.rkt")

(provide (all-defined-out)
         (all-from-out "nat-lang.rkt")
         (all-from-out "int-exp.rkt"))
