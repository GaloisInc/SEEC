#lang seec

(define-grammar nat-exp
  (val   ::= natural input)
  (exp   ::= (+ exp exp) val))

(define increment (nat-exp (+ input 1)))

(define three (nat-exp (+ 1 2)))

(define (uses-input? expr)
  (match expr
    [(nat-exp (+ l:exp r:exp))
     (or (uses-input? l)
         (uses-input? r))]
    [(nat-exp natural) #f]
    [(nat-exp input)   #t]))

(provide (all-defined-out))
