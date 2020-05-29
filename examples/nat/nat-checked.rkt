#lang seec

(define (checked-compile nexp)
  (match nexp
    ; Check that inputs are non-negative!
    [(nat-exp input)
     (int-exp (neg? input 0 input))]
    [(nat-exp n:natural)
     (int-exp ,n)]
    [(nat-exp (+ l:exp r:exp))
     (int-exp (+ ,(checked-compile l)
                 ,(checked-compile r)))]))

(define-compiler checked-nat-to-int
  #:source nat-lang
  #:target int-lang
  #:behavior-relation equal?
  #:compile checked-compile)

(require "nat-compile.rkt")

(provide (all-defined-out)
         (all-from-out "nat-compile.rkt"))
