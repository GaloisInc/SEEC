#lang seec
; Testing grammar and language definitions
; lib
(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))


; SIMP
(define-grammar simp
  (num ::= z (s num))
  (op ::= + *)
  (exp ::= (op num num) num))

(define-grammar simp+integer
  (num ::= integer)
  (op ::= + *)
  (exp ::= (op num num)))

(define-grammar simp+natural
  (num ::= natural)
  (op ::= + *)
  (exp ::= (op num num)))


(define (interp-binop op n1 n2)
  (match op
  [(lang +)
   (+ n1 n2)]
  [(lang *)
   (* n1 n2)]))

(define (eval-simp exp)
  (match exp
    [(simp (o:op n1:num n2:num))
     (interp-binop op (eval-simp n1) (eval-simp n2))]
    [(simp z) 0]
    [(simp (s n:num))
     (+ 1 (eval-simp n))]
    ))

(define test-simp-1
  (eval-simp (simp (+ (* (s z) (s (s z))) z))))
     
     
     

; STR
(define-grammar str+string
  (str ::= string)
  (binop ::= append)
  (exp ::= (binop str str)))

(define-grammar str+char
  (str ::= (char str))
  (binop ::= append)
  (exp ::= (binop str str)))
