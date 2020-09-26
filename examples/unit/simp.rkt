#lang seec
(require (file "lib.rkt"))

(provide (all-defined-out))
; simple arithmetic expression with a single variable
; testing grammar and language definitions


(define-grammar simp
  (num ::= z (s num))
  (op ::= + *)
  (exp ::= (op exp exp) var num))


(define (interp-binop op n1 n2)
  (match op
  [(simp +)
   (+ n1 n2)]
  [(simp *)
   (* n1 n2)]))

(define (eval-num num)
  (match num
    [(simp z)
     0]
    [(simp (s n:num))
     (+ (eval-num n) 1)]))

; num -> exp -> racket integer
(define (eval-simp var exp)
  (match exp
    [(simp (o:op e1:exp e2:exp))
     (interp-binop o (eval-simp var e1) (eval-simp var e2))]
    [(simp n:num)
     (eval-num n)]
    [(simp var)
     (eval-num var)]))

(define (eval-simp-closed exp)
  (eval-simp #f exp))



(define simp-term-0
  (simp z))
(define simp-term-1
  (simp (s z)))
(define simp-term-2
  (simp (+ (s z) (s z))))
(define simp-term-3
  (simp (+ (* (s z) (s (s z))) (s z))))
(define simp-term-4
  (simp (+ var (* (s z) var))))


(define test-eval-simp-1
  (eval-simp-closed simp-term-1))
(define test-eval-simp-2
  (eval-simp-closed simp-term-2))
(define test-eval-simp-3
  (eval-simp-closed simp-term-3))
(define test-eval-simp-4
  (eval-simp simp-term-1 simp-term-4))

(define-language SIMP
  #:grammar simp
  #:expression exp #:size 4
  #:context num #:size 4
  #:link cons
  #:evaluate (uncurry eval-simp))

(define-language SIMP-NOBOUND
  #:grammar simp
  #:expression exp 
  #:context num
  #:link cons
  #:evaluate (uncurry eval-simp))

(define SIMP-BACKTOBOUND
  (refine-language SIMP-NOBOUND #:expression-bound 4 #:context-bound 4))

(define-compiler SIMP-REFINED
  #:source SIMP
  #:target SIMP-BACKTOBOUND
  #:behavior-relation equal?
  #:context-relation equal?
  #:compile id)


; find additive gadget (i.e. some e s.t. m + c = b)
(define (add-spec m p b)
  (match p
    [(cons c e)
     (equal? (+ m (eval-num c)) b)]))
  
                  

; find multiplicative gadget (i.e. some e s.t. m * c = b)
(define (mult-spec m p b)
  (match p
    [(cons c e)
     (equal? (* m (eval-num c)) b)]))

(define simp-mult-term (simp (* (s (s (s z))) var)))
(mult-spec 3 (cons simp-term-1 simp-mult-term) 3)

;(find-gadget SIMP (mult-spec 2))
