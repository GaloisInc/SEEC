#lang seec
(require (file "lib.rkt"))
(require (file "simp+integer.rkt"))
(provide (all-defined-out))

; Testing grammar and language definitions with natural numbers
; lib


; SIMP with natural
(define-grammar simp+natural
  (num ::= natural)
  (op ::= + *)
  (exp ::= (op exp exp) var num))

; returns the number of ops in exp e
(define (num-ops e)
  (match e
    [(simp+natural (o:op e1:exp e2:exp))
     (+ 1 (+ (num-ops e1) (num-ops e2)))]
    [(simp+natural n:num)
     0]
    [(simp+natural var)
     0]))

(define (interp-binop op n1 n2)
  (match op
  [(simp+natural +)
   (+ n1 n2)]
  [(simp+natural *)
   (* n1 n2)]))


; exp -> racket natural
(define (eval-simp+natural v exp)
  (match exp
    [(simp+natural (o:op e1:exp e2:exp))
     (interp-binop o (eval-simp+natural v e1) (eval-simp+natural v e2))]
    [(simp+natural n:num)
     (bonsai->number n)]
    [(simp+natural var)
     (bonsai->number v)]))

(define (eval-simp+natural-closed exp)
  (eval-simp+natural #f exp))

(define-language SIMP+NATURAL
  #:grammar simp+natural
  #:expression exp #:size 4
  #:context num #:size 4
  #:link cons
  #:evaluate (uncurry eval-simp+natural))



(define simp+natural-term-1
  (simp+natural 1))
(define simp+natural-term-2
  (simp+natural (+ 3 5)))
(define simp+natural-term-3
  (simp+natural (+ (* 1 2) 1)))
(define simp+natural-term-4
  (simp+natural (+ var (* 1 var))))


(define test-eval-simp+natural-1
  (eval-simp+natural-closed simp+natural-term-1))
(define test-eval-simp+natural-2
  (eval-simp+natural-closed simp+natural-term-2))
(define test-eval-simp+natural-3
  (eval-simp+natural-closed simp+natural-term-3))
(define test-eval-simp+natural-4
  (eval-simp+natural simp+natural-term-1 simp+natural-term-4))

(define-compiler SIMP-NAT-TO-INTEGER
  #:source SIMP+NATURAL
  #:target SIMP+INTEGER
  #:behavior-relation equal?
  #:compile id)

(define-compiler SIMP-INTEGER-TO-NAT
  #:source SIMP+INTEGER
  #:target SIMP+NATURAL
  #:behavior-relation equal?
  #:compile id)



;;; Query testing
(define test-cc-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER))
   "find-changed-component query"))

(define test-cc-arg-count-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER #:count 3))
  "count argument to find-changed-component"))


(define test-cc-arg-source-exp-bound-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:source-expression-bound 6))
  "source-expression-bound argument to find-changed-component"))
                           


(define test-cc-arg-source-exp-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:source-expression-where (lambda (v1) (>= (num-ops v1) 3))))
    "source-expression-where argument to find-changed-component"))

(define test-cc-arg-source-context-bound-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:source-context-bound 2))
   "source-context-bound argument to find-changed-component"))

  
(define test-cc-arg-source-context-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:source-context-where (lambda (v1 c1) (equal? (bonsai->number c1) 0))))
   "source-context-where argument to find-changed-component"))

(define test-cc-arg-target-context-bound-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:target-context-bound 2)) 
   "target-context-bound argument to find-changed-component"))
  
(define test-cc-arg-target-context-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                                  #:target-context-where (lambda (v1 c2) (equal? (bonsai->number c2) 1))))
  "target-context-where argument to find-changed-component"))

(define test-cc-arg-source-behavior-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:source-behavior-where (lambda (v1 c1 c2 b1) (equal? b1 0))))
   "source-behavior-where argument to find-changed-component"))

(define test-cc-arg-target-behavior-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:target-behavior-where (lambda (v1 c1 c2 b2) (<= 1000 b2))))
   "target-behavior-where argument to find-changed-component"))

(define test-cc-all-args-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-changed-component SIMP-NAT-TO-INTEGER
                           #:source-expression-bound 6
                           #:source-expression-where (lambda (v1) (>= (num-ops v1) 3))
                           #:source-context-bound 2
                           #:source-context-where (lambda (v1 c1) (equal? (bonsai->number c1) 0))
                           #:target-context-bound 2
                           #:target-context-where (lambda (v1 c2) (equal? (bonsai->number c2) 1))
                           #:source-behavior-where (lambda (v1 c1 c2 b1) (equal? b1 0))
                           #:target-behavior-where (lambda (v1 c1 c2 b2) (<= 1000 b2))))
    "all arguments to find-changed-component"))
                           


;; there should be weird-component (any negative context)
(define test-wc-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER))
   "find-weird-component query"))

(define test-wc-arg-count-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER #:count 3))
  "count argument to find-weird-component"))


(define test-wc-arg-source-exp-bound-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:source-expression-bound 6))
  "source-expression-bound argument to find-weird-component"))
                           


(define test-wc-arg-source-exp-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:source-expression-where (lambda (v1) (>= (num-ops v1) 3))))
    "source-expression-where argument to find-weird-component"))

(define test-wc-arg-source-context-bound-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:source-context-bound 2))
   "source-context-bound argument to find-weird-component"))

  
(define test-wc-arg-source-context-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:source-context-where (lambda (v1 c1) (equal? (bonsai->number c1) 0))))
   "source-context-where argument to find-weird-component"))

(define test-wc-arg-target-context-bound-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:target-context-bound 2)) 
   "target-context-bound argument to find-weird-component"))
  
(define test-wc-arg-target-context-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                                  #:target-context-where (lambda (v1 c2) (equal? (bonsai->number c2) -1))))
  "target-context-where argument to find-weird-component"))

(define test-wc-arg-target-context-where-fail-nat-to-integer
  (list
   (lambda (r) (not (r)))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                                  #:target-context-where (lambda (v1 c2) (equal? (bonsai->number c2) 1))))
  "target-context-where argument to find-weird-component should make this query fail"))


(define test-wc-arg-source-behavior-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:source-behavior-where (lambda (v1 c1 c2 b1) (equal? b1 0))))
   "source-behavior-where argument to find-weird-component"))

(define test-wc-arg-target-behavior-where-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:target-behavior-where (lambda (v1 c1 c2 b2) (<= 1000 b2))))
   "target-behavior-where argument to find-weird-component"))

(define test-wc-all-args-nat-to-integer
  (list
   (lambda (r) (r))
   (thunk (find-weird-component SIMP-NAT-TO-INTEGER
                           #:source-expression-bound 6
                           #:source-expression-where (lambda (v1) (>= (num-ops v1) 3))
                           #:source-context-bound 2
                           #:source-context-where (lambda (v1 c1) (equal? (bonsai->number c1) 0))
                           #:target-context-bound 2
                           #:target-context-where (lambda (v1 c2) (equal? (bonsai->number c2) 1))
                           #:source-behavior-where (lambda (v1 c1 c2 b1) (equal? b1 0))
                           #:target-behavior-where (lambda (v1 c1 c2 b2) (<= 1000 b2))))
    "all arguments to find-weird-component"))
  
;; there shouldn't be weird components
;; WARNING: this takes a while to verify
(define (test-wc-integer-to-nat) (unpack-language-witnesses (find-weird-component SIMP-INTEGER-TO-NAT)))

