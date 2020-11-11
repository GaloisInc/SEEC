#lang seec

(require (file "list-lang.rkt")
         (file "linked-list-lang.rkt")
         (file "alist-lang.rkt"))
(provide (all-defined-out))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Implementing Association List using Linked List
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (alist->list al)
  (match al
    [(alist-api empty) (list-api empty)]
    [(alist-api (k:key v:value al+:alist))
     (list-api (,k (,v ,(alist->list al+))))]))

(define (alist->ll al) (list->ll (alist->list al)))

(define (alist->ll-i ints)
  (match ints
    [(alist-api empty)
     (linked-list empty)]
    [(alist-api ((add-elem k:key v:value) ints+:interaction))
     (linked-list ((mcons ,v) ((mcons ,k) ,(alist->ll-i ints+))))]
    [(alist-api (reset ints+:interaction))
     (linked-list (mnil ,(alist->ll-i ints+)))]))

(define (alist->ll-o o)
  (match o
    [(alist-api (lookup k:key))
     (linked-list (lookup ,k))]
    [(alist-api empty?)
     (linked-list empty?)]))


; input: an alist complete interaction
; output: a linked-list complete interaction
(define (alist->ll-ci ci)
  (let ([i-ll (alist->ll-i (ci->i-alist ci))]
        [o-ll (alist->ll-o (ci->o-alist ci))])
    (linked-list (,i-ll ,o-ll))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Compiler from abstract alist to linked-list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (alist-ll-ci-equal? ci-alist ci-ll)
  (equal? (alist->ll-ci ci-alist) ci-ll))

(define-compiler alist-to-ll-compiler
  #:source alist-lang
  #:target linked-list-lang
  #:behavior-relation equal?
  #:context-relation alist-ll-ci-equal?
  #:compile alist->ll)
  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Compiler from abstract alist to linked-list
; allowing for attacks in linked-list interaction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (alist-ll-ci-equal?-minus-attack ci-alist ci-ll)
  (complete-interaction-equal?-minus-attack (alist->ll-ci ci-alist) ci-ll))

(define-compiler alist-to-attacked-ll-compiler
  #:source alist-lang
  #:target attacked-linked-list-lang
  #:behavior-relation equal?
  #:context-relation alist-ll-ci-equal?-minus-attack
  #:compile alist->ll)




; Test nontermination of nil-state on symbolic states

(define (test-nil-state)
  (define x0 (alist-api key 1))
  (define x1 (alist-api key 1))
  (define x2 (alist-api key 1))
  (define x3 (alist-api key 1))
  (define x4 (alist-api key 1))
  (define v0 (alist-api value 1))
  (define v1 (alist-api value 1))
  (define v2 (alist-api value 1))
  (define v3 (alist-api value 1))
  (define v4 (alist-api value 1))

  #;(define lst (alist-api (0 100 (1 101 (2 102 (3 103 (4 104 empty)))))))
  #;(define lst (alist-api (,x0 ,v0 (,x1 ,v1 (,x2 ,v2 (,x3 ,v3 (,x4 ,v4 empty)))))))
  (define lst (alist-api alist 6))

  ; Compile a (possibly symbolic association list to a linked list, to ensure
  ; the starting list is well-formed
  (define s (alist->ll lst))
  (display-state s)

  ; Change the free pointer to a symbolic pointer
  #;(define new-fp 9)
  #;(define-symbolic new-fp integer?)
  (define new-fp (linked-list pointer 1))
  (define a (linked-list (change-free-pointer ,new-fp)))
  (define s+ (interpret-attack-ll a s))
  (display-state s+)

  (printf "Computed nil-state of s+: ~a~n" (nil-state s+))
  
  (define s++ (interpret-interaction-ll (linked-list ((mcons 3) empty)) s+))
  (printf "Computed (cons-state 3 s+: ~a~n" s++)

  (printf "Trying to do nil-state of s++~n")
  (define s+++ (nil-state s++))
  (printf "Done with nil-state of s++~n")
  )
(test-nil-state)
