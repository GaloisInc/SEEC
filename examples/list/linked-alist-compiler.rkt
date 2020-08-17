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

