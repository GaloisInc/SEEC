#lang seec
(require racket/format)
(require (file "list-lang.rkt"))
(require (file "linked-list-lang.rkt"))
(provide (all-defined-out))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Association list API
;
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar alist-api
  (value   ::= integer)
  (key     ::= integer)
  (alist ::= (key value alist) empty)
  (method  ::= (add-elem key value) reset)
  (interaction ::= (method interaction) empty)
  (observation ::= (lookup key) empty?)
  (complete-interaction ::= (interaction observation)))

(define (empty?-alist al)
  (match al
    [(alist-api empty) #t]
    [ _ #f]))

; returns either the value pointed to by the key in the association list al, or
; #f if the key does not appear in the list
(define (lookup-alist k al)
    (match al
      [(alist-api empty) #f]
      [(alist-api (k+:key v+:value al+:alist))
       (if (equal? k k+)
           v+
           (lookup-alist k al+))]))

(define (ci->i-alist ci)
  (match ci
    [(alist-api (intss:interaction o:observation))
     intss]))

(define (ci->o-alist ci)
  (match ci
    [(alist-api (intss:interaction o:observation))
     o]))


(define (interpret-interaction-alist ints al)
  (match ints
    [(alist-api empty) al]
    [(alist-api (reset ints+:interaction))
     (interpret-interaction-alist ints+ (alist-api empty))]
    [(alist-api ((add-elem k:key v:value) ints+:interaction))
     (interpret-interaction-alist ints+ (alist-api (,k ,v ,al)))]
    ))

(define (interpret-observation-alist o al)
  (match o
    [(alist-api empty?)
     (empty?-alist al)]
    [(alist-api (lookup k:key))
     (lookup-alist k al)]))

(define (interpret-complete-interaction-alist ci al)
  (interpret-observation-alist (ci->o-alist ci)
                               (interpret-interaction-alist (ci->i-alist ci) al)))

(define-language alist-lang
  #:grammar alist-api
  #:expression alist #:size 6
  #:context complete-interaction #:size 4
  #:link cons
  #:evaluate (uncurry interpret-complete-interaction-alist))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Utility functions for alist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; True if i is a key or a value in alist al
(define (alist-in al i)
  (match al
    [(alist-api empty) #f]
    [(alist-api (k+:key v+:value al+:alist))
     (if (or (equal? i k+) (equal? i v+))
;       (if (or (equal? i (bonsai->number k+)) (equal? i (bonsai->number v+)))
           #t
           (alist-in al+ i))]))

(define (complete-interaction-alist-lookup ints)
  (match ints
    [(alist-api (intss:interaction (lookup k:key)))
     k]
    [_
     #f]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (pp-alist al)
  (match al
    [(alist-api empty) ""]
    [(alist-api (k+:key v+:value al+:alist))
     (format "(~a, ~a)\n~a" (~a k+ #:width 5 #:align 'center) (~a v+ #:width 5 #:align 'center) (pp-alist al+))]))

(define (display-alist al)
  (displayln (pp-alist al)))


(define (display-language-witness-alist lw)
  (let ([lwl (unpack-language-witness lw)])
        (displayln (format "Association list\n~ahas behavior ~a\nunder complete-interaction ~a~n" (pp-alist (first lwl)) (fourth lwl) (second lwl)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (alist-demo)
  (begin
    (define store (alist-api (0 1 (2 3 (4 5 empty)))))
    (display-alist store)
    (define interact (alist-api ((add-elem 7 8) empty)))
    (define store+i (interpret-interaction-alist interact store))
    (display-alist store+i)
    (displayln (lookup-alist (alist-api 2) store+i))
    (displayln (lookup-alist (alist-api 7) store+i))))

