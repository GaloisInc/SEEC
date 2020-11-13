#lang seec
(provide (all-defined-out))
(set-bitwidth 4)

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))

(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a set datastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar set-api
  (set         ::= list<integer>)
  (observation         ::= (member? integer) (or observation observation) (and observation observation) (not observation))   ; observations (set -> bool)
  (method         ::= (insert integer) (remove integer)) ; commands (set -> set)
  (interaction         ::= (seq method interaction) (if observation interaction interaction) nop) ; programs (set -> set)
  (dec        ::= (count integer) (prefix? set) (member? integer) (add dec dec) (minus dec dec) (or dec dec) (and dec dec) (not dec)) ; decoder on lists (list -> T)
  (dec-fun   ::= var-element var-value integer (if-val-eq integer dec-fun dec-fun) (if-el-eq integer dec-fun dec-fun) (add dec-fun dec-fun) (minus dec-fun))
  (dec-fold ::= (fold dec-fun integer))
  (dec-inner ::= (if observation dec-inner dec-inner) (seq method dec-inner)
                  (incr dec-inner) (decr dec-inner) nop)
  (dec-while ::= (while observation dec-inner dec-while) nop)
)


(define (insert s v)
  (set-api (cons ,v ,s)))

(define (remove s v)
  (match s
    [(set-api nil) (set-api nil)]
    [(set-api (cons x:integer r:set))
     (let ([new-tail (remove r v)])
       (if (equal? x v)
           new-tail
           (set-api (cons ,x ,new-tail))))]))

(define (buggy-remove s v)
  (match s
    [(set-api nil) (set-api nil)]
    [(set-api (cons x:integer r:set))
     (if (equal? x v)
         r
         (set-api (cons ,x ,(buggy-remove r v))))]))



; set-api.set -> set-api.set -> bool 
; true if there exists l+ s.t. vl@l+ == l
(define (interpret-prefix? l vl)
  (match vl
    [(set-api nil)
     #t]
    [(set-api (cons v:integer vl+:set))
     (match l
       [(set-api nil)
        #f]
       [(set-api (cons hd:integer l+:set))
        (if (equal? hd v)
            (interpret-prefix? l+ vl+)
            #f)])]))


; set-api.set -> set-api.integer -> bool
(define (interpret-member? s v)
  (match s
    [(set-api nil) #f]
    [(set-api (cons x:integer r:set))
     (if (equal? x v)
         #t
         (interpret-member? r v))]))

; set-api.set -> set-api.integer -> integer
(define (interpret-count s i)
  (match s
    [(set-api nil) 0]
    [(set-api (cons x:integer r:set))
     (if (equal? x i)
         (+ 1 (interpret-count r i))
         (interpret-count r i))]))

;; observation -> set -> bool
(define (interpret-observation p s)
  (match p
    [(set-api (not p+:observation))
     (not (interpret-observation p+ s))]
    [(set-api (and p1:observation p2:observation))
     (and (interpret-observation p1 s)
          (interpret-observation p2 s))]
    [(set-api (or p1:observation p2:observation))
     (or (interpret-observation p1 s)
         (interpret-observation p2 s))]    
    [(set-api (member? v:integer))
     (interpret-member? s v)]))

;; method -> set -> set
(define (interpret-method m s)
  (match m
    [(set-api (insert i:integer))
     (insert s i)]
    [(set-api (remove i:integer))
     (remove s i)]))

;; method -> set -> set
;; uses buggy-remove which just removes one instance of element i
(define (interpret-buggy-method m s)
  (match m
    [(set-api (insert i:integer))
     (insert s i)]
    [(set-api (remove i:integer))
     (buggy-remove s i)]))


;; interaction -> set -> set
(define (interpret-interaction i s)
  (match i
    [(set-api nop)
     s]
    [(set-api (seq m:method i+:interaction))
     (interpret-interaction i+ (interpret-method m s))]
    [(set-api (if o:observation i1:interaction i2:interaction))
     (if (interpret-observation o s)
         (interpret-interaction i1 s)
         (interpret-interaction i2 s))]))

;; interaction -> set -> set
(define (interpret-buggy-interaction i s)
  (match i
    [(set-api nop)
     s]
    [(set-api (seq m:method i+:interaction))
     (interpret-interaction i+ (interpret-buggy-method m s))]
    [(set-api (if o:observation i1:interaction i2:interaction))
     (if (interpret-observation o s)
         (interpret-interaction i1 s)
         (interpret-interaction i2 s))]))

(define-language set-lang
  #:grammar set-api
  #:expression interaction #:size 4
  #:context set #:size 3
  #:link cons
  #:evaluate (uncurry interpret-interaction))

(define-attack obs-int
  #:grammar set-api
  #:gadget interaction #:size 4
  #:evaluate-gadget interpret-interaction
  #:decoder observation #:size 2
  #:evaluate-decoder interpret-observation)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DEC
; dec is a decoder language where functionalities
; such as "count" are builtin
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 
;; dec -> set -> T
(define (interpret-dec p s)
  (match p
    [(set-api (count i:integer))
     (interpret-count s i)]
    [(set-api (add p1:dec p2:dec))
     (+ (interpret-dec p1 s)
        (interpret-dec p2 s))]
     [(set-api (minus p1:dec p2:dec))
      (- (interpret-dec p1 s)
         (interpret-dec p2 s))]
    [(set-api (not p+:dec))
     (not (interpret-dec p+ s))]
    [(set-api (and p1:dec p2:dec))
     (and (interpret-dec p1 s)
          (interpret-dec p2 s))]
    [(set-api (or p1:dec p2:dec))
     (or (interpret-dec p1 s)
         (interpret-dec p2 s))]
    [(set-api (prefix? vl:set))
     (interpret-prefix? s vl)]
    [(set-api (member? v:integer))
     (interpret-member? s v)]))

(define-attack dec-int
  #:grammar set-api
  #:gadget interaction #:size 3
  #:evaluate-gadget interpret-interaction
  #:decoder dec #:size 3
  #:evaluate-decoder interpret-dec)

(define-attack dec-buggy-int
  #:grammar set-api
  #:gadget interaction #:size 3
  #:evaluate-gadget interpret-buggy-interaction
  #:decoder dec #:size 3
  #:evaluate-decoder interpret-dec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DEC-WHILE
; dec-while is a decoder language consisting of
; a sequence of while (obs) dec-inner ...
; and dec-inner is a sequence of conditionals over observations,
; interaction over states and interaction (increment, decrement) with a counter 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; int -> dec-inner -> state -> (list int state)
(define (interpret-inner value i s)
  (match i
    [(set-api (if o:observation pi1:dec-inner pi2:dec-inner))
     (if (interpret-observation o s)
         (interpret-inner value pi1 s)
         (interpret-inner value pi2 s))]
    [(set-api (seq m:method i+:dec-inner))
     (interpret-inner value i+ (interpret-buggy-method m s))]
    [(set-api (incr i+:dec-inner))
     (interpret-inner (+ value 1) i+ s)]
    [(set-api (decr i+:dec-inner))
     (interpret-inner (- value 1) i+ s)]
    [(set-api nop)
     (list value s)
     ]))

;; int -> int -> dec-while -> state -> int
(define (interpret-while fuel value w s)
  (if (<= fuel 0)
      value
      (match w
        [(set-api (while o:observation pi:dec-inner pw:dec-while))
         (if (interpret-observation o s)
             (let ([cs (interpret-inner value pi s)])
               (interpret-while (- fuel 1) (first cs) w (second cs)))
               (interpret-while fuel value pw s))]
         [(set-api nop)
          value])))

;; dec-while -> state -> int
(define (interpret-dec-while w s)
  (interpret-while 4 0 w s))

(define-attack dec-while-int
  #:grammar set-api
  #:gadget interaction #:size 3
  #:evaluate-gadget interpret-interaction
  #:decoder dec-while #:size 4
  #:evaluate-decoder interpret-dec-while)

(define-attack dec-while-buggy-int
  #:grammar set-api
  #:gadget interaction #:size 3
  #:evaluate-gadget interpret-buggy-interaction
  #:decoder dec-while #:size 4
  #:evaluate-decoder interpret-dec-while)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DEC-FOLD
; dec-fold is a decoder language representing a function
; (\ e. \ v. p) being left-folded over the state
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; dec-fold -> int -> int -> int
(define (interpret-dec-fun p e v)
  (match p
    [(set-api var-element)
     e]
    [(set-api var-value)
     v]
    [(set-api i:integer)
     (bonsai->number i)]
    [(set-api (if-el-eq i:integer p1:dec-fun p2:dec-fun))
     (if (equal? (bonsai->number i) e)
         (interpret-dec-fun p1 e v)
         (interpret-dec-fun p2 e v))]
    [(set-api (if-val-eq i:integer p1:dec-fun p2:dec-fun))
     (if (equal? (bonsai->number i) v)
         (interpret-dec-fun p1 e v)
         (interpret-dec-fun p2 e v))]

    [(set-api (add p1:dec-fun p2:dec-fun))
     (+  (interpret-dec-fun p1 e v)
         (interpret-dec-fun p2 e v))]
    [(set-api (minus p+:dec-fun))
     (- (interpret-dec-fun p+ e v))]))

  

;; dec-fun -> set -> int -> int
(define (interpret-dec-fold+ f s v)
  (match s
    [(set-api nil)
     v]
    [(set-api (cons e:integer s+:set))
     (interpret-dec-fold+ f s+ (interpret-dec-fun f (bonsai->number e) v))]))

; Folds over state s using function p and default value 0
;; dec-fold -> set -> int
(define (interpret-dec-fold p s)
  (match p
    [(set-api (fold f:dec-fun i:integer))
     (interpret-dec-fold+ f s (bonsai->number i))]))

(define-attack dec-fold-int
  #:grammar set-api
  #:gadget interaction #:size 3
  #:evaluate-gadget interpret-interaction
  #:decoder dec-fold #:size 4
  #:evaluate-decoder interpret-dec-fold)

(define-attack dec-fold-buggy-int
  #:grammar set-api
  #:gadget interaction #:size 3
  #:evaluate-gadget interpret-buggy-interaction
  #:decoder dec-fold #:size 4
  #:evaluate-decoder interpret-dec-fold)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; EXAMPLES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Synthesize a decoder and a gadget implementing "not" using set
;; Expected:
;;; decoder: (set-api (member? 1))
;;; gadget: (set-api (if (member? 1) (seq (remove 1) nop) (seq (insert 1) nop)))
(define bool-funs (list (lambda (x) x) (lambda (x) (not x))))

(define empty-funs (list #f #f))


(define boolean-axioms
  (lambda (dec symbols x)
      (let ([id-s (first symbols)]
            [neg-s (second symbols)]
            [eq (lambda (r l) (equal?
                               (dec r)
                               (dec l)))])
        (and (equal? x (id-s x)) ; using equals on contexts to force id to be nop
             (eq x (neg-s (neg-s x)))
             (not (eq x (neg-s x)))))))


(define (test-spec-member)
    (display-related-gadgets (find-related-gadgets set-lang obs-int bool-funs) displayln))

(define (test-spec-member-axioms)
    (display-related-gadgets (find-related-gadgets set-lang obs-int empty-funs #:valid boolean-axioms) displayln))


; Natural numbers in set from definition of z and +
; NOTE: this would not work in buggy set
;; Expected:
;;; decoder: (count 0)
;;; gadget-z (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define nat-z-succ-funs (list (lambda (x) 0) (lambda (x) (+ 1 x))))

(define (test-spec-count)
    (display-related-gadgets (find-related-gadgets set-lang dec-int nat-z-succ-funs) displayln))



; Natural numbers in buggy set from definition of nat-pred and +1
; NOTE: this would not work in set
;; Expected:
;;; decoder: (count 0)
;;; gadget-pred (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define nat-pred-succ-funs (list (lambda (n) (max 0 (- n 1))) (lambda (n) (+ 1 n))))
(define nat-pred-succ-axioms
  (lambda (dec symbols x)
      (let ([pred-s (first symbols)]
            [succ-s (second symbols)]
            [eq (lambda (r l) (equal?
                               (dec r)
                               (dec l)))])
        (and (eq x (pred-s (succ-s x)))
             (not (eq x (succ-s x)))))))

(define (test-spec-buggy-count)
  (display-related-gadgets (find-related-gadgets set-lang dec-buggy-int nat-pred-succ-funs) displayln))

(define (test-spec-buggy-count-axioms)
  (display-related-gadgets (find-related-gadgets set-lang dec-buggy-int empty-funs #:valid nat-pred-succ-axioms) displayln))


; Integers in set from -1 and +1
; NOTE: this also works in buggy set
;; Expected:
;;; decoder (set-api (minus (count 0) (count 1))))
;;; gadget-pred (set-api (seq (insert 1) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define int-pred-succ-funs (list (lambda (n) (- n 1)) (lambda (n) (+ n 1))))

(define int-pred-succ-axioms
  (lambda (dec symbols x)
      (let ([pred-s (first symbols)]
            [succ-s (second symbols)]
            [eq (lambda (r l) (equal?
                               (dec r)
                               (dec l)))])
        (and (eq (succ-s (pred-s x)) (pred-s (succ-s x)))
             (not (eq x (pred-s x)))
             (not (eq x (succ-s x)))))))


(define (test-spec-count-int)
    (display-related-gadgets (find-related-gadgets set-lang dec-int int-pred-succ-funs) displayln))

(define (test-spec-count-int-axioms)
    (display-related-gadgets (find-related-gadgets set-lang dec-int empty-funs #:valid int-pred-succ-axioms) displayln))


; Natural numbers in sets from 0 and +1
; where the decoder is a fold over state
;; Expected:
;;; decoder (set-api (fold (add (if-el-eq 1 1 0) var-value) 0))
;;; gadget-pred (set-api (seq (remove 1) nop))
;;; gadget-succ (set-api (seq (insert 1) nop))
(define (test-spec-count-fold)
  (display-related-gadgets (find-related-gadgets set-lang dec-fold-int nat-z-succ-funs) displayln))

 
; Natural numbers in buggy-sets from nat-pred and +1
; where the decoder is a fold over state
;; Expected:
;;; decoder (set-api (fold (add (if-el-eq 1 1 0) var-value) 0))
;;; gadget-pred (set-api (seq (remove 1) nop))
;;; gadget-succ (set-api (seq (insert 1) nop))
(define (test-spec-buggy-count-fold)
    (display-related-gadgets (find-related-gadgets set-lang dec-fold-buggy-int nat-pred-succ-funs) displayln))


; Natural numbers in buggy-sets from nat-pred and +1
; where the decoder is a sequence of while observation interaction with a counter
; NOTE: this takes a long time with larger set. while is bounded by fuel in interpret-while-d.
; NOTE: this would NOT work on non-buggy set
;; Expected:
;;; decoder (set-api (while (member? 0) (seq (remove 0) (incr nop)) (while (member? 0) nop nop))
;;; gadget-pred (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-buggy-count-while)
    (display-related-gadgets (find-related-gadgets set-lang dec-while-buggy-int nat-pred-succ-funs) displayln))

; WARNING: THIS IS SLOW (30 min)
;; Expected:
;;; decoder (set-api (while (or (member? 1) (and (member? 0) (member? 0))) (if (not (member? 1)) (seq (remove 0) (incr nop)) (seq (remove 1) (decr nop))) nop)
;;; gadget-pred (set-api (seq (insert 1) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-buggy-count-while-int)
    (display-related-gadgets (find-related-gadgets set-lang dec-while-buggy-int int-pred-succ-funs) displayln))


; This should fail, as non-buggy version cannot produce something equivalent to "count" using dec-while
; (and likewise with integer's spec-pred and spec-succ)
(define (test-spec-count-while-nat)
    (display-related-gadgets (find-related-gadgets set-lang dec-while-int nat-z-succ-funs) displayln))



#| Some notes about a future multi-typed version of find-related gadget

What we have: a list of individual specifications of type
\x. S_i x

s.t. forall s
   S_i D s == D (G_i s)


D can be parameterized by the type of what we are decoding:
assume S_i takes 2 imput and returns one (e.g. +), 
for type S/G: t -> t'

S_i (D_t s) == D_t' (G_i s)


We also want to be able to give relation specifcations between multiple S.
assume Si : ti -> ti' and Sj : tj -> tj'


\S. \x:t. F S0 ... Sn x

then it should be the case that forall s, 
     F G_0  ...  G_n (D_t s)

e.g. \S_s S_p x, S_s S_p x = S_p S_s x
which goes to 
  (G_s G_p x) = (G_p G_s x)
rather than 

find_related_gadgets: language -> list(n) specification -> (bool x list(n) nat x nat) -> rel_spec -> list(n) gadget

synthesize
#:forall x
#:guarantee 
(and (decoder_i' (gadget_i set) = spec_i (decoder_i set))
     ...
     rel_spec list_gadget set)


|#
