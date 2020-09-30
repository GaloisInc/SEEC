#lang seec
(provide (all-defined-out))
(set-bitwidth 4)

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a set datastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar set-api
  (set         ::= list<integer>)
  (observation         ::= (member? integer) (or observation observation) (and observation observation) (not observation))   ; observationervations (set -> bool)
  (method         ::= (insert integer) (remove integer)) ; commands (set -> set)
  (interaction         ::= (seq method interaction) (if observation interaction interaction) nop) ; programs (set -> set)
  (dec        ::= (count integer) (prefix? set) (member? integer) (add dec dec) (minus dec dec) (or dec dec) (and dec dec) (not dec)) ; decoder on lists (list -> T)
  (dec-fun   ::= var-element var-value integer (if-val-eq integer dec-fun dec-fun) (if-el-eq integer dec-fun dec-fun) (add dec-fun dec-fun) (minus dec-fun))
  (dec-fold ::= (fold dec-fun integer))
  (dec-inner ::= (if observation dec-inner dec-inner) (seq method dec-inner)
                  (inc dec-inner) (dec dec-inner) nop)
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
    #|
    [(set-api (not p+:observation))
     (not (interpret-observation p+ s))]
    [(set-api (and p1:observation p2:observation))
     (and (interpret-observation p1 s)
          (interpret-observation p2 s))]
    [(set-api (or p1:observation p2:observation))
     (or (interpret-observation p1 s)
         (interpret-observation p2 s))]
    |#
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
    [(set-api (inc i+:dec-inner))
     (interpret-inner (+ value 1) i+ s)]
    [(set-api (dec i+:dec-inner))
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
(define (interpret-while-d w s)
  (interpret-while 4 0 w s))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DEC-FOLD
; dec-fold is a decoder language representing a function
; (\ e. \ v. p) being left-folded over the state (with default value 0)
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; EXAMPLES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Synthesize a decoder and a gadget implementing "not" using set
;; Expected:
;;; decoder: (set-api (member? 1))
;;; gadget: (set-api (if (member? 1) (seq (remove 1) nop) (seq (insert 1) nop)))
(define (test-spec-member)
  (begin
    (define spec (lambda (x) (not x)))
    (define decoder (set-api observation 2))
    (define gadget (set-api interaction 4))
    (define set (set-api set 3))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (equal?
                               (interpret-dec decoder (interpret-interaction gadget set))
                               (spec (interpret-dec decoder set))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget (concretize gadget sol))
          (displayln "gadget...")
          (displayln c-gadget)
          (define c-decoder (concretize decoder sol))
          (displayln "decoder...")
          (displayln c-decoder)))
    ))

; Natural numbers in set from definition of z and +
; NOTE: this would not work in buggy set
;; Expected:
;;; decoder: (count 0)
;;; gadget-z (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-count)
  (begin
    (define spec-z (lambda n 0))
    (define spec-succ (lambda (n) (+ 1 n)))
    (define decoder (set-api dec 2))
    (define gadget-z (set-api interaction 3))
    (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-dec decoder (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-dec decoder set)))
                                   (equal?
                                    (interpret-dec decoder (interpret-interaction gadget-z set))
                                    (spec-z (interpret-dec decoder set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-z (concretize gadget-z sol))
          (displayln "gadget z and succ...")
          (displayln c-gadget-z)
          (displayln c-gadget-succ)
          (define c-decoder (concretize decoder sol))
          (displayln "decoder...")
          (displayln c-decoder)))))


; Natural numbers in buggy set from definition of nat-pred and +1
; NOTE: this would not work in set
;; Expected:
;;; decoder: (count 0)
;;; gadget-pred (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-buggy-count)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define decoder (set-api dec 2))
    (define gadget-pred (set-api interaction 3))
   (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set

                 #:guarantee (assert
                              (and (equal?
                                    (interpret-dec decoder (interpret-buggy-interaction gadget-succ set))
                                    (spec-succ (interpret-dec decoder set)))
                                   (equal?
                                    (interpret-dec decoder (interpret-buggy-interaction gadget-pred set))
                                    (spec-pred (interpret-dec decoder set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (define c-decoder (concretize decoder sol))
          (displayln "decoder...")
          (displayln c-decoder))))
  )


; Integers in set from -1 and +1
; NOTE: this also works in buggy set
;; Expected:
;;; decoder (set-api (minus (count 0) (count 1))))
;;; gadget-pred (set-api (seq (insert 1) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-count-int)
  (begin
    (define spec-pred (lambda (n) (- n 1)))
    (define spec-succ (lambda (n) (+ n 1)))
   (define decoder (set-api dec 3))
    (define gadget-pred (set-api interaction 3))
   (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
  (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-dec decoder (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-dec decoder set)))
                                   (equal?
                                    (interpret-dec decoder (interpret-interaction gadget-pred set))
                                    (spec-pred (interpret-dec decoder set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-set (concretize set sol))
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (define c-decoder (concretize decoder sol))
          (displayln "decoder...")
          (displayln c-decoder)))))

          
; Natural numbers in sets from 0 and +1
; where the decoder is a fold over state
;; Expected:
;;; decoder (set-api (fold (add (if-el-eq 1 1 0) var-value) 0))
;;; gadget-pred (set-api (seq (remove 1) nop))
;;; gadget-succ (set-api (seq (insert 1) nop))
(define (test-spec-count-fold)
  (begin
    (define spec-z 0)
    (define spec-succ (lambda (n) (+ 1 n)))
    (define decoder (set-api dec-fold 4))
    (define gadget-z (set-api interaction 3))
    (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-dec-fold decoder (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-dec-fold decoder set)))
                                   (equal?
                                    (interpret-dec-fold decoder (interpret-interaction gadget-z set))
                                    spec-z)))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-z (concretize gadget-z sol))
          (displayln "gadget z and succ...")
          (displayln c-gadget-z)
          (displayln c-gadget-succ)
          (define c-decoder (concretize decoder sol))
          (displayln "decoder...")
          (displayln c-decoder)))))


; Natural numbers in buggy-sets from nat-pred and +1
; where the decoder is a fold over state
;; Expected:
;;; decoder (set-api (fold (add (if-el-eq 1 1 0) var-value) 0))
;;; gadget-pred (set-api (seq (remove 1) nop))
;;; gadget-succ (set-api (seq (insert 1) nop))
(define (test-spec-buggy-count-fold)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define decoder (set-api dec-fold 4))
    (define gadget-pred (set-api interaction 3))
    (define gadget-succ (set-api interaction 3))
   (define set (set-api set 5))
   (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-dec-fold decoder (interpret-buggy-interaction gadget-succ set))
                                    (spec-succ (interpret-dec-fold decoder set)))
                                   (equal?
                                    (interpret-dec-fold decoder (interpret-buggy-interaction gadget-pred set))
                                    (spec-pred (interpret-dec-fold decoder set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin

          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (define c-decoder (concretize decoder sol))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (displayln "decoder...")
          (displayln c-decoder)))))


; Natural numbers in buggy-sets from nat-pred and +1
; where the decoder is a sequence of while observation interaction with a counter
; NOTE: this takes a long time with larger set. while is bounded by fuel in interpret-while-d.
; NOTE: this would NOT work on non-buggy set
;; Expected:
;;; decoder (set-api (while (member? 0) (seq (remove 0) (inc nop)) (while (member? 0) nop nop))
;;; gadget-pred (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-buggy-count-while-nat)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define decoder (set-api dec-while 4))
    (define gadget-pred (set-api interaction 3))
   (define gadget-succ (set-api interaction 3))
    (define set (set-api set 3))
  (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-while-d decoder (interpret-buggy-interaction gadget-succ set))
                                    (spec-succ (interpret-while-d decoder set)))
                                   (equal?
                                    (interpret-while-d decoder (interpret-buggy-interaction gadget-pred set))
                                    (spec-pred (interpret-while-d decoder set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (define c-decoder (concretize decoder sol))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)          
          (displayln "decoder...")
          (displayln c-decoder)))))

; This should fail, as non-buggy version cannot produce something equivalent to "count" using dec-while 
(define (test-spec-count-while-nat)
  (begin
    (define spec-z 0)
    (define spec-succ (lambda (n) (+ 1 n)))
    (define decoder (set-api dec-while 4))
    (define gadget-z (set-api interaction 3))
    (define gadget-succ (set-api interaction 3))
    (define set (set-api set 3))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-while-d decoder (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-while-d decoder set)))
                                   (equal?
                                    (interpret-while-d decoder (interpret-interaction gadget-z set))
                                    spec-z)))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-z (concretize gadget-z sol))
          (displayln "gadget z and succ...")
          (displayln c-gadget-z)
          (displayln c-gadget-succ)
          (define c-decoder (concretize decoder sol))
          (displayln "decoder...")
          (displayln c-decoder)))))
