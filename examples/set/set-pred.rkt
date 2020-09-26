#lang seec
(provide (all-defined-out))

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a set datastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar set-api
  (value       ::= integer boolean)
  (vallist     ::= list<value>)
  (set         ::= list<integer>)
  (trace       ::= list<boolean>)
  (pred-inner ::= (if obs pred-inner pred-inner) (seq met pred-inner)
                  (inc pred-inner) (dec pred-inner) nop)
  (pred-while ::= (while observation pred-inner pred-while) nop)             
  (pred-fold   ::= var-element var-value integer (if-val-eq integer pred-fold pred-fold) (if-el-eq integer pred-fold pred-fold) (add pred-fold pred-fold) (minus pred-fold)) 
  (pred        ::= (count integer) (prefix? set) (member? integer) (add pred pred) (minus pred pred) (or pred pred) (and pred pred) (not pred)) ; predicate on lists (list -> T)
  (observation         ::= (member? integer) (or observation) (and observation observation) (not observation))   ; observationervations (set -> bool)
  (method         ::= (insert integer) (remove integer)) ; commands (set -> set)
  (interaction         ::= (seq method interaction) (if observation interaction interaction) nop) ; programs (set -> set)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an abstract semantics of operations on sets
;
; * The semantics will represent a set as a list of unique values.
; * Inserting and removing an element inserts or removes the corresponding
;   element from the list.
; * member? searches the list for the requested element
; * select *non-deterministically* chooses and element from the list to return
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Convenience functions for manipulating lists
(define (head s)
  (match s
    [(set-api nil) (assert #f)]
    [(set-api (cons x:any any)) x]))

(define (tail s)
  (match s
    [(set-api nil) (assert #f)]
    [(set-api (cons any rest:any)) rest]))

(define (abstract-insert s v)
  (set-api (,v ,(abstract-remove s v))))

(define (abstract-remove s v)
  (match s
    [(set-api nil) (set-api nil)]
    [(set-api (cons x:value r:vallist))
     (let ([new-tail (abstract-remove r v)])
       (if (equal? x v)
           new-tail
           (set-api (cons ,x ,new-tail))))]))

(define (abstract-member? s v)
  (match s
    [(set-api nil) (set-api #f)]
    [(set-api (cons x:value r:vallist))
     (if (equal? x v)
         (set-api #t)
         (abstract-member? r v))]))

(define (abstract-select s)
  (match s
    [(set-api nil)      (set-api #f)]
    [(set-api vallist)  (abstract-select-nondet s)]))

; The (nondet!) construct introduces a non-deterministic choice
(define (abstract-select-nondet s)
  (match s
    [(set-api (cons x:value nil)) x]
    [(set-api (cons x:value r:vallist))
     (if (nondet!) x (abstract-select-nondet r))]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an concrete implementation of the set API
;
; * Like the abstract semantics, the implementation represents sets as lists of
;   elements in the set.
; * Inserting and removing an element inserts or removes the corresponding
;   element from the list. If an item is in the list already, inserting it will
;   add a second occurence. Removing an item will remove all occurences of the
;   item in the list.
; * member? searches the list for the requested element
; * select returns the most-recently inserted item (the item at the head of the
;   list
;
; Also define a "buggy" implementation of the API where remove is implemented
; incorrectly and only removes the first instance of element.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (concrete-insert s v)
  (set-api (cons ,v ,s)))

(define (concrete-remove s v)
  (match s
    [(set-api nil) (set-api nil)]
    [(set-api (cons x:value r:vallist))
     (let ([new-tail (concrete-remove r v)])
       (if (equal? x v)
           new-tail
           (set-api (cons ,x ,new-tail))))]))

(define (buggy-concrete-remove s v)
  (match s
    [(set-api nil) (set-api nil)]
    [(set-api (cons x:value r:vallist))
     (if (equal? x v)
         r
         (set-api (cons ,x ,(buggy-concrete-remove r v))))]))

(define (concrete-member? s v)
  (match s
    [(set-api nil) (set-api #f)]
    [(set-api (cons x:value r:vallist))
     (if (equal? x v)
         (set-api #t)
         (concrete-member? r v))]))

(define (concrete-select s)
  (match s
    [(set-api nil) (set-api #f)]
    [(set-api (cons x:value vallist)) x]))


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




;; pred -> set -> T
(define (interpret-pred p s)
  (match p
    [(set-api (count i:integer))
     (interpret-count s i)]
    [(set-api (add p1:pred p2:pred))
     (+ (interpret-pred p1 s)
        (interpret-pred p2 s))]
     [(set-api (minus p1:pred p2:pred))
      (- (interpret-pred p1 s)
         (interpret-pred p2 s))]
    [(set-api (not p+:pred))
     (not (interpret-pred p+ s))]
    [(set-api (and p1:pred p2:pred))
     (and (interpret-pred p1 s)
          (interpret-pred p2 s))]
    [(set-api (or p1:pred p2:pred))
     (or (interpret-pred p1 s)
         (interpret-pred p2 s))]
    [(set-api (prefix? vl:set))
     (interpret-prefix? s vl)]
    [(set-api (member? v:value))
     (interpret-member? s v)]))

;;; WHILE pred language
;; int -> pred-inner -> state -> (list int state)
(define (interpret-inner value i s)
  (match i
    [(set-api (if o:observation pi1:pred-inner pi2:pred-inner))
     (if (interpret-observation o s)
         (interpret-inner value pi1 s)
         (interpret-inner value pi2 s))]
    [(set-api (seq m:method i+:pred-inner))
     (interpret-inner value i+ (interpret-buggy-method m s))]
    [(set-api (inc i+:pred-inner))
     (interpret-inner (+ value 1) i+ s)]
    [(set-api (dec i+:pred-inner))
     (interpret-inner (- value 1) i+ s)]
    [(set-api nop)
     (list value s)
     ]))

;; int -> int -> pred-while -> state -> int
(define (interpret-while fuel value w s)
  (if (<= fuel 0)
      value
      (match w
        [(set-api (while o:observation pi:pred-inner pw:pred-while))
         (if (interpret-observation o s)
             (let ([cs (interpret-inner value pi s)])
               (interpret-while (- fuel 1) (first cs) w (second cs)))
               (interpret-while fuel value pw s))]
         [(set-api nop)
          value])))

;; pred-while -> state -> int
(define (interpret-while-d w s)
  (interpret-while 4 0 w s))


;;; FOLD pred language

;; pred-fold -> int -> int -> int
(define (interpret-pred-fold p e v)
  (match p
    [(set-api var-element)
     e]
    [(set-api var-value)
     v]
    [(set-api i:integer)
     (bonsai->number i)]
    [(set-api (if-el-eq i:integer p1:pred-fold p2:pred-fold))
     (if (equal? (bonsai->number i) e)
         (interpret-pred-fold p1 e v)
         (interpret-pred-fold p2 e v))]
    [(set-api (if-val-eq i:integer p1:pred-fold p2:pred-fold))
     (if (equal? (bonsai->number i) v)
         (interpret-pred-fold p1 e v)
         (interpret-pred-fold p2 e v))]

    [(set-api (add p1:pred-fold p2:pred-fold))
     (+  (interpret-pred-fold p1 e v)
         (interpret-pred-fold p2 e v))]
    [(set-api (minus p+:pred-fold))
     (- (interpret-pred-fold p+ e v))]))

  

;; pred-fold -> set -> int -> int
(define (interpret-fold+ p s v)
  (match s
    [(set-api nil)
     v]
    [(set-api (cons e:integer s+:set))
     (interpret-fold+ p s+ (interpret-pred-fold p (bonsai->number e) v))]))

; Folds over state s using function p and default value 0
;; pred-fold -> set -> int
(define (interpret-fold p s)
  (interpret-fold+ p s 0))

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
     (concrete-insert s i)]
    [(set-api (remove i:integer))
     (concrete-remove s i)]))

;; method -> set -> set
;; uses buggy-concrete-remove which just removes one instance of element i
(define (interpret-buggy-method m s)
  (match m
    [(set-api (insert i:integer))
     (concrete-insert s i)]
    [(set-api (remove i:integer))
     (buggy-concrete-remove s i)]))


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




; Synthesize a predicate and a gadget implementing "not" using set
;; Expected:
;;; predicate: (set-api (member? 1))
;;; gadget: (set-api (if (member? 1) (seq (remove 1) nop) (seq (insert 1) nop)))
(define (test-spec-member)
  (begin
    (define spec (lambda (x) (not x)))
    (define predicate (set-api pred 2))
    (define gadget (set-api interaction 4))
    (define set (set-api set 3))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (equal?
                               (interpret-pred predicate (interpret-interaction gadget set))
                               (spec (interpret-pred predicate set))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget (concretize gadget sol))
          (displayln "gadget...")
          (displayln c-gadget)
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))
    ))

; Natural numbers in set from definition of z and +
; NOTE: this would not work in buggy set
;; Expected:
;;; predicate: (count 0)
;;; gadget-z (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-count)
  (begin
    (define spec-z 0)
    (define spec-succ (lambda (n) (+ 1 n)))
    (define predicate (set-api pred 2))
    (define gadget-z (set-api interaction 3))
    (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-pred predicate (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-pred predicate set)))
                                   (equal?
                                    (interpret-pred predicate (interpret-interaction gadget-z set))
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
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))))


; Natural numbers in buggy set from definition of nat-pred and +1
; NOTE: this would not work in set
;; Expected:
;;; predicate: (count 0)
;;; gadget-pred (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-buggy-count)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define predicate (set-api pred 2))
    (define gadget-pred (set-api interaction 3))
   (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set

                 #:guarantee (assert
                              (and (equal?
                                    (interpret-pred predicate (interpret-buggy-interaction gadget-succ set))
                                    (spec-succ (interpret-pred predicate set)))
                                   (equal?
                                    (interpret-pred predicate (interpret-buggy-interaction gadget-pred set))
                                    (spec-pred (interpret-pred predicate set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate))))
  )


; Integers in set from -1 and +1
; NOTE: this also works in buggy set
;; Expected:
;;; predicate (set-api (minus (count 0) (count 1))))
;;; gadget-pred (set-api (seq (insert 1) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-count-int)
  (begin
    (define spec-pred (lambda (n) (- n 1)))
    (define spec-succ (lambda (n) (+ n 1)))
   (define predicate (set-api pred 3))
    (define gadget-pred (set-api interaction 3))
   (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
  (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-pred predicate (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-pred predicate set)))
                                   (equal?
                                    (interpret-pred predicate (interpret-interaction gadget-pred set))
                                    (spec-pred (interpret-pred predicate set)))))))
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
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))))

          
; Natural numbers in sets from 0 and +1
; where the predicate is a fold over state
;; Expected:
;;; predicate (set-api (add (if-el-eq 1 1 0) var-value))
;;; gadget-pred (set-api (seq (remove 1) nop))
;;; gadget-succ (set-api (seq (insert 1) nop))
(define (test-spec-count-fold)
  (begin
    (define spec-z 0)
    (define spec-succ (lambda (n) (+ 1 n)))
    (define predicate (set-api pred-fold 3))
    (define gadget-z (set-api interaction 3))
    (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-fold predicate (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-fold predicate set)))
                                   (equal?
                                    (interpret-fold predicate (interpret-interaction gadget-z set))
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
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))))


; Natural numbers in buggy-sets from nat-pred and +1
; where the predicate is a fold over state
;; Expected:
;;; predicate (set-api (add (if-el-eq 1 1 0) var-value))
;;; gadget-pred (set-api (seq (remove 1) nop))
;;; gadget-succ (set-api (seq (insert 1) nop))
(define (test-spec-buggy-count-fold-nat)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define predicate (set-api pred-fold 3))
    (define gadget-pred (set-api interaction 3))
   (define gadget-succ (set-api interaction 3))
    (define set (set-api set 5))
  (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-fold predicate (interpret-buggy-interaction gadget-succ set))
                                    (spec-succ (interpret-fold predicate set)))
                                   (equal?
                                    (interpret-fold predicate (interpret-buggy-interaction gadget-pred set))
                                    (spec-pred (interpret-fold predicate set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))))


; Natural numbers in buggy-sets from nat-pred and +1
; where the predicate is a sequence of while observation interaction with a counter
; NOTE: this takes a long time with larger set. while is bounded by fuel in interpret-while-d.
; NOTE: this would NOT work on non-buggy set
;; Expected:
;;; predicate (set-api (while (member? 0) (seq (remove 0) (inc nop)) (while (member? 0) nop nop))
;;; gadget-pred (set-api (seq (remove 0) nop))
;;; gadget-succ (set-api (seq (insert 0) nop))
(define (test-spec-buggy-count-while-nat)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define predicate (set-api pred-while 4))
    (define gadget-pred (set-api interaction 3))
   (define gadget-succ (set-api interaction 3))
    (define set (set-api set 3))
  (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-while-d predicate (interpret-buggy-interaction gadget-succ set))
                                    (spec-succ (interpret-while-d predicate set)))
                                   (equal?
                                    (interpret-while-d predicate (interpret-buggy-interaction gadget-pred set))
                                    (spec-pred (interpret-while-d predicate set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (define c-predicate (concretize predicate sol))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)          
          (displayln "predicate...")
          (displayln c-predicate)))))

; This should fail, as non-buggy version cannot produce something equivalent to "count" using pred-while 
(define (test-spec-count-while-nat)
  (begin
    (define spec-z 0)
    (define spec-succ (lambda (n) (+ 1 n)))
    (define predicate (set-api pred-while 4))
    (define gadget-z (set-api interaction 3))
    (define gadget-succ (set-api interaction 3))
    (define set (set-api set 3))
    (define sol (synthesize
                 #:forall set
                 #:guarantee (assert
                              (and (equal?
                                    (interpret-fold predicate (interpret-interaction gadget-succ set))
                                    (spec-succ (interpret-fold predicate set)))
                                   (equal?
                                    (interpret-fold predicate (interpret-interaction gadget-z set))
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
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))))
