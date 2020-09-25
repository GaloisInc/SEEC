#lang seec
(provide (all-defined-out))

; Performance tweak: model integers using 4-bit bitvectors
;(set-bitwidth 4)
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
  (pred-while ::= (while obs pred-inner pred-while) nop)             
  (pred-fold   ::= var-element var-value integer (if-val-eq integer pred-fold pred-fold) (if-el-eq integer pred-fold pred-fold) (add pred-fold pred-fold) (minus pred-fold)) 
  (pred        ::= (count integer) (prefix? set) (member? integer) (add pred pred) (minus pred pred) (or pred pred) (and pred pred) (not pred)) ; predicate on lists (list -> T)
  (obs         ::= (member? integer) (or pred pred) (and pred pred) (not pred))   ; observations (set -> bool)
  (obs-target        ::= (equal? set) (member? integer) (or pred pred) (and pred pred) (not pred))   ; observations (set -> bool)
  (met         ::= (insert integer) (remove integer)) ; commands (set -> set)
  (int         ::= (seq met int) (if obs int int) nop) ; programs (set -> set)
  (method      ::= (insert integer) (remove integer) (member? integer) select)
  (interaction ::= list<method>)
  
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

; Input: an interaction and a state (vallist)
; Output: the trace (vallist) obtained by executing the interaction on the input
; state
(define (abstract-interpret interaction state)
  (match interaction
    [(set-api nil) (set-api nil)]
    [(set-api (cons (insert v:value) r:interaction))
     (abstract-interpret r (abstract-insert state v))]
    [(set-api (cons (remove v:value) r:interaction))
     (abstract-interpret r (abstract-remove state v))]
    [(set-api (cons (member? v:value) r:interaction))
     (set-api (cons ,(abstract-member? state v) ,(abstract-interpret r state)))]
    [(set-api (cons select r:interaction))
     (set-api (cons ,(abstract-select state) ,(abstract-interpret r state)))]))

; Input: an interaction and a set
; Output: a pair of a trace and a set obtained by executing
; the interaction on the input state
(define (abstract-interpret-with-state interaction state)
  (match interaction
    [(set-api nil) (cons (set-api nil) state)]
    [(set-api (cons (insert v:value) r:interaction))
     (let* ([new-state (abstract-insert state v)])
       (abstract-interpret-with-state r new-state))]
    [(set-api (cons (remove v:value) r:interaction))
     (let* ([new-state (abstract-remove state v)])
       (abstract-interpret-with-state r new-state))]
    [(set-api (cons (member? v:value) r:interaction))
     (let* ([b (abstract-member? state v)])
       (match (abstract-interpret-with-state r state)
         [(cons t state+)
          (cons (set-api (cons ,b ,t)) state+)]))]
    [(set-api (cons select r:interaction))
     (let* ([b (abstract-select state)])
       (match (abstract-interpret-with-state r state)
         [(cons t state+)
          (cons (set-api (cons ,b ,t)) state+)]))]
    ))

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

(define (concrete-interpret interaction state)
  (match interaction
    [(set-api nil) (set-api nil)]
    [(set-api (cons (insert v:value) r:interaction))
     (concrete-interpret r (concrete-insert state v))]
    [(set-api (cons (remove v:value) r:interaction))
     (concrete-interpret r (concrete-remove state v))]
    [(set-api (cons (member? v:value) r:interaction))
     (set-api (cons ,(concrete-member? state v) ,(concrete-interpret r state)))]
    [(set-api (cons select r:interaction))
     (set-api (cons ,(concrete-select state) ,(concrete-interpret r state)))]))

(define (buggy-concrete-interpret interaction state)
  (match interaction
    [(set-api nil) (set-api nil)]
    [(set-api (cons (insert v:value) r:interaction))
     (buggy-concrete-interpret r (concrete-insert state v))]
    [(set-api (cons (remove v:value) r:interaction))
     (buggy-concrete-interpret r (buggy-concrete-remove state v))]
    [(set-api (cons (member? v:value) r:interaction))
     (set-api (cons ,(concrete-member? state v) ,(buggy-concrete-interpret r state)))]
    [(set-api (cons select r:interaction))
     (set-api (cons ,(concrete-select state) ,(buggy-concrete-interpret r state)))]))

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


; Input: an interaction and a set
; Output: a pair of a trace and a set obtained by executing
; the interaction on the input state
(define (concrete-interpret-with-state interaction state)
  (match interaction
    [(set-api nil) (cons (set-api nil) state)]
    [(set-api (cons (insert v:value) r:interaction))
     (let* ([new-state (concrete-insert state v)])
       (concrete-interpret-with-state r new-state))]
    [(set-api (cons (remove v:value) r:interaction))
     (let* ([new-state (concrete-remove state v)])
       (concrete-interpret-with-state r new-state))]
    [(set-api (cons (member? v:value) r:interaction))
     (let* ([b (concrete-member? state v)])
       (match (concrete-interpret-with-state r state)
         [(cons t state+)
          (cons (set-api (cons ,b ,t)) state+)]))]
    [(set-api (cons select r:interaction))
     (let* ([b (concrete-select state)])
       (match (concrete-interpret-with-state r state)
         [(cons t state+)
          (cons (set-api (cons ,b ,t)) state+)]))]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Work in progress to synthesize predicates and gadgets 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; pred -> set -> T
(define (concrete-interpret-pred p s)
  (match p
    [(set-api (count i:integer))
     (interpret-count s i)]
    [(set-api (add p1:pred p2:pred))
     (+ (concrete-interpret-pred p1 s)
        (concrete-interpret-pred p2 s))]
     [(set-api (minus p1:pred p2:pred))
      (- (concrete-interpret-pred p1 s)
         (concrete-interpret-pred p2 s))]
    [(set-api (not p+:pred))
     (not (concrete-interpret-pred p+ s))]
    [(set-api (and p1:pred p2:pred))
     (and (concrete-interpret-pred p1 s)
          (concrete-interpret-pred p2 s))]
    [(set-api (or p1:pred p2:pred))
     (or (concrete-interpret-pred p1 s)
         (concrete-interpret-pred p2 s))]
    [(set-api (prefix? vl:set))
     (interpret-prefix? s vl)]
    [(set-api (member? v:value))
     (interpret-member? s v)]))

;;; WHILE pred language
(define (concrete-interpret-inner value i s)
  (match i
    [(set-api (if o:obs pi1:pred-inner pi2:pred-inner))
     (if (concrete-interpret-obs o s)
         (concrete-interpret-inner value pi1 s)
         (concrete-interpret-inner value pi2 s))]
    [(set-api (seq m:met i+:pred-inner))
     (concrete-interpret-inner value i+ (concrete-interpret-buggy-met m s))]
    [(set-api (inc i+:pred-inner))
     (concrete-interpret-inner (+ value 1) i+ s)]
    [(set-api (dec i+:pred-inner))
     (concrete-interpret-inner (- value 1) i+ s)]
    [(set-api nop)
     (list value s)
     ]))

;; int -> int pred-while -> set -> integer
(define (concrete-interpret-while fuel value w s)
  (if (<= fuel 0)
      value
      (match w
        [(set-api (while o:obs pi:pred-inner pw:pred-while))
         (if (concrete-interpret-obs o s)
             (let ([cs (concrete-interpret-inner value pi s)])
               (concrete-interpret-while (- fuel 1) (first cs) w (second cs)))
               (concrete-interpret-while fuel value pw s))]
         [(set-api nop)
          value])))

(define (concrete-interpret-while-d w s)
  (concrete-interpret-while 4 0 w s))


;;; FOLD pred language
(define (concrete-interpret-pred-fold p e v)
  (match p
    [(set-api var-element)
     e]
    [(set-api var-value)
     v]
    [(set-api i:integer)
     (bonsai->number i)]
    [(set-api (if-el-eq i:integer p1:pred-fold p2:pred-fold))
     (if (equal? (bonsai->number i) e)
         (concrete-interpret-pred-fold p1 e v)
         (concrete-interpret-pred-fold p2 e v))]
    [(set-api (if-val-eq i:integer p1:pred-fold p2:pred-fold))
     (if (equal? (bonsai->number i) v)
         (concrete-interpret-pred-fold p1 e v)
         (concrete-interpret-pred-fold p2 e v))]

    [(set-api (add p1:pred-fold p2:pred-fold))
     (+  (concrete-interpret-pred-fold p1 e v)
         (concrete-interpret-pred-fold p2 e v))]
    [(set-api (minus p+:pred-fold))
     (- (concrete-interpret-pred-fold p+ e v))]))

  

;; pred-fold -> set -> integer (value) -> integer
(define (concrete-interpret-fold+ p s v)
  (match s
    [(set-api nil)
     v]
    [(set-api (cons e:integer s+:set))
     (concrete-interpret-fold+ p s+ (concrete-interpret-pred-fold p (bonsai->number e) v))]))

(define (concrete-interpret-fold p s)
  (concrete-interpret-fold+ p s 0))

;; obs -> set -> bool
(define (concrete-interpret-obs p s)
  (match p
    [(set-api (not p+:obs))
     (not (concrete-interpret-obs p+ s))]
    [(set-api (and p1:obs p2:obs))
     (and (concrete-interpret-obs p1 s)
          (concrete-interpret-obs p2 s))]
    [(set-api (or p1:obs p2:obs))
     (or (concrete-interpret-obs p1 s)
         (concrete-interpret-obs p2 s))]
    [(set-api (member? v:integer))
     (interpret-member? s v)]))

;; met -> set -> set
(define (concrete-interpret-met m s)
  (match m
    [(set-api (insert i:integer))
     (concrete-insert s i)]
    [(set-api (remove i:integer))
     (concrete-remove s i)]))

;; met -> set -> set
;; uses buggy-concrete-remove which just removes one instance of element i
(define (concrete-interpret-buggy-met m s)
  (match m
    [(set-api (insert i:integer))
     (concrete-insert s i)]
    [(set-api (remove i:integer))
     (buggy-concrete-remove s i)]))


;; int -> set -> set
(define (concrete-interpret-int i s)
  (match i
    [(set-api nop)
     s]
    [(set-api (seq m:met i+:int))
     (concrete-interpret-int i+ (concrete-interpret-met m s))]
    [(set-api (if o:obs i1:int i2:int))
     (if (concrete-interpret-obs o s)
         (concrete-interpret-int i1 s)
         (concrete-interpret-int i2 s))]))

;; int -> set -> set
(define (concrete-interpret-buggy-int i s)
  (match i
    [(set-api nop)
     s]
    [(set-api (seq m:met i+:int))
     (concrete-interpret-int i+ (concrete-interpret-buggy-met m s))]
    [(set-api (if o:obs i1:int i2:int))
     (if (concrete-interpret-obs o s)
         (concrete-interpret-int i1 s)
         (concrete-interpret-int i2 s))]))


;; trying to synthesize a predicate:pred recognizing some notion of booleans in the list/set,
;; and a gadget:int implementing the specification (e.g. not)

;(define spec not)
;(define spec (lambda (x) x))
(define s1 (set-api (cons 1 nil)))
(define s2 (set-api (cons 2 (cons 3 nil))))
(define s3 (set-api (cons 4 (cons 1 (cons 5 nil)))))


#;(define gadget (set-api int 6))
#;(define predicate (set-api (member? 1)))
#;(define gadget (set-api (if (member? 1)
                            (seq (remove 1) nop)
                            (seq (insert 1) nop))))
#;(define set (set-api set 4))
#;(define sol (verify (assert
                      (equal?
                           (concrete-interpret-pred predicate (concrete-interpret-int gadget set))
                           (spec (concrete-interpret-pred predicate set))))))


;; find a sec for which this doesn't work


;; FAILING Predicate is a pred, gadget implements not 
;(define predicate (set-api (prefix? (cons 1 (cons 1 nil)))))
#;(define gadget (set-api (if (member? 1)
                            (seq (insert 0) nop)
                            (seq (insert 1) (seq (insert 1) nop)))))



;; Predicate is an obs, gadget implements not
(define (test-spec-member)
  (begin
    (define spec (lambda (x) (not x)))
    (define predicate (set-api pred 2))
    ;  (define predicate (set-api (member? 1)))
    ;  (define predicate (set-api (prefix? (cons 1 nil)))) FAILS
    ;(define predicate (set-api (or (member? 1) (member? 2))))
    (define gadget (set-api int 4))
    #;(define gadget (set-api (if (member? 1)
                                  (seq (remove 1) nop)
                                  (seq (insert 1) nop))))        
    (define set (set-api set 3))
    (define sol (synthesize
                 #:forall set
                 ;             #:assume ..
                 #:guarantee (assert
                              (equal?
                               (concrete-interpret-pred predicate (concrete-interpret-int gadget set))
                               (spec (concrete-interpret-pred predicate set))))))
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

; Synthesizing z (remove) and succ (insert) and pred (count) from definition of z and +
(define (test-spec-count)
  (begin
    (define spec-z 0)
    (define spec-succ (lambda (n) (+ 1 n)))
    (define predicate (set-api pred 2))
    ;  (define predicate (set-api (member? 1)))
    ;  (define predicate (set-api (prefix? (cons 1 nil)))) FAILS
    (define gadget-z (set-api int 3))
    (define gadget-succ (set-api int 3))
    #;(define gadget (set-api (if (member? 1)
                                  (seq (remove 1) nop)
                                  (seq (insert 1) nop))))        
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set
                 ;             #:assume ..
                 #:guarantee (assert
                              (and (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-int gadget-succ set))
                                    (spec-succ (concrete-interpret-pred predicate set)))
                                   (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-int gadget-z set))
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


; Synthesizing pred (buggy-remove) and succ (insert) and pred (count) from definition of -1 and +1
(define (test-spec-buggy-count)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define predicate (set-api pred 2))
;    (define predicate (set-api (count 1)))
    ;  (define predicate (set-api (prefix? (cons 1 nil)))) FAILS
    (define gadget-pred (set-api int 3))
;    (define gadget-pred (set-api (seq (remove 1) nop)))
   (define gadget-succ (set-api int 3))
;    (define gadget-succ (set-api (seq (insert 1) nop)))
    #;(define gadget (set-api (if (member? 1)
                                  (seq (remove 1) nop)
                                  (seq (insert 1) nop))))        
    (define set (set-api set 5))
    #;(define sol (verify (assert
                              (and (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-pred predicate set)))
                                   (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-pred predicate set)))))))
    (define sol (synthesize
                 #:forall set
                 ;             #:assume ..
                 #:guarantee (assert
                              (and (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-pred predicate set)))
                                   (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-pred predicate set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          #;(define c-set (concretize set sol))
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          #|(displayln "set...")
          (displayln c-set)
          (displayln "results (succ and pred)...")
          (displayln (equal? (concrete-interpret-pred predicate (concrete-interpret-buggy-int c-gadget-succ c-set))
                             (spec-succ (concrete-interpret-pred predicate c-set))))
          (displayln (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int c-gadget-pred c-set))
                                    (spec-pred (concrete-interpret-pred predicate c-set))))|#
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate))))
          )

; trying to synthesize pred on integer using 2 counts
(define (test-spec-buggy-count-int)
  (begin
    (define spec-pred (lambda (n) (- n 1)))
    (define spec-succ (lambda (n) (+ n 1)))
   (define predicate (set-api pred 3))
;    (define predicate (set-api (minus (count 0) (count 1))))
    (define gadget-pred (set-api int 3))
;    (define gadget-pred (set-api (seq (insert 1) nop)))
   (define gadget-succ (set-api int 3))
;    (define gadget-succ (set-api (seq (insert 0) nop)))
    (define set (set-api set 5))
#;    (define sol (verify (assert
                              (and (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-pred predicate set)))
                                   (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-pred predicate set)))))))
  (define sol (synthesize
                 #:forall set
                 ;             #:assume ..
                 #:guarantee (assert
                              (and (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-pred predicate set)))
                                   (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-pred predicate set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-set (concretize set sol))
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (displayln "set...")
          (displayln c-set)
          (displayln "results (succ and pred)...")
          (displayln (equal? (concrete-interpret-pred predicate (concrete-interpret-buggy-int c-gadget-succ c-set))
                             (spec-succ (concrete-interpret-pred predicate c-set))))
          (displayln (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int c-gadget-pred c-set))
                                    (spec-pred (concrete-interpret-pred predicate c-set))))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))))
          
;; Synthesize count from fold
(define (test-spec-count-fold)
  (begin
    (define spec-z 0)
    (define spec-succ (lambda (n) (+ 1 n)))
    (define predicate (set-api pred-fold 3))
#;    (define predicate (set-api (add (if-el-eq 1 1 0) var-value)))
    (define gadget-z (set-api int 3))
    (define gadget-succ (set-api int 3))
    #;(define gadget (set-api (if (member? 1)
                                  (seq (remove 1) nop)
                                  (seq (insert 1) nop))))        
    (define set (set-api set 5))
    (define sol (synthesize
                 #:forall set
                 ;             #:assume ..
                 #:guarantee (assert
                              (and (equal?
                                    (concrete-interpret-fold predicate (concrete-interpret-int gadget-succ set))
                                    (spec-succ (concrete-interpret-fold predicate set)))
                                   (equal?
                                    (concrete-interpret-fold predicate (concrete-interpret-int gadget-z set))
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


;; synthesize count (from fold) and pred + succ over nat
(define (test-spec-buggy-count-fold-nat)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define predicate (set-api pred-fold 3))
;   (define predicate (set-api (add (if-el-eq -4577 1 0) var-value)))
;    (define predicate (set-api (minus (count 0) (count 1))))
    (define gadget-pred (set-api int 3))
;    (define gadget-pred (set-api (seq (insert 1) nop)))
   (define gadget-succ (set-api int 3))
;    (define gadget-succ (set-api (seq (insert 0) nop)))
    (define set (set-api set 5))
#;    (define sol (verify (assert
                              (and (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-pred predicate set)))
                                   (equal?
                                    (concrete-interpret-pred predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-pred predicate set)))))))
  (define sol (synthesize
                 #:forall set
                 ;             #:assume ..
                 #:guarantee (assert
                              (and (equal?
                                    (concrete-interpret-fold predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-fold predicate set)))
                                   (equal?
                                    (concrete-interpret-fold predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-fold predicate set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-set (concretize set sol))
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (displayln "set...")
          (displayln c-set)
          (displayln "results (succ and pred)...")
          (displayln (equal? (concrete-interpret-fold predicate (concrete-interpret-buggy-int c-gadget-succ c-set))
                             (spec-succ (concrete-interpret-fold predicate c-set))))
          (displayln (equal?
                                    (concrete-interpret-fold predicate (concrete-interpret-buggy-int c-gadget-pred c-set))
                                    (spec-pred (concrete-interpret-fold predicate c-set))))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)
          (define c-predicate (concretize predicate sol))
          (displayln "predicate...")
          (displayln c-predicate)))))


;; synthesize count (from fold) and pred + succ over nat
(define (test-spec-buggy-count-while-nat)
  (begin
    (define spec-pred (lambda (n) (max 0 (- n 1))))
    (define spec-succ (lambda (n) (+ n 1)))
    (define predicate (set-api pred-while 4))
    #;(define predicate (while (member? 7704) (seq (remove 7704) (inc nop)) (while (member? 7704) nop nop)))
    (define gadget-pred (set-api int 3))
;    (define gadget-pred (set-api (seq (remove 1) nop)))
   (define gadget-succ (set-api int 3))
;    (define gadget-succ (set-api (seq (insert 1) nop)))
    (define set (set-api set 3))
#;    (define sol (verify (assert
                              (and (equal?
                                    (concrete-interpret-while-d predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-while-d predicate set)))
                                   (equal?
                                    (concrete-interpret-while-d predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-while-d predicate set)))))))
  (define sol (synthesize
                 #:forall set
                 ;             #:assume ..
                 #:guarantee (assert
                              (and (equal?
                                    (concrete-interpret-while-d predicate (concrete-interpret-buggy-int gadget-succ set))
                                    (spec-succ (concrete-interpret-while-d predicate set)))
                                   (equal?
                                    (concrete-interpret-while-d predicate (concrete-interpret-buggy-int gadget-pred set))
                                    (spec-pred (concrete-interpret-while-d predicate set)))))))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")
          (define c-set (concretize set sol))
          (define c-gadget-succ (concretize gadget-succ sol))
          (define c-gadget-pred (concretize gadget-pred sol))
          (define c-predicate (concretize predicate sol))

          (displayln "set...")
          (displayln c-set)
          (displayln "results (succ and pred)...")
          (displayln (concrete-interpret-while-d c-predicate (concrete-interpret-buggy-int c-gadget-succ c-set)))         
          (displayln (spec-succ (concrete-interpret-while-d predicate c-set)))
          (displayln (concrete-interpret-while-d c-predicate (concrete-interpret-buggy-int c-gadget-pred c-set)))
          (displayln (spec-pred (concrete-interpret-while-d predicate c-set)))
          (displayln "gadget pred and succ...")
          (displayln c-gadget-pred)
          (displayln c-gadget-succ)          
          (displayln "predicate...")
          (displayln c-predicate)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Helper function for constraining the synthesis search problem
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (valid-set? xs)
  (match xs
    [(set-api nil) #t]
    [(set-api (cons x:integer r:vallist))
     (match (concrete-member? r x)
       [(set-api #f) (valid-set? r)]
       [(set-api #t) #f])]
    [_ #f]))

(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

(define id
  (lambda (a)
    a))


; cons in reverse order
(define snoc
  (lambda (a b) (cons b a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Demonstration synthesis tasks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-language abstract
  #:grammar set-api
  #:expression interaction #:size 4
  #:context    vallist     #:size 2 #:where valid-set?
  #:link snoc
  #:evaluate (uncurry abstract-interpret))

(define-language concrete
  #:grammar set-api
  #:expression interaction #:size 4
  #:context    vallist     #:size 2 #:where valid-set?
  #:link snoc
  #:evaluate (uncurry concrete-interpret))

(define-compiler abstract-to-concrete
  #:source abstract
  #:target concrete
  #:behavior-relation equal?
  #:context-relation equal?
  #:compile id)

(define-language buggy-concrete
  #:grammar set-api
  #:expression interaction #:size 4
  #:context    vallist     #:size 2 #:where valid-set?
  #:link snoc
  #:evaluate (uncurry buggy-concrete-interpret))

(define-compiler abstract-to-buggyconcrete
  #:source abstract
  #:target buggy-concrete
  #:behavior-relation equal?
  #:context-relation equal?
  #:compile id)


; OS: Concrete doesn't work here since concrete-interpret returns a trace as behavior, which doesn't witness the length of the list underlying the set
; JP: Changing evaluate to concrete-context which makes behavior := trace * vallist

(define-language concrete-with-state
  #:grammar set-api
  #:expression interaction #:size 4
  #:context    set     #:size 2 #:where valid-set?
  #:link snoc ; link is applied to the context and then the expression, so in
              ; this case a program is (snoc vallist context) = (cons context vallist)
  #:evaluate (uncurry concrete-interpret-with-state))


#;(begin
  #;(define v1 (set-api interaction 4))
  (define v1 (set-api (cons (insert 0) nil)))

  (define c1 (set-api set 3))
  #;(define c1 (set-api (cons 0 nil)))

  (define b1 (concrete-interpret-with-state v1 c1))
  (displayln "b1...")
  (displayln b1)
  (define condition (add1-concrete? (cons v1 c1) b1))
  (displayln "condition...")
  (displayln condition)
  (define sol (synthesize
               #:forall c1
               #:guarantee (assert condition)
               ))
  (if (unsat? sol)
      (displayln "Synthesis failed")
      (begin
        (displayln "Synthesis succeeded")
        (define v-concrete (concretize v1 sol))
        (displayln "interaction...")
        (displayln v-concrete)

        #;(displayln "set...")
        #;(displayln (concretize c1 sol))
        )
  ))



(define (concrete-two-member-spec? prog res-set)
  (let ([member1 (concrete-member? res-set (bonsai-integer 1))]
        [member2 (concrete-member? res-set (bonsai-integer 2))])
    (and (bonsai->racket member1) (not (bonsai->racket member2)))))

(define expected-context (set-api (cons (insert 1) (cons (remove 2) nil))))


; Trying to do something equivalent to concrete-two-member-spec with the concrete language (dealing with interactions)
; 1) append the lookups after the interactions
; 2) check the last two element of the trace
(define (concrete-member-spec? prog res-set)
  (match prog
    [(cons expr init-set)     
     (let* ([test-expr (set-api (cons (member? 1) (cons (member? 2) nil)))]
            [full-expr (append expr test-expr)]
            [trace (concrete-interpret full-expr test-expr)]
            [test-trace (drop trace (length expr))])
       (match test-trace
         [(list mem1 mem2)
            (and mem1 (not mem2))]
         [ _ #f]))]))


