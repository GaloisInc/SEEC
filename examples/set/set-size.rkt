#lang seec

; Performance tweak: model integers using 4-bit bitvectors
(current-bitwidth 4)
(current-default-bound 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a set datastructure
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar set-api
  (value       ::= integer boolean)
  (vallist     ::= list<value>) ; empty (value vallist))
  (method      ::= (insert integer) (remove integer) (member? integer) select)
  (interaction ::= list<method>) ; empty (method interaction))
;  (context     ::= empty ((insert integer) context) ((remove integer) context))
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
; Output: the state (vallist) obtained by executing the interaction on the input
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
  #:expression interaction 
  #:context    vallist #:where valid-set?
  #:link snoc
  #:evaluate (uncurry abstract-interpret))

(define-language concrete
  #:grammar set-api
  #:expression interaction
  #:context    vallist #:where valid-set?
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
  #:expression interaction
  #:context    vallist #:where valid-set?
  #:link snoc
  #:evaluate (uncurry buggy-concrete-interpret))

(define-compiler abstract-to-buggyconcrete
  #:source abstract
  #:target buggy-concrete
  #:behavior-relation equal?
  #:context-relation equal?
  #:compile id)

(begin
  (displayln "Trying to find a trace with weird behavior under buggy compilation")
  (let* ([trace (set-api interaction 4)]
         [gen (make-query-weird-computation
               abstract-to-buggyconcrete
               trace
               #:source-context-bound 2
               #:target-context-bound 2)]
         [witness (gen)])
    (display-weird-component witness displayln)))

(begin
  (displayln "Trying to find a trace with different behavior under compilation")
  (let* ([trace (set-api interaction 4)]
         [gen (make-query-changed-behavior abstract-to-concrete
                                           trace
                                           #:source-context-bound 2
                                           #:target-context-bound 2)]
         [witness (gen)])
    (display-changed-behavior witness displayln)))

(begin
  (displayln "Trying to find a trace with weird behavior under correct compilation")
  (let* ([trace (set-api interaction 4)]
         [gen (make-query-weird-computation abstract-to-concrete
                                            trace
                                            #:source-context-bound 2
                                            #:target-context-bound 2)]
         [witness (gen)])
    (display-weird-component witness displayln)))


