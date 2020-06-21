#lang seec

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a list datatype
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar list-api
  (value ::= integer)
  (valopt ::= (some value) none)
  (vallist ::= (value vallist) empty)
  (method ::=  (cons value) nil)
  (interaction ::= (method interaction) empty))

(define (abstract-cons n l)
  (list-api (,n ,l)))

(define abstract-nil
  (list-api empty))


; 
(define (abstract-lookup n l)
  (match l
    [(list-api (hd:value tl:vallist))
     (if (equal? n 0)
         (list-api (some ,hd))
         (abstract-lookup (- n 1) tl))]
    [(list-api empty)
     (list-api none)]))
    

(define (interpret-interaction ints l)
  (match ints
    [(list-api empty) l]
    [(list-api (m:method intss:interaction))
     (match m
       [(list-api nil)
        (interpret-interaction intss (list-api empty))]
       [(list-api (cons n:value))
        (interpret-interaction intss (list-api (,n ,l)))])]))

; Tests for list

(define abc (list-api (1 (2 (3 empty)))))

(define b1 (list-api ((cons 4) ((cons 1) empty))))
(define b2 (list-api (nil ,b1)))

(displayln (interpret-interaction b1 abc))
(displayln (interpret-interaction b2 abc))
(displayln (abstract-lookup 0 abc))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a linked-list datatype that will implement the list API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-grammar linked-list
  (value ::= integer)
  (pointer ::= integer null) ; pointer is distance from end (top) of heap
  (cell ::= (value pointer))
  (heap ::= (cell heap) empty)
  (state ::= (pointer pointer heap)) ; (1) head of the list (2) head of the free-list (3) heap
  (method ::= (cons value) nil)
  (interaction ::= (method interaction) empty)) 

(define (empty-state s)
  (linked-list (null null empty)))

(define (destruct-heap s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (list (linked-list ,hd) (linked-list ,fp) (linked-list ,hp))]))


(define (interpret-interaction-ll ints s)
  (match ints
    [(linked-list empty) s]
    [(linked-list (m:method intss:interaction))
     (let-values ([(hd hp) (destruct-heap s)])
       (match m
         [(linked-list nil)                     
          (interpret-interaction-ll intss (linked-list (null ,hp)))]
         [(linked-list (cons n:value))
          (let* ([updated-hp (linked-list ((,n ,hd) ,hp))]) ; TODO: hd + 1 here
            (interpret-interaction-ll intss (linked-list (0 ,updated-hp))))]))]))



(define (list-to-ll-inner l)
  (begin
    (displayln l)
    (match l
      [(list-api (hd:value empty))
       (linked-list ((,hd null) empty))]
      [(list-api (hd:value tl:vallist))
       (let ([h (list-to-ll-inner tl)]
           [c (linked-list (,hd 1))])
         (linked-list (,c ,h)))])))


(define (list-to-ll l)
  (match l
    [(list-api empty)
     (linked-list (null empty))]
    [ _
      (let ([h (list-to-ll-inner l)])
        (linked-list (0 ,h)))]))

     
; Test for linked-list
(define abc-ll (list-to-ll abc))
(define b1-ll (linked-list ((cons 4) ((cons 1) empty))))


(displayln abc-ll)
(displayln (list-to-ll abstract-nil))
;(displayln (interpret-interaction-ll b1-ll abc-ll))



  #|
  n = 0 -> look at head cell, return (value :: m)
  where m is: if pointer = null, nil
              if pointer = p: ll-to-list-n p revheap heap
  n = S m -> place head-cell on rev-heap
    |#

#;(define (ll-to-list-n n revheap heap)
  (begin
    (if (negative? n)
        (assert (< n (length revheap)))
        (assert (<= n (length heap))))
    (list-api empty)))  


#;(define (ll-to-list s)
  (match s
    [(n:integer h:heap)
     (ll-to-list-n n empty h)]
    [(null h:heap)
     (list-api empty)]))



#| 
(define-grammar linked-list
  (value ::= integer) 
  (pointer ::= natural null)
  (cell ::= (value pointer)) ; cell is a link (value, pointer)
  (heap ::= list<cell>)
  (state ::= (natural natural heap)) ; state is (1) head of the list (2) head of free-list  (3) heap
  (method ::= (cons value) nil)
  (interaction ::= (method interaction) empty))


; insert head2 at the end of head1
;
(define (linked-append head1 head2 hp)
  (match head1
    [(list-api null)
     (cons head2 hp)
     ]
    [(list-api natural)
     
     
     ]
 
    

; Reset the state to represent an empty list
(define (linked-nil s)
  (match s
    [(list-api (head:natural free:natural hp:heap))
     (let ([mod-heap (linked-append heap free hp)])
       (list-api (null head mod-heap)))]))

(define (interpret-interaction-ll ints s)
  (match ints
    [(list-api empty) l]
    [(list-api (m:method intss:interaction))
     (match m
       [(list-api nil)
        (interpret-interaction intss (linked-nil s))] 
       [(list-api (cons n:value))
        (interpret-interaction intss (linked-cons n s))])]))



|#
