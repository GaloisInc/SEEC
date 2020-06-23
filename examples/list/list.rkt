#lang seec
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))


(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    [_ (raise-argument-error 'bonsai->number "bonsai-integer?" n)]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a list datatype
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar list-api
  (value ::= integer)
  (valopt ::= (some value) none)
  (vallist ::= (value vallist) empty)
  (method ::=  (cons value) nil)
  (interaction ::= (method interaction) empty))


(define (length-list l)
  (match l
    [(list-api empty) 0]
    [(list-api (v:value l-tl:vallist))
     (+ (length-list l-tl) 1)]))

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
;
; begin
;    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-grammar linked-list
  (value ::= integer)
  (valopt ::= (some value) none)
  (pointer ::= natural null) ; pointer is distance from begining of heap
  (cell ::= (value pointer))
  (heap ::= (cell heap) empty)
  (state ::= (pointer pointer heap)) ; (1) head of the list (2) head of the free-list (3) heap
  (method ::= (cons value) nil)
  (interaction ::= (method interaction) empty)) 

(define (empty-state s)
  (linked-list (null null empty)))

; Accessors for linked-list
(define (cell-value c)
  (match c
    [(linked-list (v:value _:pointer))
     (linked-list ,v)]))

(define (cell-pointer c)
  (match c
    [(linked-list (_:value p:pointer))
     (linked-list ,p)]))


(define (state-head s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (linked-list ,hd)]))
  
(define (state-heap s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (linked-list ,hp)]))


(define (destruct-state s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (list (linked-list ,hd) (linked-list ,fp) (linked-list ,hp))]))

  
; Replace the ith cell of hp with c, returns the modified hp and i.*next
(define (overwrite-heap i c hp)
  (match hp
    [(linked-list (hd-c:cell tl-hp:heap))
     (if (= 0 i)
         (match hd-c
           [(linked-list (_:value inext:pointer))
            (cons (linked-list (,c ,tl-hp)) (linked-list ,inext))])
         (let*-values ([(cons new-hp new-fp) (overwrite-heap (- i 1) c tl-hp)])
           (cons (linked-list (,hd-c ,new-hp)) new-fp)))]))

(define (length-heap h)
  (match h
    [(linked-list empty)
     0]
    [(linked-list (c:cell h-tl:heap))
     (+ (length-heap h-tl) 1)]))

    
; push v on top of heap (at the end of the list)
(define (snoc-heap c h)
  (match h
  [(linked-list empty)
   (linked-list (,c empty))]
  [(linked-list (hd-c:cell tl-hp:heap))
   (linked-list (,hd-c ,(snoc-heap c tl-hp)))]))
    

(define (cons-state v s)
  (match s
  [(linked-list (hd:pointer fp:pointer hp:heap))
   (match fp
     [(linked-list null) ; empty free-list, allocated new cell on top of hp
      (let* ([heap-size (length-heap hp)]
             [new-cell (linked-list (,v ,hd))]
             [new-heap (snoc-heap new-cell hp)])
        (linked-list (,heap-size null ,new-heap)))]
     [(linked-list i:integer); free-list is non-empty, use the head of the free-list.
      (let ([new-cell (linked-list (,v ,hd))])
            (let*-values ([(new-hp new-fp) (overwrite-heap i new-cell hp)])
              (linked-list (,i ,new-fp ,new-hp))))])]))



; return the nth element in the heap
(define (lookup-heap n hp)
  (match hp
    [(linked-list (hd-c:cell tl-hp:heap))          
     (if (equal? n 0)         
           (linked-list ,hd-c)
           (lookup-heap (- n 1) tl-hp))]))


; lookup the nth element of a list headed at hd in hp
(define (lookup-ll-inner n hd hp)
  (if (< n 0)
      (linked-list none)
      (let* ([c (lookup-heap hd hp)])
        (if (equal? n 0)
            (linked-list (some ,(cell-value c)))
            (match (cell-pointer c)
              [(linked-list null)
               (linked-list none)]
              [(linked-list ptr:natural) 
               (lookup-ll-inner (- n 1) (bonsai->number ptr) hp)])))))

(define (lookup-ll n s)
  (match s    
    [(linked-list (hd:pointer _:pointer hp:heap))
     (match hd
       [(linked-list null)
        (linked-list none)]
       [(linked-list hd:natural)
       (lookup-ll-inner n (bonsai->number hd) hp)])]))



#|
(define (interpret-interaction-ll ints s)
  (match ints
    [(linked-list empty) s]
    [(linked-list (m:method intss:interaction))
     (let-values ([(hd fp hp) (destruct-heap s)])
       (match m
         [(linked-list nil)                     
          (interpret-interaction-ll intss (linked-list (null ,hp)))]
         [(linked-list (cons n:value))
          (let* ([updated-hp (linked-list ((,n ,hd) ,hp))]) ; TODO: hd + 1 here
            (interpret-interaction-ll intss (linked-list (0 ,updated-hp))))]))]))
|#


; inner function for list-to-ll, produces a heap representing the ith -> end elements of the list
(define (list-to-ll-inner i l)
  (begin
    (displayln l)
    (match l
      [(list-api (hd:value empty))
       (linked-list ((,hd null) empty))]
      [(list-api (hd:value tl:vallist))
       (let* ([ii (+ i 1)]
              [h (list-to-ll-inner ii tl)]
              [c (linked-list (,hd ,ii))])
         (linked-list (,c ,h)))])))


(define (list-to-ll l)
  (match l
    [(list-api empty)
     (linked-list (null null empty))]
    [ _
      (let ([h (list-to-ll-inner 0 l)])
        (linked-list (0 null ,h)))]))

     
; Test for linked-list
(define abc-ll (list-to-ll abc))
(define b1-ll (linked-list ((cons 4) ((cons 1) empty))))
(define empty-ll (list-to-ll abstract-nil))
(define abc-heap (linked-list ((1 1) ((2 2) ((3 null) empty)))))
(define abc-state (linked-list (0 null ,abc-heap)))
(define heap-ll (linked-list ((1 null) empty)))

(displayln empty-ll)
(displayln (state-heap empty-ll))
(displayln (length-heap heap-ll))
(displayln abc-ll)
(displayln abc-state)
(displayln (length-heap abc-heap))
(displayln (state-heap abc-state))
(displayln (lookup-ll 1 abc-state))
(displayln (lookup-ll 2 abc-state))

;(displayln (length-heap (state-heap abc-ll)))
;(displayln (lookup-ll 1 abc-ll))
;(displayln (interpret-interaction-ll b1-ll abc-ll))


