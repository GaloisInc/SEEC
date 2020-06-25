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

(define b0 (list-api (nil ((cons 4) empty))))
(define b1 (list-api ((cons 4) ((cons 1) empty))))
(define b2 (list-api (nil ,b1)))

#|
(displayln (interpret-interaction b1 abc))
(displayln (interpret-interaction b2 abc))
(displayln (abstract-lookup 0 abc)) |#


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
) 

(define (empty-state s)
  (linked-list (null null empty)))

; Accessors for linked-list
(define (cell-value c)
  (match c
    [(linked-list (v:value _:pointer))
     v]))

(define (cell-pointer c)
  (match c
    [(linked-list (_:value p:pointer))
     p]))

(define (state-head s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     hd]))
  
(define (state-heap s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     hp]))
  
; Replace the ith cell of hp with c, returns the modified hp and i.*next
(define (overwrite-heap i c hp)
  (match hp
    [(linked-list (hd-c:cell tl-hp:heap))
     (if (= 0 i)
         (match hd-c
           [(linked-list (_:value inext:pointer))
            (list (linked-list (,c ,tl-hp))  (linked-list ,inext))])
         (let*-values ([(cons new-hp new-fp) (overwrite-heap (- i 1) c tl-hp)])
           (list (linked-list (,hd-c ,new-hp)) new-fp)))]))

(define (length-heap h)
  (match h
    [(linked-list empty)
     0]
    [(linked-list (c:cell h-tl:heap))
     (+ (length-heap h-tl) 1)]))

; n1:natural, ptr2:pointer, hp:heap
; append l2 at the end of l1
(define (append-ll n1 ptr2 hp)
  (let ([hd1 (lookup-heap n1 hp)])        
    (match hd1
      [(linked-list (v:value null))
       (let ([newhd1 (linked-list (,v ,ptr2))])
         (overwrite-heap n1 newhd1 hp))]
      [(linked-list (_:value n:natural))
       (append-ll n ptr2 hp)])))


; push v on top of heap (at the end of the list)
(define (snoc-heap c h)
  (match h
    [(linked-list empty)
     (linked-list (,c empty))]
    [(linked-list (hd-c:cell tl-hp:heap))
     (linked-list (,hd-c ,(snoc-heap c tl-hp)))]))


(define (nil-state s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (match fp
       [(linked-list null)
        (linked-list (null ,hd ,hp))]
       [(linked-list n:natural)
        (let ([newhp (append-ll n hd hp)])
          (linked-list (null ,fp ,newhp)))])]))

; Add a cell with (v, hd) in front of the hd-list represented in hp
(define (cons-state v s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (match fp
       [(linked-list null) ; empty free-list, allocated new cell on top of hp
        (let* ([heap-size (length-heap hp)]
               [new-cell (linked-list (,v ,hd))]
               [new-heap (snoc-heap new-cell hp)])
          (linked-list (,(bonsai-integer heap-size) null ,new-heap)))]
       [(linked-list i:natural); free-list is non-empty, use the head of the free-list.
        (let* ([new-cell (linked-list (,v ,hd))]
               [new-hp-fp (overwrite-heap (bonsai->number i) new-cell hp)])
          (linked-list (,i ,(second new-hp-fp) ,(first new-hp-fp))))])]))
  


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




(define (interpret-interaction-ll ints s)
  (match ints
    [(list-api empty)
     s]
    [(list-api (m:method intss:interaction))
       (match m
         [(list-api nil)                     
          (interpret-interaction-ll intss (nil-state s))]
         [(list-api (cons n:value))
          (interpret-interaction-ll intss (cons-state n s))])]))



; inner function for list-to-ll, produces a heap representing the ith -> end elements of the list
(define (list-to-ll-inner i l)
  (match l
    [(list-api (hd:value empty))
     (linked-list ((,hd null) empty))]
    [(list-api (hd:value tl:vallist))
     (let* ([ii (+ i 1)]
            [h (list-to-ll-inner ii tl)]
            [c (linked-list (,hd ,(bonsai-integer ii)))])
       (linked-list (,c ,h)))]))


(define (list-to-ll l)
  (match l
    [(list-api empty)
     (linked-list (null null empty))]
    [ _
      (let ([h (list-to-ll-inner 0 l)])
        (linked-list (0 null ,h)))]))

     
; Test for linked-list
(define abc-ll (list-to-ll abc))
(define empty-ll (list-to-ll abstract-nil))



(displayln (interpret-interaction-ll b1 abc-ll))


#|
(displayln (length-heap abc-heap))
(displayln (lookup-ll 1 abc-state))
;(displayln (lookup-ll 2 abc-state))
(displayln (state-heap empty-ll))
;(displayln (list-to-ll-inner 0 abc))
;(define abc-ll2 (linked-list (0 null ,(list-to-ll-inner 0 abc))))
;(displayln abc-ll2)
;(displayln (state-heap abc-ll2))

|#
;(displayln (length-heap (state-heap abc-ll)))
;(displayln (lookup-ll 1 abc-ll))
;(displayln (interpret-interaction-ll b1-ll abc-ll))


