#lang seec
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))


(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    [_ (raise-argument-error 'bonsai->number "bonsai-integer?" n)]
    ))

(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a language of API calls for a list datatype
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar list-api
  (value ::= integer)
  (vallist ::= (value vallist) empty)
  (method ::=  (cons value) nil) ; Could be renamed as constructor
  (operation ::= empty? head tail)
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

(define (abstract-empty? l)
  (match l
    [(list-api empty)
     #t]
    [ _
      #f]))


(define (abstract-head n l)
  (match l
    [(list-api (hd:value tl:vallist))
     hd]))

(define (abstract-tail n l)
  (match l
    [(list-api (hd:value tl:vallist))
     tl]))

(define (abstract-lookup n l)
  (match l
    [(list-api (hd:value tl:vallist))
     (if (equal? n 0)
         hd
         (abstract-lookup (- n 1) tl))]
    [(list-api empty)
     #f]))
    
(define (interpret-operation op l)
  (match op
    [(list-api empty?)
     (abstract-empty? l)]
     [(list-api head)
      (abstract-head l)]
     [(list-api tail)
      (abstract-tail l)
      ]))


(define (interpret-interaction ints l)
  (match ints
    [(list-api empty) l]
    [(list-api (m:method intss:interaction))
     (match m
       [(list-api nil)
        (interpret-interaction intss (list-api empty))]
       [(list-api (cons n:value))
        (interpret-interaction intss (list-api (,n ,l)))])]))

(define-language list-lang
  #:grammar list-api 
  #:expression interaction #:size 3
  #:context vallist #:size 6
  #:link cons
  #:evaluate (uncurry interpret-interaction))


; Tests for list

(define abc (list-api (1 (2 (3 empty)))))

(define b0 (list-api (nil ((cons 4) empty))))
(define b1 (list-api ((cons 4) ((cons 1) empty))))
(define b2 (list-api (nil ,b1)))

#|
(displayln (interpret-interaction b1 abc))
(displayln (interpret-interaction b2 abc))
(displayln (abstract-lookup 0 abc)) |#

(define (opt-equals? v1 v2)
  (if v1
      (if v2
          (equal? (bonsai->number v1) (bonsai->number v2))
          #f)
      (if v2
          #f
          #t)))
      
     
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define a linked-list datatype that will implement the list API
;
; begin
;    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-grammar linked-list
  (value ::= integer)
  (pointer ::= natural null) ; pointer is distance from begining of heap
  (cell ::= (value pointer))
  (heap ::= (cell heap) empty)
  (state ::= (pointer pointer heap)) ; (1) head of the list (2) head of the free-list (3) heap
  (method ::=  (cons value) nil) ; Could be renamed as constructor
  (interaction ::= (method interaction) empty)
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

; True if pointer p is scoped in a heap of size n
(define (scoped-pointer? ptr n)
  (match ptr
    [(linked-list null)
     #t]
    [(linked-list i:natural)
     (< (bonsai->number i) n)]))

; true if all pointers in heap h are scoped in a heap of size n
(define (scoped-heap? h n)
  (match h
    [(linked-list empty)
     #t]
    [(linked-list (hd-c:cell tl-h:heap))
     (and
      (scoped-pointer? (cell-pointer hd-c) n)
      (scoped-heap? tl-h n))]))

; true if all pointers in s are scoped (see scoped-pointer?)
(define (scoped-state? s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (let ([l-h (length-heap hp)])
       (and
        (scoped-pointer? hd l-h)
        (scoped-pointer? fp l-h)
        (scoped-heap? hp l-h)))]))

  
; Replace the ith cell of hp with c, returns the modified hp and i.*next
(define (overwrite-heap i c hp)
  (match hp
    [(linked-list (hd-c:cell tl-hp:heap))
     (if (= 0 i)
         (match hd-c
           [(linked-list (_:value inext:pointer))
            (list (linked-list (,c ,tl-hp))  (linked-list ,inext))])
         (let ([new-hp-fp (overwrite-heap (- i 1) c tl-hp)])
           (list (linked-list (,hd-c ,(first new-hp-fp))) (second new-hp-fp))))]))

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
      #f
      (let* ([c (lookup-heap hd hp)])
        (if (equal? n 0)
            (linked-list ,(cell-value c))
            (match (cell-pointer c)
              [(linked-list null)
               #f]
              [(linked-list ptr:natural) 
               (lookup-ll-inner (- n 1) (bonsai->number ptr) hp)])))))

(define (lookup-ll n s)
  (match s    
    [(linked-list (hd:pointer _:pointer hp:heap))
     (match hd
       [(linked-list null)
        #f]
       [(linked-list hd:natural)
       (lookup-ll-inner n (bonsai->number hd) hp)])]))




(define (interpret-interaction-ll ints s)
  (match ints
    [(linked-list empty)
     s]
    [(linked-list (m:method intss:interaction))
       (match m
         [(linked-list nil)                     
          (interpret-interaction-ll intss (nil-state s))]
         [(linked-list (cons n:value))
          (interpret-interaction-ll intss (cons-state n s))])]))

(define-language ll-lang
  #:grammar linked-list
  #:expression interaction #:size 3
  #:context state #:size 6
  #:link cons
  #:evaluate (uncurry interpret-interaction-ll))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Translation between list-api and linked-list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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


(define (list-to-ll-method m)
  (match m
    [(list-api nil)
     (linked-list nil)]
    [(list-api (cons n:value))
     (linked-list (cons ,n))]))

(define (list-to-ll-interaction ints)
  (match ints
    [(list-api empty) (linked-list empty)]
    [(list-api (m:method intss:interaction))
               (linked-list (,(list-to-ll-method m) ,(list-to-ll-interaction intss)))]))
  
     
; Test for linked-list
(define abc-ll (list-to-ll abc))
(define empty-ll (list-to-ll abstract-nil))
(displayln abc-ll)

#;(begin
    (displayln (scoped-state? abc-ll))
    (displayln (interpret-interaction-ll b1 abc-ll))
    (displayln [lookup-ll 1 abc-ll])
    (displayln (length-heap abc-heap))
    (displayln (lookup-ll 1 abc-state))
    ;(displayln (lookup-ll 2 abc-state))
    (displayln (state-heap empty-ll))
    ;(displayln (list-to-ll-inner 0 abc))
    ;(define abc-ll2 (linked-list (0 null ,(list-to-ll-inner 0 abc))))
    ;(displayln abc-ll2)
    ;(displayln (state-heap abc-ll2))   
    ;(displayln (length-heap (state-heap abc-ll)))
    ;(displayln (lookup-ll 1 abc-ll))
    ;(displayln (interpret-interaction-ll b1-ll abc-ll))    
    )

; Synthesis test

; 1 - Find a n s.t. lookup n (1 -> 2 -> 3) = Some 3
#;(begin
  (displayln "LL-synth test 1: symbolic lookup index")
  (define-symbolic* n* integer?)
  (define sol
    (solve (assert (opt-eq-ll? (lookup-ll n* abc-ll) 3))))
  (if (unsat? sol)
      (displayln "No model found")
    (begin
      (displayln "Model found.")
      (displayln "n...")
      (define n (concretize n* sol))
      (displayln n)
      (displayln "lookup n abc-ll...")
      (displayln (lookup-ll n abc-ll)))))

; 2 - Find a ll s.t. lookup 0 ll = Some 3
#;(begin
    (displayln "LL-synth test 2: symbolic linked-list")
    (define ll* (linked-list state 5))
    ;; Restrict to states where all pointers are scoped
    ;(assert (scoped-state? ll*)) 
    (define sol2
      (solve (assert (opt-eq-ll? (lookup-ll 0 ll*) 3))))
    (if (unsat? sol2)
        (displayln "No model found")
        (begin
          (displayln "Model found.")
          (displayln "ll...")
          (define ll (concretize ll* sol2))
          (displayln ll)
          (displayln "lookup n abc-ll...")
          (displayln (lookup-ll 0 ll)))))


; 3 Find an interaction i and a n s.t. lookup n (i abc-ll) = Some 4
#;(begin
  (displayln "LL-synth test 3: symbolic interaction")
  (define i* (list-api interaction 4))
  (define abc-ll-i* (interpret-interaction-ll i* abc-ll))
  (define sol3
    (solve (assert (opt-eq-ll? (lookup-ll 1 abc-ll-i*) 4))))
  (if (unsat? sol3)
      (displayln "No model found")
      (begin
        (displayln "Model found.")
        (displayln "i...")
        (define i (concretize i* sol3))
        (displayln i)
        (define abc-ll-i (interpret-interaction-ll i abc-ll))
        (displayln "lookup 1 (apply i abc-ll)...")
        (displayln [lookup-ll 1 abc-ll-i]))))





; LL p1 -> s1 -> p2 -> s2 -| , fl -|
; can we find a new fl pointer and interaction s.t.
; forall p2 s2, access ? (i (state')) = s2 where state' is state with new fl pointer
;
; Expected solution looks like
; fl switched to point to s1
; cons p3 s3
; can recover s2 (for any p2, s2) using s3


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Application on top of lists: association store
;
;    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Create an interaction representing storing (k, v) in association store
(define (store-value k v)
  (list-api ((cons ,v) ((cons ,k) empty))))


(define (get-value k l)
  (match l
    [(list-api empty)
     #f]
    [(list-api (kc:value tl:vallist))
     (match tl
       [(list-api (vc:value tll:vallist))
        (if (equal? (bonsai->number kc) (bonsai->number k))
            vc
            (get-value k tll))])]))

; Test for list association stores
(define s1 (list-api (0 (1 (2 (3 (4 (5 empty))))))))
(displayln s1)
;(define s2 (interpret-interaction (store-value (bonsai-integer 4) (bonsai-integer 10)) s1))
;(displayln s2)
;(displayln (get-value (bonsai-integer 4) s2))


(define (get-value-ll-inner fuel k hd hp)
  (if (<= fuel 0)
      #f
      (match hd
        [(linked-list null)
         #f]
        [(linked-list n:natural)
         (let* ([k-c (lookup-heap (bonsai->number n) hp)]
                [v-c (lookup-heap (bonsai->number (cell-pointer k-c)) hp)]
                [newhd (cell-pointer v-c)])
           #;(begin
             (displayln "in get-value-ll looking for")            
             (displayln k)
             (displayln k-c)
             (displayln v-c)
             (display "fuel")
             (display fuel))
             (if (equal? k (bonsai->number (cell-value k-c)))
                 (cell-value v-c)
                 (get-value-ll-inner (- fuel 1) k newhd hp)))])))


  
(define (get-value-ll k s)
  (match s
    [(linked-list (hd:pointer _:pointer hp:heap))
     (let ([fuel (length-heap hp)])
       (get-value-ll-inner 10 (bonsai->number k) hd hp))]))


; Tests for linked-list association stores
(define s1-ll (list-to-ll s1))
(displayln s1-ll)
(define s2-ll (interpret-interaction-ll (store-value (bonsai-integer 4) (bonsai-integer 10)) s1-ll))
(displayln s2-ll)
(displayln (get-value-ll (bonsai-integer 4) s2-ll))


; Now let's try modifying s1-ll's fp to be able to get the value 3 while looking up something different than 2 (its key)
(define as1-ll (linked-list (,(state-head s1-ll) 4 ,(state-heap s1-ll))))
(displayln as1-ll)
;(displayln (cons-state (bonsai-integer 7) as1-ll))
(define as2-ll (interpret-interaction-ll (store-value (bonsai-integer 6) (bonsai-integer 7)) as1-ll))
(displayln as2-ll)
;(displayln (get-value-ll (bonsai-integer 1) as2-ll))


; try to find a free pointer s.t. changed behavior between list and linked list
(define (modify-fp-state fp s)
  (linked-list (,(state-head s) ,fp ,(state-heap s))))

#;(begin
  (displayln "Store-Synth test 1: find a fp with behavior 7 -> 0")
  (define newfp* (linked-list pointer 1))
  (define as1-ll* (modify-fp-state newfp* s1-ll))
  ; Restrict to scoped states (i.e. newfp* is null or scoped on heap)
  (assert (scoped-state? as1-ll*))
  (define a-int (store-value (bonsai-integer 6) (bonsai-integer 7)))
  (define as2-ll* (interpret-interaction-ll a-int as1-ll*))
  (define sol-sst1
    (solve (assert (opt-equals? (get-value-ll (bonsai-integer 7) as2-ll*) (bonsai-integer 0)))))
  (if (unsat? sol-sst1)
      (displayln "No model found")
    (begin
      (displayln "Model found.")
      (displayln "fp...")
      (define newfp (concretize newfp* sol-sst1))
      (displayln newfp)
      )))

(begin
  (displayln "Store-Synth test 2: find a changed behavior between list and attacked linked-list")
  (current-bitwidth 4)
;  (define newfp* (linked-list null))
  (define newfp* (linked-list pointer 1))
  ;define as1-ll* s1-ll)
  (define as1-ll* (modify-fp-state newfp* s1-ll))
  ; Restrict to scoped states (i.e. newfp* is null or scoped on heap)
  (assert (scoped-state? as1-ll*))
  (define a-int (store-value (bonsai-integer 6) (bonsai-integer 7)))  
  (define s2 (interpret-interaction a-int s1))
  (define as2-ll* (interpret-interaction-ll a-int as1-ll*))
  (define-symbolic index* integer?)
  (define sol-sst2
    (verify (assert (opt-equals? (get-value index* s2) (get-value-ll index* as2-ll*)))))
  (if (unsat? sol-sst2)
      (displayln "No model found")
    (begin
      (displayln "Model found.")
      (displayln "fp...")
      (define newfp (concretize newfp* sol-sst2))
      (displayln newfp)
      (displayln "index...")
      (define index (concretize index* sol-sst2))
      (displayln index)
      (displayln "Source behavior")
      (define gis2 (get-value (bonsai-integer index) s2))
      (displayln gis2)
      (displayln "Target behavior")
;      (define as1-ll s1-ll)
      (define as1-ll (modify-fp-state newfp s1-ll))
      (define as2-ll (interpret-interaction-ll a-int as1-ll))
      (define gias2ll (get-value-ll (bonsai-integer index) as2-ll))
      (displayln gias2ll)
      (displayln "Result:")
      (displayln (opt-equals? gis2 gias2ll))
     )))
