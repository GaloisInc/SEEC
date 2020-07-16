#lang seec

(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    [_ (raise-argument-error 'bonsai->number "bonsai-integer?" n)]
    ))

(define (snoc a b)
  (cons b a))

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
  (method ::=  (mcons value) mnil) 
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

(define (abstract-nth n l)
  (match l
    [(list-api (hd:value tl:vallist))
     (if (equal? n 0)
         hd
         (abstract-nth (- n 1) tl))]
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
       [(list-api (mcons n:value))
        (interpret-interaction intss (list-api (,n ,l)))])]))

(define-language list-lang
  #:grammar list-api 
  #:expression interaction #:size 3
  #:context vallist #:size 6
  #:link snoc
  #:evaluate (uncurry interpret-interaction))

; Tests for list

(define abc (list-api (1 (2 (3 empty)))))

(define b0 (list-api (mnil ((mcons 4) empty))))
(define b1 (list-api ((mcons 4) ((mcons 1) empty))))
(define b2 (list-api (mnil ,b1)))

#|
(displayln (interpret-interaction b1 abc))
(displayln (interpret-interaction b2 abc))
(displayln (abstract-nth 0 abc)) |#

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
  (pointer ::= natural null) ; pointer is distance from beginning of heap
  (cell ::= (value pointer))
  (heap ::= (cell heap) empty)
  (state ::= (pointer pointer heap)) ; (1) head of the list (2) head of the free-list (3) heap
  (method ::=  (mcons value) mnil) ; Could be renamed as constructor
  (interaction ::= (method interaction) empty))

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

(define (state-free-pointer s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     fp]))

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
  (let ([hd1 (nth-heap n1 hp)])        
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
(define (nth-heap n hp)
  (match hp
    [(linked-list (hd-c:cell tl-hp:heap))          
     (if (equal? n 0)         
           (linked-list ,hd-c)
           (nth-heap (- n 1) tl-hp))]))

; lookup the nth element of a list headed at hd in hp
(define (nth-ll-inner n hd hp)
  (if (< n 0)
      #f
      (let* ([c (nth-heap hd hp)])
        (if (equal? n 0)
            (linked-list ,(cell-value c))
            (match (cell-pointer c)
              [(linked-list null)
               #f]
              [(linked-list ptr:natural) 
               (nth-ll-inner (- n 1) (bonsai->number ptr) hp)])))))

(define (nth-ll n s)
  (match s    
    [(linked-list (hd:pointer _:pointer hp:heap))
     (match hd
       [(linked-list null)
        #f]
       [(linked-list hd:natural)
       (nth-ll-inner n (bonsai->number hd) hp)])]))

(define (interpret-interaction-ll ints s)
  (match ints
    [(linked-list empty)
     s]
    [(linked-list (mnil intss:interaction))
     (interpret-interaction-ll intss (nil-state s))]
    [(linked-list ((mcons n:value) intss:interaction))
     (interpret-interaction-ll intss (cons-state n s))]
    ))

(define-language ll-lang
  #:grammar linked-list
  #:expression interaction #:size 3
  #:context state #:size 6
  #:link snoc
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
    [(list-api mnil)
     (linked-list mnil)]
    [(list-api (mcons n:value))
     (linked-list (mcons ,n))]))

(define (list-to-ll-interaction ints)
  (match ints
    [(list-api empty) (linked-list empty)]
    [(list-api (m:method intss:interaction))
               (linked-list (,(list-to-ll-method m) ,(list-to-ll-interaction intss)))]))

; Comparing vallist l with the linked-list headed at fp in hp
(define (list-to-ll-equal?-inner l fp hp)
  (match l
    [(list-api (hd:value tl:vallist))
     (match fp 
       [(linked-list n:natural)
        (let ([hd-ll (nth-heap (bonsai->number n) hp)])
          (if (equal? (bonsai->number hd) (bonsai->number (cell-value hd-ll)))
              (list-to-ll-equal?-inner tl (cell-pointer hd-ll) hp)
              #f))]
       [(linked-list null)
        #f])]
    [(list-api empty)
     (match fp
       [(linked-list null)
        #t]
       [ _
         #f])]))

; list -> linked-list (state) -> bool
(define (list-to-ll-equal? l s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (list-to-ll-equal?-inner l hd hp)]))

(define-compiler list-to-ll-compiler
  #:source list-lang
  #:target ll-lang
  #:behavior-relation list-to-ll-equal?
  #:context-relation list-to-ll-equal?
  #:compile (lambda (i) i))


#;(begin
  (displayln "Trying to find a trace with different behavior under compilation")
  (let* ([gen (make-query-changed-component list-to-ll-compiler)]
         [witness (gen)])
    (display-changed-behavior witness displayln)))




  
     
; Test for linked-list
(define abc-ll (list-to-ll abc))
(define empty-ll (list-to-ll abstract-nil))
(define i-000 (list-api ((mcons 0) ((mcons 0) ((mcons 0) empty)))))

#;(begin
    (displayln abstract-nil)
    (displayln (interpret-interaction i-000 abstract-nil))
    (displayln empty-ll)
    (displayln (interpret-interaction-ll i-000 empty-ll)))

#;(begin
    (displayln abc-ll)
    (displayln (list-to-ll-equal? abc abc-ll))
    (displayln (scoped-state? abc-ll))
    (displayln (interpret-interaction-ll b1 abc-ll))
    (displayln [nth-ll 1 abc-ll])
    (displayln (length-heap abc-heap))
    (displayln (nth-ll 1 abc-state))
    ;(displayln (nth-ll 2 abc-state))
    (displayln (state-heap empty-ll))
    ;(displayln (list-to-ll-inner 0 abc))
    ;(define abc-ll2 (linked-list (0 null ,(list-to-ll-inner 0 abc))))
    ;(displayln abc-ll2)
    ;(displayln (state-heap abc-ll2))   
    ;(displayln (length-heap (state-heap abc-ll)))
    ;(displayln (nth-ll 1 abc-ll))
    ;(displayln (interpret-interaction-ll b1-ll abc-ll))    
    )

; Linked-List Synthesis Test

; 1 - Find a n s.t. nth n (1 -> 2 -> 3) = Some 3
(define (sll1) (begin
     (displayln "LL-synth test 1: symbolic nth index")          
     (define n* (linked-list value 1))
     (define sol
       (solve (assert (opt-equals? (nth-ll n* abc-ll) 3))))
     (if (unsat? sol)
         (displayln "No model found")
         (begin
           (displayln "Model found.")
           (displayln "n...")
           (define n (concretize n* sol))
           (displayln n)
           (displayln "nth n abc-ll...")
      (displayln (nth-ll n abc-ll))))))
#;(sll1)

; 2 - Find a ll s.t. nth 0 ll = Some 3
(define (sll2) (begin
    (displayln "LL-synth test 2: symbolic linked-list")
    (define ll* (linked-list state 5))
    ;; Restrict to states where all pointers are scoped
    ;(assert (scoped-state? ll*)) 
    (define sol2
      (solve (assert (opt-equals? (nth-ll 0 ll*) 3))))
    (if (unsat? sol2)
        (displayln "No model found")
        (begin
          (displayln "Model found.")
          (displayln "ll...")
          (define ll (concretize ll* sol2))
          (displayln ll)
          (displayln "nth n abc-ll...")
          (displayln (nth-ll 0 ll))))))
#;(sll2)


; 3 Find an interaction i and a n s.t. nth n (i abc-ll) = Some 4
(define (sll3) (begin
  (displayln "LL-synth test 3: symbolic interaction")
  (define i* (list-api interaction 4))
  (define abc-ll-i* (interpret-interaction-ll i* abc-ll))
  (define sol3
    (solve (assert (opt-equals? (nth-ll 1 abc-ll-i*) 4))))
  (if (unsat? sol3)
      (displayln "No model found")
      (begin
        (displayln "Model found.")
        (displayln "i...")
        (define i (concretize i* sol3))
        (displayln i)
        (define abc-ll-i (interpret-interaction-ll i abc-ll))
        (displayln "nth 1 (apply i abc-ll)...")
        (displayln [nth-ll 1 abc-ll-i])))))
#;(sll3)


; 4 Shows that list-to-ll is correct, i.e. no changed behavior between l and (list-to-ll l)
(define (sll4) (begin
  (displayln "LL-synth test 4: Verifying l-to-ll")
  (define l*-t4 (list-api vallist 4))
  (define ll*-t4 (list-to-ll l*-t4))
  (define sol-t4
    (verify (assert (list-to-ll-equal? l*-t4 ll*-t4))))
  (if (unsat? sol-t4)
      (displayln "Verified")
      (begin
        (displayln "Counter-example found.")
        (define l-t4 (concretize l*-t4 sol-t4))
        (displayln l-t4)
        (displayln (list-to-ll l-t4))))))
#;(sll4)

; 5 Shows that interactions preserve the correspondence between lists and translated linked-lists
(define (sll5) (begin
  (displayln "LL-synth test 5: verifying interactions post list-to-ll")
  (define l*-t5 (list-api vallist 5))
  (define ll*-t5 (list-to-ll l*-t5))
  (define i*-t5 (list-api interaction 5))
  (define l2*-t5 (interpret-interaction i*-t5 l*-t5))
  (define ll2*-t5 (interpret-interaction-ll i*-t5 ll*-t5))
  (define sol-t5
    (verify (assert (list-to-ll-equal? l2*-t5 ll2*-t5))))
  (if (unsat? sol-t5)
      (displayln "Verified")
      (begin
        (displayln "Counter-example found.")
        (define l-t5 (concretize l*-t5 sol-t5))
        (define i-t5 (concretize i*-t5 sol-t5))
        (displayln "Initial list:")
        (displayln l-t5)
        (displayln "Translated ll:")
        (define ll-t5 (list-to-ll l-t5))
        (displayln ll-t5)
        (displayln "Interaction:")
        (displayln i-t5)
        (displayln "Resulting list:")
        (define l2-t5 (interpret-interaction i-t5 l-t5))
        (displayln l2-t5)
        (displayln "Resulting linked-list:")
        (define ll2-t5 (interpret-interaction-ll i-t5 ll-t5))
        (displayln ll2-t5)
        (displayln "l2 =? ll2:")
        (displayln (list-to-ll-equal? l2-t5 ll2-t5))))))
#;(sll5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Application on top of lists: association store
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Create an interaction representing storing (k, v) in association store
(define (store-value k v)
  (list-api ((mcons ,v) ((mcons ,k) empty))))

(define (lookup k l)
  (match l
    [(list-api empty)
     #f]
    [(list-api (kc:value tl:vallist))
     (match tl
       [(list-api (vc:value tll:vallist))
        (if (equal? (bonsai->number kc) (bonsai->number k))
            vc
            (lookup k tll))])]))

; Test for list association stores
(define s1 (list-api (0 (1 (2 (3 (4 (5 empty))))))))
;(displayln s1)
;(define s2 (interpret-interaction (store-value (bonsai-integer 4) (bonsai-integer 10)) s1))
;(displayln s2)
;(displayln (nth (bonsai-integer 4) s1))

(define (lookup-ll-inner fuel k hd hp)
  (if (<= fuel 0)
      #f
      (match hd
        [(linked-list null)
         #f]
        [(linked-list n:natural)
         (let* ([k-c (nth-heap (bonsai->number n) hp)]
                [v-c (nth-heap (bonsai->number (cell-pointer k-c)) hp)]
                [newhd (cell-pointer v-c)])
             (if (equal? k (bonsai->number (cell-value k-c)))
                 (cell-value v-c)
                 (lookup-ll-inner (- fuel 1) k newhd hp)))])))

; Bound on fuel provided to recursive functions
(define rec-bound 10)

(define (lookup-ll k s)
  (match s
    [(linked-list (hd:pointer _:pointer hp:heap))
     (lookup-ll-inner rec-bound (bonsai->number k) hd hp)]))

; Tests for linked-list association stores
(define s1-ll (list-to-ll s1))
(define s2-ll (interpret-interaction-ll (store-value (bonsai-integer 4) (bonsai-integer 10)) s1-ll))
#;(begin
    (displayln s1-ll)
    (displayln s2-ll)
    (displayln (lookup-ll (bonsai-integer 4) s2-ll)))

(define as1-ll (linked-list (,(state-head s1-ll) 4 ,(state-heap s1-ll))))
(define as2-ll (interpret-interaction-ll (store-value (bonsai-integer 6) (bonsai-integer 7)) as1-ll))
#;(begin 
    (displayln as1-ll)
    (displayln (cons-state (bonsai-integer 7) as1-ll))
    (displayln as2-ll)
    (displayln (lookup-ll (bonsai-integer 1) as2-ll)))


; try to find a free pointer s.t. changed behavior between list and linked list
(define (modify-fp-state fp s)
  (linked-list (,(state-head s) ,fp ,(state-heap s))))


(define (ss0) (begin
  (displayln "Store-Styn test 0 : find a key that returns 1")
  (define index* (linked-list value 1))
  (define gv (lookup index* s1))
  (define sol-sst0 (solve
                    (assert (opt-equals? gv (bonsai-integer 1)))))
  (if (unsat? sol-sst0)
      (displayln "No model found")
      (begin
        (displayln "Model found.")
        (displayln "index...")
        (define index (concretize index* sol-sst0))
        (displayln index)))))
#;(ss0)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Association list API
;
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-grammar alist-api
  (value   ::= integer null)
  (key     ::= integer)
  (alist ::= (key value alist) empty)
  (method  ::= (add-elem key value) reset)
  (interaction ::= (method interaction) empty)
  (operation ::= (lookup key) empty?)
  )

(define (interpret-interaction-assoc ints al)
  (match ints
    [(alist-api empty) al]
    [(alist-api (reset ints+:interaction))
     (interpret-interaction-assoc ints+ (alist-api empty))]
    [(alist-api ((add-elem k:key v:value) ints+:interaction))
     (interpret-interaction-assoc ints+ (alist-api (,k ,v ,al)))]
    ))
; input: an alist interaction
; output: a linked-list interaction
(define (alist->ll-interaction ints)
  (match ints
    [(alist-api empty) (linked-list empty)]
    [(alist-api ((add-elem k:key v:value) ints+:interaction))
     (linked-list ((mcons ,v) ((mcons ,k) ,(alist->ll-interaction ints+))))]
    [(alist-api (reset ints+:interaction))
     (linked-list (mnil ,(alist->ll-interaction ints+)))]
    ))

; returns either the value pointed to by the key in the association list al, or
; null if the key does not appear in the list
(define (alist-lookup al k)
  (match al
    [(alist-api empty) #f]
    [(alist-api (k+:key v+:value al+:alist))
     (if (equal? k k+)
         v+
         (alist-lookup al+ k))]))

; op: an alist-api operation
; s: a linked-list state
(define (alist->ll-operation op s)
  (match op
    [(alist-api (lookup k:key))
     (lookup-ll k s)]
    [(alist-api empty?)
     (equal? (state-head s) (linked-list null))]
    ))

(define (alist->list al)
  (match al
    [(alist-api empty) (list-api empty)]
    [(alist-api (k:key v:value al+:alist))
     (list-api (,k (,v ,(alist->list al+))))]))

(define (alist->ll al) (list-to-ll (alist->list al)))

; True if i is a key or a value in alist al
(define (alist-in al i)
  (match al
    [(alist-api empty) #f]
    [(alist-api (k+:key v+:value al+:alist))
     (if (or (equal? i k+) (equal? i v+))
         #t
         (alist-in al+ i))]))

; True if i is a key or a value in interaction ints
(define (alist-ints-in ints i)
  (match ints
    [(alist-api empty)
     #f]
    [(alist-api ((add-elem k+:key v+:value) ints+:interaction))
     (if (or (equal? i k+) (equal? i v+))
         #t
         (alist-ints-in ints+ i))]))

(define (ss1) (begin

  (define al1 (alist-api (0 1 (2 3 (4 5 empty)))))
  (displayln "al1...")
  (displayln al1)

  (define al1-ll (alist->ll al1))
  (displayln "al1-ll...")
  (displayln al1-ll)

  (displayln "Store-Synth test 1: find a fp with behavior 7 -> 0 from the al grammar")
  (define newfp* (linked-list pointer 1))
  #;(define as1-ll (modify-fp-state newfp* s1-ll))
  (define al1-ll* (match al1-ll
                     [(linked-list (hp:pointer _:pointer h:heap))
                      (linked-list (,hp ,newfp* ,h))]))
  (displayln "al1-ll*...")
  (displayln al1-ll*)

  ; Restrict to scoped states (i.e. newfp* is null or scoped on heap)
  (assert (scoped-state? al1-ll*))

  (define a-int (alist-api ((add-elem 6 7) empty)))
  (define ll-int (alist->ll-interaction a-int))
  (displayln "ll-int...")
  (displayln ll-int)
  (define al2-ll* (interpret-interaction-ll ll-int al1-ll*))

  (define lookup-7 (lookup-ll (bonsai-integer 7) al2-ll*))

  (define sol-sst1
    (solve (assert (opt-equals? lookup-7 (bonsai-integer 0)))))
  (if (unsat? sol-sst1)
      (displayln "No model found")
    (begin
      (displayln "Model found.")
      (displayln "fp...")
      (define newfp (concretize newfp* sol-sst1))
      (displayln newfp)
      (define al2-ll (interpret-interaction-ll ll-int (modify-fp-state newfp s1-ll)))
      (displayln "al2-ll...")
      (displayln al2-ll)
      (displayln "get 7 al2-ll...")
      (displayln (lookup-ll (bonsai-integer 7) al2-ll))
     ))))
#;(ss1)

(define (ss2) (begin
  (displayln "Store-Synth test 2: find a changed behavior between list and attacked linked-list")
  (current-bitwidth 4)

  (define al (alist-api (0 1 (2 3 (4 5 empty)))))
  (displayln "al...")
  (displayln al)

  (define al-ll (alist->ll al))
  (displayln "al-ll...")
  (displayln al-ll)

  (define newfp* (linked-list pointer 1))
  (define al-ll* (modify-fp-state newfp* al-ll))
  ; Restrict to scoped states (i.e. newfp* is null or scoped on heap)
  (assert (scoped-state? al-ll*))

  (define a-int (alist-api ((add-elem 6 7) empty)))
  (define ll-int (alist->ll-interaction a-int))
  (displayln "ll-int...")
  (displayln ll-int)

  (define al+ (interpret-interaction-assoc a-int al))
  (define al+-ll (interpret-interaction-ll ll-int al-ll))
  (define al+-ll* (interpret-interaction-ll ll-int al-ll*))

  ; symbolic index
  (define index* (linked-list value 1))

  (define v* (lookup-ll index* al+-ll*))
  (define v (lookup-ll index* al+-ll))

  ; Below are some example of assertion to tweak the model found:
  ; ensures that the behavior is not destructive (i.e. gas2-ll* is not #f)
  ;(assert v*)
  ; ensures that the behavior is new
  ; (assert (not v))

  ; In particular, we can find our desired attack by
  ; requiring key (index) to be known to attacker, and result (value) to be private
  (assert (or (equal? index* (bonsai-integer 7)) (equal? index* (bonsai-integer 6))))
  (assert (not (or (equal? v* (bonsai-integer 7)) (equal? v* (bonsai-integer 6)))))
  (define r (opt-equals? v v*))
  (define sol-sst2 (synthesize #:forall '()
                               #:guarantee (assert (not r))))
  (if (unsat? sol-sst2)
      (displayln "No model found")
    (begin
      (displayln "Model found.")
      (displayln "fp...")
      (define newfp-index (concretize (cons newfp* index*) sol-sst2))
      (define newfp (car newfp-index))
      (define index (cdr newfp-index))
      (displayln newfp)
      (displayln "index...")
;      (define index (concretize index* sol-sst2))
      (displayln index)
      (displayln "Source linked-list after interaction")
      (displayln al+)
      (define v+ (alist-lookup al+ index))
      #;(define gis2 (lookup-ll index al+))
      (displayln "Source behavior of (lookup index)")
      (displayln v+)

      (define al-ll-modified (modify-fp-state newfp al-ll))
      (define al+-ll-modified (interpret-interaction-ll ll-int al-ll-modified))
      (displayln "Attacked linked-list after interaction")
      (displayln al+-ll-modified)
      (define v+-ll (lookup-ll index al+-ll-modified))
      (displayln "Target behavior of (lookup index)")
      (displayln v+-ll)
      (displayln "Result:")
      (displayln (opt-equals? v+ v+-ll))
     ))))
#;(ss2)

(define (ss3) (begin
  (displayln "Store-Synth test 3: Synthesize an attack on linked-list valid on any association list")
  (current-bitwidth 4)

  (define al* (alist-api alist 4))

  (define al-ll* (alist->ll al*))

  (define a-fp* (linked-list pointer 1))
  ; al as an attacked ll
  (define al-all* (modify-fp-state a-fp* al-ll*))
  ; Restrict to scoped states (i.e. a-fp* is null or scoped on heap)
  (assert (scoped-state? al-all*))

  (define a-key* (alist-api key 1))
  (define a-val* (alist-api value 1))
  (assert (equal? (lookup-ll a-key* al-ll*) #f))
  (assert (equal? (lookup-ll a-val* al-ll*) #f))

  (define a-int* (alist-api ((add-elem ,a-key* ,a-val*) empty)))
  
  (define ll-int* (alist->ll-interaction a-int*))

  (define al+* (interpret-interaction-assoc a-int* al*))
  (define al+-ll* (interpret-interaction-ll ll-int* al-ll*))
  (define al+-all* (interpret-interaction-ll ll-int* al-all*))

  ; symbolic index
  (define index* (linked-list value 1))

  (define v* (lookup-ll index* al+-all*))
  (define v (lookup-ll index* al+-ll*))

  ; We can find our desired attack by requiring:
  ; 1) the key (index) is known to attacker.
  (assert (or (equal? a-key* index*)
              (equal? a-val* index*)))
  ; 2) the result (value) is not known to the attacker.
  (assert (alist-in al* v*))
  
  (define r (opt-equals? v v*))

  (define sol-sst3 (synthesize #:forall al*
                               #:guarantee (assert (not r))))
  (if (unsat? sol-sst3)
      (displayln "No model found")
    (begin
      (displayln "Model found.")
      (displayln "")
      (define concrete-vars (concretize (list a-fp* index* a-key* a-val*) sol-sst3))      
      (define a-fp (first concrete-vars))
      (define index (second concrete-vars))
      (define a-key (third concrete-vars))
      (define a-val (fourth concrete-vars))
      (define a-int (alist-api ((add-elem ,a-key ,a-val) empty)))
      (define ll-int (alist->ll-interaction a-int))

      ; Generate some list that respects the restrictions on al*
      (clear-asserts!)
      (define fresh-al* (alist-api alist 4))
      (define fresh-al-ll* (alist->ll fresh-al*))
      (define fresh-al-all* (modify-fp-state a-fp fresh-al-ll*))
      (assert (scoped-state? fresh-al-all*))
      (define sol-fresh-al (solve (assert (not (or (alist-in fresh-al* a-key) (alist-in fresh-al* a-val))))))
      (define example-vars (concretize (list fresh-al* fresh-al-ll* fresh-al-all*) sol-fresh-al))
      (define al (first example-vars))
      (define al-ll (second example-vars))
      (define al-all (third example-vars))
      (define al+ (interpret-interaction-assoc a-int al))
      (define al+-ll (interpret-interaction-ll ll-int al-ll))
      (define al+-all (interpret-interaction-ll ll-int al-all))
      

      (displayln "Attack key/value")
      (displayln a-int)
      (displayln "Attack fp...")
      (displayln a-fp)
      (displayln "Index...")
      (displayln index)
      (displayln "")
      
      (displayln "Source list")
      (displayln al)
      (displayln "Source list after interaction")
      (displayln al+)
      (define v+ (alist-lookup al+ index))
      (displayln "Source behavior of (lookup index)")
      (displayln v+)
      (displayln "")
      
      (displayln "Translated linked-list")
      (displayln al-ll)
      (displayln "Translated linked-list after interaction")
      (displayln al+-ll)
      (displayln "")
      
      (displayln "Attacked linked-list")
      (displayln al-all)
      (displayln "Attacked linked-list after interaction")
      (displayln al+-all)
      (define v+-ll (lookup-ll index al+-all))
      (displayln "Target behavior of (lookup index)")
      (displayln v+-ll)
      ))))
(ss3)