#lang seec
(require racket/format)
(require racket/contract)
(require (file "list-lang.rkt"))

(require (only-in racket/base
                  make-parameter
                  parameterize))

(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(provide (all-defined-out))
(require rosette/lib/value-browser)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Linked List 
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-grammar linked-list
  (value ::= integer)
  (pointer ::= natural null) ; pointer is distance from beginning of heap
  (cell ::= (value pointer))
  (heap ::= (cell heap) empty)
  (state ::= (pointer pointer heap)) ; (1) head of the list (2) head of the free-list (3) heap
  (method ::=  (mcons value) mnil)
  (interaction ::= (method interaction) empty)
  (observation ::= (lookup value) empty?)
  (complete-interaction ::= (interaction observation))
  (attack ::= (change-free-pointer pointer))
  (attacked-complete-interaction ::= (attack complete-interaction)))


; Bound on fuel provided to recursive functions
(define rec-bound (make-parameter 10))


(define (pointer->number p)
  (match p
    [(linked-list n:natural) n]
    [_ (raise-argument-error 'pointer->number
                             "non-null linked-list-pointer?"
                             p)]
    ))


(define (heap-length hp)
  (match hp
    [(linked-list empty) 0]
    [(linked-list (cell hp+:heap)) (+ 1 (heap-length hp+))]
    ))

(define (empty-state s)
  (linked-list (null null empty)))


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

(define (change-free-pointer s p)
  (match s
    [(linked-list (hd:pointer _:pointer hp:heap))
     (linked-list (,hd ,p ,hp))]))

; True if pointer p is scoped in a heap of size n
(define (scoped-pointer? ptr n)
  (match ptr
    [(linked-list null)
     #t]
    [(linked-list i:natural)
     (< i n)]))

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
;
; NOTE: even with a small fuel size like 5, when the heap is a union of a large
; number of possibilities (which occurs when it is generated from overwrite-heap
; and append-ll-even), this makes it very slow
(define (append-ll-inner fuel n1 ptr2 hp)
  #;(printf "append-ll-inner: ~a~n" fuel)
  (cond
    [(<= fuel 0) (raise-arguments-error 'append-ll-inner
                                        "ran out of fuel")]
    [else
     (let ([hd1 (nth-heap n1 hp)])
       (match hd1
         [(linked-list (v:value null))
          (let ([newhd1 (linked-list (,v ,ptr2))])
            (first (overwrite-heap n1 newhd1 hp)))]
         [(linked-list (_:value n:natural))
          (append-ll-inner (- fuel 1) n ptr2 hp)]))]
    ))
(define (append-ll n1 ptr2 hp)
    (append-ll-inner (rec-bound) n1 ptr2 hp))


; push v on top of heap (at the end of the list)
(define (snoc-heap c h)
  #;(-> linked-list-cell? linked-list-heap? linked-list-heap?)
  (match h
    [(linked-list empty)
     (linked-list (,c empty))]
    [(linked-list (hd-c:cell tl-hp:heap))
     (linked-list (,hd-c ,(snoc-heap c tl-hp)))]))

(define (nil-state s)
  #;(printf "(nil-state)~n")
  (for/all ([s s])
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (match fp
       [(linked-list null)
        (linked-list (null ,hd ,hp))]
       [(linked-list n:natural)
        (let ([newhp (append-ll n hd hp)])
          (linked-list (null ,fp ,newhp)))])])))

; Add a cell with (v, hd) in front of the hd-list represented in hp
(define (cons-state v s)
  #;(printf "(cons-state)~n")
  (for/all ([s s])
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (match fp
       [(linked-list null) ; empty free-list, allocated new cell on top of hp
        (let* ([heap-size (length-heap hp)]
               [new-cell (linked-list (,v ,hd))]
               [new-heap (snoc-heap new-cell hp)])
          (linked-list (,heap-size null ,new-heap)))]
       [(linked-list i:natural); free-list is non-empty, use the head of the free-list.
          (let* ([new-cell (linked-list (,v ,hd))]
                 [new-hp-fp (overwrite-heap i new-cell hp)])
            (linked-list (,i ,(second new-hp-fp) ,(first new-hp-fp))))])])))

; return the nth element in the heap
(define (nth-heap n hp)
  (match hp
    [(linked-list (hd-c:cell tl-hp:heap))
     (if (= n 0)
         hd-c
         (nth-heap (- n 1) tl-hp))]))

; lookup the nth element of a list headed at hd in hp
#;(define (nth-ll-inner n hd hp)
  (if (< n 0)
      #f
      (let* ([c (nth-heap hd hp)])
        (if (equal? n 0)
            (linked-list ,(cell-value c))
            (match (cell-pointer c)
              [(linked-list null)
               #f]
              [(linked-list ptr:natural) 
               (nth-ll-inner (- n 1) ptr hp)])))))

#;(define (nth-ll n s)
  (match s    
    [(linked-list (hd:pointer _:pointer hp:heap))
     (match hd
       [(linked-list null)
        #f]
       [(linked-list hd:natural)
       (nth-ll-inner n hd hp)])]))

(define (interpret-interaction-ll ints s)
  #;(printf "(interpret-interaction-ll ~a)~n" ints)
  #;(display-state s)
  (for/all ([ints ints])
  (match ints
    [(linked-list empty)
     s]
    [(linked-list (mnil intss:interaction))
     (interpret-interaction-ll intss (nil-state s))]
    [(linked-list ((mcons n:value) intss:interaction))
     (interpret-interaction-ll intss (cons-state n s))]
    )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Observations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (empty?-ll s)
  #;(printf "(empty?-ll)~n")
  (for/all ([s s])
  (match s 
    [(linked-list (null _:pointer _:heap))
     #t]
    [ _
      #f])))

(define (lookup-ll-inner fuel k hd hp)
  #;(printf "(lookup-ll-inner ~a)~n" fuel)
  #;(render-value/window hp)
  (if (<= fuel 0)
      (raise-arguments-error 'lookup-ll-inner
                             "ran out of fuel")
      (match hd
        [(linked-list null)
         #f]
        [(linked-list n:natural)
         (let* ([k-c (nth-heap n hp)]
                [v-c (nth-heap (pointer->number (cell-pointer k-c)) hp)]
                [newhd (cell-pointer v-c)])
             (if (equal? k (cell-value k-c))
                 (cell-value v-c)
                 (lookup-ll-inner (- fuel 1) k newhd hp)))])))

(define (lookup-ll k s)
  #;(-> linked-list-value? linked-list-state? (or/c #f linked-list-value?))
  (for/all ([s s]) ; Because we are doing case analysis on the state here (and
                   ; further analysis in lookup-ll-inner), for/all improves
                   ; performance here
  #;(printf "(lookup-ll)~n")
  (match s
    [(linked-list (hd:pointer _:pointer hp:heap))
     (lookup-ll-inner (rec-bound) k hd hp)])))

(define (interpret-observation-ll obs s)
  #;(printf "(interpret-observation-ll ~a)~n" obs)
  #;(display-state s)
  (match obs
    [(linked-list empty?)
                  (empty?-ll s)]
    [(linked-list (lookup k:value))
                  (lookup-ll k s)]))


(define (modify-fp-state fp s)
  (linked-list (,(state-head s) ,fp ,(state-heap s))))

(define (interpret-attack-ll a s)
  (match a
    [(linked-list (change-free-pointer p:pointer))
     (modify-fp-state p s)]))

(define (ci->i ci)
      (match ci
        [(linked-list (intss:interaction o:observation))
         intss]))

(define (ci->o ci)
  (match ci
    [(linked-list (intss:interaction o:observation))
     o]))

(define (aci->ci aci)
  (match aci
    [(linked-list (a:attack ci:complete-interaction))
     ci]))

(define (aci->a aci)
  (match aci
    [(linked-list (a:attack ci:complete-interaction))
     a]))


; Check if n is added (mcons) by complete interaction
(define (complete-interaction-ll-in? ci v)
  (interaction-ll-in? (ci->i ci) v))

(define (interpret-complete-interaction-ll ci s)
  (interpret-observation-ll (ci->o ci) (interpret-interaction-ll (ci->i ci) s)))

(define (interpret-attacked-complete-interaction-ll aci s)
  (interpret-complete-interaction-ll (aci->ci aci) (interpret-attack-ll (aci->a aci) s)))


(define-language linked-list-lang
  #:grammar linked-list
  #:expression state #:size 6
  #:context complete-interaction #:size 5
  #:link cons
  #:evaluate (uncurry interpret-complete-interaction-ll))


(define-language attacked-linked-list-lang
  #:grammar linked-list
  #:expression state #:size 6
  #:context attacked-complete-interaction #:size 6
  #:link cons
  #:evaluate (uncurry interpret-attacked-complete-interaction-ll))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Utility functions for linked-list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Return the index looked up by the complete-interaction
(define (complete-interaction-ll-lookup ints)
  (match ints
    [(linked-list (intss:interaction (lookup v:value)))
     v]
    [_
     #f]))

(define (interaction-ll-in? ints v)
    (match ints
      [(linked-list ((mcons n:value) intss:interaction))
       (or (equal? n v)
            (interaction-ll-in? intss v))]
      [(linked-list (mnil intss:interaction))
       (interaction-ll-in? intss v)]))
(define (attacked-complete-interaction-ll-in? aci v)
  (interaction-ll-in? (ci->i (aci->ci aci)) v))

; #t if ints2 = (attack ints1)
(define (complete-interaction-equal?-minus-attack ci aci)
  (equal? ci (aci->ci aci)))
     
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Translation between list-api and linked-list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; inner function for list->ll, produces a heap representing the ith -> end elements of the list
(define (list->ll-inner i l)
  (match l
    [(list-api (hd:value empty))
     (linked-list ((,hd null) empty))]
    [(list-api (hd:value tl:vallist))
     (let* ([ii (+ i 1)]
            [h (list->ll-inner ii tl)]
            [c (linked-list (,hd ,ii))])
       (linked-list (,c ,h)))]))

(define (list->ll l)
  (match l
    [(list-api empty)
     (linked-list (null null empty))]
    [ _
      (let ([h (list->ll-inner 0 l)])
        (linked-list (0 null ,h)))]))

(define (list->ll-method m)
  (match m
    [(list-api mnil)
     (linked-list mnil)]
    [(list-api (mcons n:value))
     (linked-list (mcons ,n))]))

(define (list->ll-interaction ints)
  (match ints
    [(list-api empty) (linked-list empty)]
    [(list-api (m:method intss:interaction))
               (linked-list (,(list->ll-method m) ,(list->ll-interaction intss)))]))

; Comparing vallist l with the linked-list headed at fp in hp
(define (list-ll-equal?-inner l fp hp)
  (match l
    [(list-api (hd:value tl:vallist))
     (match fp 
       [(linked-list n:natural)
        (let ([hd-ll (nth-heap n hp)])
          (if (equal? hd (cell-value hd-ll))
              (list-ll-equal?-inner tl (cell-pointer hd-ll) hp)
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
(define (list-ll-equal? l s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (list-ll-equal?-inner l hd hp)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (pointer-val p)
  (match p
    [(linked-list null)
     -1]
    [(linked-list n:natural)
     n]))

(define (pp-pointer p)
  (match p
    [(linked-list null)
     "NULL"]
    [(linked-list n:natural)
     (format "->~a " n)]))
      
(define (pp-cell c)
  (match c
    [(linked-list (v:value p:pointer))
     (format " ~a, ~a " (~a v #:width 5 #:align 'center) (~a (pp-pointer p) #:width 5 #:align 'center))]))

(define (pp-heap hd fp hp adr)
  (match hp
    [(linked-list empty)
     ""]
    [(linked-list (c:cell hp+:heap))
     (let ([fp-str (if (equal? adr fp)
                       "<-FP"
                       "")]
           [hd-str (if (equal? adr hd)
                       "<-HD"
                       "")])
     (format "~a>(~a)~a~a\n~a" adr (pp-cell c) hd-str fp-str (pp-heap hd fp hp+ (+ adr 1))))]))

(define (pp-state s)
  (match s
    [(linked-list (hd:pointer fp:pointer hp:heap))
     (format "~a" (pp-heap (pointer-val hd) (pointer-val fp) hp 0))]))

(define (display-state s)
  (displayln (pp-state s)))

(define (display-language-witness-ll lw)
  (let ([lwl (unpack-language-witness lw)])
        (displayln (format "Linked-list\n~ahas behavior ~a\nunder complete-interaction ~a~n" (pp-state (first lwl)) (fourth lwl) (second lwl)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (linked-list-demo)
  (begin

    (define state (linked-list (0 null ((0 1) ((1 2) ((2 3) ((3 4) ((4 5) ((5 null) empty)))))))))
    (display-state state)
    (displayln (lookup-ll (linked-list 2) state))


    ; interaction demo
    (define interact (linked-list ((mcons 8) ((mcons 7) empty))))
    (define state+i (interpret-interaction-ll interact state))
    (display-state state+i)
    
    ; free pointer demo
    (define reset (linked-list (mnil empty)))
    (define state+r (interpret-interaction-ll reset state))
    (display-state state+r)
    (define state+ri (interpret-interaction-ll interact state+r))
    (display-state state+ri)

    ; attack demo
    (define attack (linked-list (change-free-pointer 4)))
    (define state+a (interpret-attack-ll attack state))
    (display-state state+a) 
    (define state+ai (interpret-interaction-ll interact state+a))
    (display-state state+ai)
    (displayln (lookup-ll (linked-list 8) state+ai))
    (displayln (lookup-ll (linked-list 8) state+i))
    ))
