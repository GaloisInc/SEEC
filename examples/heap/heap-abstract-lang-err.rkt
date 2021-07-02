#lang seec
(require seec/private/util)
(require seec/private/monad)
(require racket/format)
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
(require (file "lib.rkt"))
(require (file "heap-lang.rkt"))
(provide (all-defined-out))


; Making a higher-abstraction model which described the content of a heap
; and which can be compiled (non-deterministically) into a multiple equivalent heaps

(define-grammar abstract-model
  (pointer ::= (P natural selector) N)
  (selector ::= a b)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer )
  (block ::= (value value))
  (buf-loc ::= natural)
  (buf ::= list<value>)
  (heap ::= list<block>)
  (state ::= (buf heap) E) ; added error state E
  (action ::=
    (read buf-loc buf-loc) ; place the element at pointer (1)buf-loc in heap into the buffer at (2)buf-loc
    (write buf-loc buf-loc); place the element at (1)buf-loc in buffer into the heap pointer (2)buf-loc
    (copy buf-loc buf-loc) ; overwrite (2) with value of (1)
    (incr buf-loc) ; add 1 to value at buf-loc
    (decr buf-loc) ; remove 1 to value at buf-loc
    (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
    (alloc buf-loc)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= list<action>)
  )

(define (abs-select s a1 a2)
  (match s
    [(abstract-model a)
     a1]
    [(abstract-model b)
     a2]))
    
(define (block-nth p n)
  (match p
    [(abstract-model (a-cell:any b-cell:any))
     (abs-select n a-cell b-cell)]))
    
(define (block-replace p n val)
  (match p
    [(abstract-model (a-cell:any b-cell:any))
     (match n
       [(abstract-model a)
        (abstract-model (,val ,b-cell))]
       [(abstract-model b)
        (abstract-model (,a-cell ,val))])]))

; n is the size of the buffer
(define (abs-init-state n)
  (let* ([b (repeat (abstract-model 0) n)]
         [h (abstract-model nil)])
    (abstract-model (,b ,h))))

(define (abs-state b h)
  (abstract-model (,b ,h)))

(define (abs-error-state)
  (abstract-model E))

(define (abs-is-null? p)
  (equal? p (abstract-model N)))

(define (abs-state->buf s)
  (match s
    [(abstract-model (b:buf any))
                     b]))

(define (abs-state->heap s)
    (match s
    [(abstract-model (any h:heap))
     h]))

; decrease all pointers bigger
(define (abs-shift-pointer n p)
  (match p
    [(abstract-model (P m:natural s:selector))
     (if (< n m)
         (abstract-model (P ,(- m 1) ,s))
         (if (equal? n m)
             (abstract-model N)
             p))]
    [(abstract-model N)
     p]))



(define (abs-shift-value n v)
  (match v
    [(abstract-model p:pointer)
     (abs-shift-pointer n p)]
    [any
     v]))
     
(define (abs-shift-block n b)
  (match b
    [(abstract-model (v1:value v2:value))
     (abstract-model (,(abs-shift-value n v1) ,(abs-shift-value n v2)))]))

(define (abs-shift-buf n buf)
  (map (lambda (v) (abs-shift-value n v)) buf))

(define (abs-shift-heap n heap)
  (map (lambda (b) (abs-shift-block n b)) heap))

(define (abs-shift-state n s)
  (match s
    [(abstract-model (b:buf h:heap))
     (abstract-model (,(abs-shift-buf n b) ,(abs-shift-heap n h)))]))


; This version of abs-free doesn't force the selector to be "a"
(define (abs-free b h bl)
  (let* ([p (nth b bl)]) ; get the pointer
    (match p
      [(abstract-model (P n:natural m:selector))
       (let* ([b+ (replace b bl (abstract-model N))]
              [h+ (drop-nth n h)]
              [b++ (abs-shift-buf n b+)]
              [h++ (abs-shift-heap n h+)])
        (abs-state b++ h++))]
      [any
       (abs-error-state)])))


(define/debug #:suffix (abs-alloc b h bl)
  (begin
    (let* ([b+ (replace b bl (abstract-model (P ,(s-length h) a)))]
           [h+ (append h (abstract-model (cons (0 0) nil)))])
      (abs-state b+ h+))))
  
(define (abs-read-heap h loc)
  (match loc
    [(abstract-model (P n:natural m:selector))
     (let* ([payload (nth h n)])
       (block-nth payload m))]
    [(abstract-model any)
     #f]))

(define (abs-write-heap h loc val)
  (match loc
    [(abstract-model (P n:natural m:selector))
     (let* ([payload (nth h n)]
            [payload+ (block-replace payload m val)])
       (replace h n payload+))]
    [(abstract-model any)
     #f]))


(define (abs-incr val)
  (match val
    [(abstract-model i:integer)
     (abstract-model ,(+ i 1))]
    [(abstract-model (P n:natural s:selector))
     (abs-select s                 
                 (abstract-model (P ,n b))
                 (abstract-model N))]))

(define (abs-decr val)
  (match val
    [(abstract-model i:integer)
     (abstract-model ,(- i 1))]
    [(abstract-model (P n:natural s:selector))
     (abs-select s
                 (abstract-model N)
                 (abstract-model (P ,n a)))]))


(define/debug #:suffix (abs-interpret-action a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
     (match a
       [(abstract-model (copy bl0:buf-loc bl1:buf-loc))
        (let* ([val (nth b bl0)]
               [b+ (replace b bl1 val)])
          (abs-state b+ h))]
       [(abstract-model (incr bl:buf-loc))
        (let* ([val (nth b bl)]
               [val+ (abs-incr val)]
               [b+ (replace b bl val+)])
          (if (abs-is-null? val+)
              (abs-error-state)
              (abs-state b+ h)))]
       [(abstract-model (decr bl:buf-loc))
        (let* ([val (nth b bl)]
               [val+ (abs-decr val)]
               [b+ (replace b bl val+)])
          (if (abs-is-null? val+)
              (abs-error-state)
              (abs-state b+ h)))]
       [(abstract-model (free bl:buf-loc))
        (abs-free b h bl)]
       [(abstract-model (alloc bl:buf-loc))
        (abs-alloc b h bl)]
       [(abstract-model (read bhl:buf-loc bl:buf-loc))
        (let* ([loc (nth b bhl)] ; get the pointer
               [val (abs-read-heap h loc)]) ; get the value at the location
          (if val
              (abs-state (replace b bl val) h)
              (abs-error-state)))]
       [(abstract-model (write bl:buf-loc bhl:buf-loc))
        (let* ([val (nth b bl)]
               [loc (nth b bhl)]
               [h+ (abs-write-heap h loc val)])
          (if h+
              (abs-state b h+)
              (abs-error-state)))]))))


(define (abs-interpret-interaction i s)
    (match i
    [(abstract-model (cons a:action i+:interaction))
     (abs-interpret-interaction i+ (abs-interpret-action a s))]
    [(abstract-model nil)
     s]))


(define-language abstract-lang
  #:grammar abstract-model
  #:expression state #:size 10
  #:context action #:size 3
  #:link cons
  #:evaluate (uncurry abs-interpret-action))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; PREDICATES over abstract-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; abs-dangling? -> true if there are any dangling (-1) pointers in the state
(define (abs-val-dangling? v)
  (match v
    [(abstract-model (P -1 any))
     #t]
    [(abstract-model any)
     #f]))

(define (abs-buf-dangling? b)
  (match b
    [(abstract-model nil)
     #f]
    [(abstract-model (cons v:any b+:any))
     (or (abs-val-dangling? v)
         (abs-buf-dangling? b+))]))

(define (abs-block-dangling? b)
  (match b
    [(abstract-model (v1:any v2:any))
     (or (abs-val-dangling? v1)
         (abs-val-dangling? v2))]))

(define (abs-heap-dangling? h)
  (match h
    [(abstract-model nil)
     #f]
    [(abstract-model (cons p:block h+:heap))
     (or (abs-block-dangling? p)
         (abs-heap-dangling? h+))]))

(define (abs-state-dangling? s)
  (match s
    [(abstract-model (b:any h:any))
     (or (abs-buf-dangling? b)
         (abs-heap-dangling? h))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (print-abs-nnvalue nv)
  (match nv
    [(abstract-model i:integer)
     (format "~a" i)]))

(define (print-abs-selector s)
  (match s
    [(abstract-model a)
     "a"]
    [(abstract-model b)
     "b"]))

(define (print-abs-pointer p)
  (match p
    [(abstract-model (P n:integer s:selector))
     (format "P ~a ~a" n (print-abs-selector s))]
    [(abstract-model N)
     "null"]
    [(abstract-model any)
      "?pointer?"]))
                 
(define (print-abs-value v)
  (match v
    [(abstract-model (P n:any s:selector))
     (print-abs-pointer v)]
    [(abstract-model N)
     (print-abs-pointer v)]
    [(abstract-model nv:nnvalue)
     (print-abs-nnvalue nv)]))

(define (print-abs-block p)
  (match p
    [(abstract-model (a:any b:any))
     (format "(~a, ~a)" (print-abs-value a) (print-abs-value b))]))

(define (display-abs-buf b)
  (define (display-abs-buf+ b addr)
    (match b
      [(abstract-model nil)
       (displayln "")]
      [(abstract-model (cons h:any b+:any))
       (displayln (format "~a > ~a"
                          (~a addr #:width 2)
                          (print-abs-value h)))
       (display-abs-buf+ b+ (+ addr 1))]))
  (display-abs-buf+ b 0))

(define (display-abs-heap h)
  (define (display-abs-heap+ h addr)
    (match h
      [(abstract-model nil)
       (displayln "")]
      [(abstract-model (cons p:block h+:heap))
       (displayln (format "~a > ~a "
                          (~a addr #:width 2)
                          (~a (print-abs-block p))))
       (display-abs-heap+ h+ (+ addr 1))]))
  (display-abs-heap+ h 0))

(define (display-abs-state s)
  (match s
    [(abstract-model E)
     (displayln "ERROR ABSTRACT STATE")]
    [(abstract-model (b:any h:any))
     (begin
       (displayln "BUFFER:")
       (display-abs-buf b)
       (displayln "HEAP:")
       (display-abs-heap h))]))


(define (display-abs-witness witness)
  (if witness
      (let* ([lwl-abstract (unpack-language-witness witness)])
        (displayln "State: ")
        (display-abs-state (first lwl-abstract))
        (displayln "steps, under interaction...")
        (display (second lwl-abstract))
        (displayln ", to state: ")
        (display-abs-state (fourth lwl-abstract)))
      (displayln "No witness found")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING abstract-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define ad (abs-init-state 4))

;(debug? #t)
(define ad+  (abs-interpret-action aa0 ad))


(define ad++ (abs-interpret-action aa1 ad+))


(define ad+3* (abs-interpret-action af0 ad++))
(define ad+3** (abs-interpret-action af1 ad++))
(define ad+4* (abs-interpret-action af1 ad+3*))
(define ad+5* (abs-interpret-action aa0 ad+4*))
(define ad+4** (abs-interpret-action af0 ad+3**))



(define abuf (abstract-model (cons (P 0 a) (cons (P 1 b) (cons 4 (cons 5 nil))))))
(define aheap (abstract-model (cons (6 (P 1 a)) (cons ((P 0 a) 7) nil))))
(define astate (abstract-model (,abuf ,aheap)))


(define asmallbuf (abstract-model (cons (P 0 a) (cons -1 (cons 0 (cons 1 nil))))))
(define asmallheap (abstract-model (cons ((P 0 b) 2) nil)))
(define asmallstate (abstract-model (,asmallbuf ,asmallheap)))

(define ademobuf (abstract-model (cons N (cons (P 0 a) (cons 0 (cons 0 nil))))))
(define ademoheap (abstract-model (cons (0 0) nil)))
(define ademostate (abstract-model (,ademobuf ,ademoheap)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; QUERY over the abstract-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; initial state is ademostate
(define (demo-behavior0 p b)
  (match p
    [(cons a s)
     (equal? s ademostate)]))

; returns a symbolic abstract state and a list of variables
(define (make-symbolic-abstract-state)
  (let*
      ([ab0 (abstract-model value 2)]
       [ab1 (abstract-model value 2)]
       [ab2 (abstract-model value 2)]
       [ab3 (abstract-model value 2)]
       [ab* (abstract-model (cons ,ab0 (cons ,ab1 (cons ,ab2 (cons ,ab3 nil)))))]
       [ah* (abstract-model heap 4)]
       [as* (abstract-model (,ab* ,ah*))])
    (cons as* (list ab0 ab1 ab2 ab3 ah*))))

(define (make-small-abstract-state)
  (let*
      ([ab0 (abstract-model value 2)]
       [ab1 (abstract-model value 2)]
       [ab2 (abstract-model value 2)]
       [ab3 (abstract-model value 2)]
       [ab* (abstract-model (cons ,ab0 (cons ,ab1 (cons ,ab2 (cons ,ab3 nil)))))]
       [ablock (abstract-model block 3)]
       [ah* (abstract-model (cons ,ablock nil))]
       [as* (abstract-model (,ab* ,ah*))])
    (cons as* (list ab0 ab1 ab2 ab3 ah*))))


(define (with-abstract-schema q)
    (let* ([assert-store (asserts)]
           [as* (make-small-abstract-state)])
      (let* ([w (q (car as*))])
        (clear-asserts!)
        (for-each (lambda (arg) (assert arg)) assert-store)
        w)))

; resulting state is demostate
(define (demo-behavior1 p b)
  (let
      ([ademostate+ (abs-interpret-action (abstract-model (alloc 0)) ademostate)])
    (equal? b ademostate)))

(define (demo-behavior1t p b)
  #t)

; -- much slower vs. sketched version (am-q0s)
(define (am-q0) 
  (display-abs-witness (first (find-gadget abstract-lang demo-behavior0))))

(define (am-q0s)
  (let* ([sv (make-symbolic-abstract-state)])
    (display-abs-witness (first (find-gadget abstract-lang demo-behavior0 #:expression (car sv))))))


; -- not working yet?
; -- should be able to find ademostate after (free 1), and then alloc 1
(define (am-q1) 
  (display-abs-witness (first (find-gadget abstract-lang demo-behavior1))))


(define (am-q1s)
  (let* ([sv (make-symbolic-abstract-state)])
    (display-abs-witness (first (find-gadget abstract-lang demo-behavior1 #:expression (car sv))))))
