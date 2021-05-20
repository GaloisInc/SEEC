#lang seec
(require seec/private/util)
(require seec/private/monad)
(require racket/format)
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
(require (file "lib.rkt"))
(require (file "heap-lang-hl.rkt"))
(provide (all-defined-out))

; heap-loc version
; Making a higher-abstraction model which described the content of a heap
; and which can be compiled (non-deterministically) into a multiple equivalent heaps
; TODO: Need to update the pointers when freeing a block

(define-grammar abstract-model
  (pointer ::= (P natural selector) N)
  (selector ::= a b)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer )
  (block ::= (value value))
  (buf-loc ::= natural)
  (buf ::= list<value>)
  (heap ::= list<block>)
  (state ::= (buf heap))
  (heap-loc ::= pointer)
  (action ::=
    (read heap-loc buf-loc) ; place the element at pointer (1)buf-loc in heap into the buffer at (2)buf-loc
    (write buf-loc heap-loc); place the element at (1)buf-loc in buffer into the heap pointer (2)buf-loc
    (copy buf-loc buf-loc) ; overwrite (2) with value of (1)
    (incr buf-loc) ; add 1 to value at buf-loc
    (decr buf-loc) ; remove 1 to value at buf-loc
    (free heap-loc) ; free the object at the pointer held in buf-loc in buffer
    (alloc buf-loc)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (s-action ::=
            (set buf-loc value))
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

(define (abs-state->buf s)
  (match s
    [(abstract-model (b:buf any))
                     b]))

(define (abs-state->heap s)
    (match s
    [(abstract-model (any h:heap))
     h]))

; decrease all pointers bigger (or equal to n)
(define (abs-shift-pointer n p)
  (match p
    [(abstract-model (P m:natural s:selector))
     (if (<= n m)
         (abstract-model (P ,(- m 1) ,s))
         p)]
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

; free the block at hl
(define (abs-free b h hl)
    (match hl
      [(abstract-model (P n:natural m:selector))
       (let* ([h+ (drop-nth n h)]
              [b++ (abs-shift-buf n b)]
              [h++ (abs-shift-heap n h+)])
        (abs-state b++ h++))]
      [any
       (assert #f)]))

(define/debug #:suffix (abs-alloc b h bl)
  (begin
    (let* ([b+ (replace b bl (abstract-model (P ,(s-length h) a)))]
           [h+ (append h (abstract-model (cons (0 0) nil)))])
      (abs-state b+ h+))))
  
(define (abs-read-heap h loc)
  (match loc
    [(abstract-model (P n:natural m:selector))
     (let* ([payload (nth h n)])
       (block-nth payload m))]))

(define (abs-write-heap h loc val)
  (match loc
    [(abstract-model (P n:natural m:selector))
     (let* ([payload (nth h n)]
            [payload+ (block-replace payload m val)])
       (replace h n payload+))]))

(define (abs-incr val)
  (match val
    [(abstract-model i:integer)
     (abstract-model ,(+ i 1))]
    [(abstract-model (P n:natural a))
     (abstract-model (P ,n b))]))

(define (abs-decr val)
  (match val
    [(abstract-model i:integer)
     (abstract-model ,(- i 1))]
    [(abstract-model (P n:natural b))
     (abstract-model (P ,n a))]))


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
          (abs-state b+ h))]
       [(abstract-model (decr bl:buf-loc))
        (let* ([val (nth b bl)]
               [val+ (abs-decr val)]
               [b+ (replace b bl val+)])
          (abs-state b+ h))]
       [(abstract-model (free hl:heap-loc))
        (abs-free b h hl)]
       [(abstract-model (alloc bl:buf-loc))
        (abs-alloc b h bl)]
       [(abstract-model (read hl:heap-loc bl:buf-loc))
        (let* ([val (abs-read-heap h hl)] ; get the value at the location
               [b+ (replace b bl val)]) ; place the value in the buffer
             (abs-state b+ h))]
       [(abstract-model (write bl:buf-loc hl:heap-loc))
        (let* ([val (nth b bl)]
               [h+ (abs-write-heap h hl val)])
          (abs-state b h+))]))))

(define/debug #:suffix (abs-interpret-saction a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
     (match a
       [(abstract-model (set bl:buf-loc v:value))
        (let* ([b+ (replace b bl v)])
          (abs-state b+ h))]))))


(define (abs-interpret-interaction i s)
    (match i
    [(abstract-model (cons a:action i+:interaction))
     (abs-interpret-interaction i+ (abs-interpret-action a s))]
    [(abstract-model nil)
     s]))


(define-language abstract-lang
  #:grammar abstract-model
  #:expression interaction #:size 4
  #:context state #:size 10
  #:link (lambda (s i) (cons i s))
  #:evaluate (uncurry abs-interpret-interaction))


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
    [(abstract-model (b:any h:any))
     (begin
       (displayln "BUFFER:")
       (display-abs-buf b)
       (displayln "HEAP:")
       (display-abs-heap h))]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING abstract-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define ad (abs-init-state 4))


(define abuf (abstract-model (cons (P 0 a) (cons (P 1 b) (cons 4 (cons 5 nil))))))
(define aheap (abstract-model (cons (6 (P 1 a)) (cons ((P 0 a) 7) nil))))
(define astate (abstract-model (,abuf ,aheap)))


(define asmallbuf (abstract-model (cons (P 0 a) (cons -1 (cons 0 (cons 1 nil))))))
(define asmallheap (abstract-model (cons ((P 0 b) 2) nil)))
(define asmallstate (abstract-model (,asmallbuf ,asmallheap)))

(define ademobuf (abstract-model (cons N (cons (P 0 a) (cons 0 (cons 0 nil))))))
(define ademoheap (abstract-model (cons (0 0) nil)))
(define ademostate (abstract-model (,ademobuf ,ademoheap)))

;(debug? #t)

(define ad+  (abs-interpret-action aa0 ad))


(define ad++ (abs-interpret-action aa1 ad+))

(define abss0 (abstract-model (set 0 N)))
(define absf0 (abstract-model (free (P 0 a))))
(define abss1 (abstract-model (set 1 N)))
(define absf1 (abstract-model (free (P 1 a))))

(define ad+3* (abs-interpret-action absf0 (abs-interpret-saction abss0 ad++)))
(define ad+3** (abs-interpret-action absf1 (abs-interpret-saction abss1 ad++)))

(define ad+4* (abs-interpret-action absf0 (abs-interpret-saction abss1 ad+3*)))
 



(define ad+5* (abs-interpret-action aa0 ad+4*))

(define ad+4** (abs-interpret-action absf0 (abs-interpret-saction abss0 ad+3**)))




