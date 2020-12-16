#lang seec
(set-bitwidth 4)
(require racket/format)
(require racket/contract)
(provide (all-defined-out))



;
; Heap allocator model 
; Inspired by ARCHEAP
;
;

(define-grammar heap-model
  (pointer ::= natural null)
  (offset ::= integer)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer)
;  (writevalue ::= (start natural) (end natural)) ; TODO: limit the offset of writes to start or end of blocks
  (buf-loc ::= natural)
  (buf ::= list<nnvalue>)
  (heap-loc ::= pointer)
  (heap ::= list<value>) 
  (state ::= (buf heap pointer)) ; global buffer, heap and free list pointer
  (action ::=
          (set buf-loc nnvalue) ; Set element at buf-loc in buffer to nnvalue
          (read buf-loc heap-loc) ; place the element at heap-loc in heap into the buffer at buf-loc
          (write heap-loc buf-loc); place the element at buf-loc in buffer into the heap at heap-loc
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc natural)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= ; list of actions
               (action interaction)
               nop)
  #;(bug ::= ; the hope is that we do not have to use this, and instead can characterize the bugs synthesized 
       overflow
       write-after-free
       off-by-one-overflow
       off-by-one-null-overflow
       double-free
       arbitrary-free )
  #;(r-bugged-interaction ::= ; this is a list of interaction that allows a repeated occurence of a bug
                        (action r-bugged-interaction)
                        (repeat r-bugged-interaction)
                        nop)
  #;(bugged-interaction ::= ; list of action with exactly one bug (?should I make this at most one bug?)
                      (action bugged-interaction)
                      (bug r-bugged-interaction))
 )

; What do we need to keep track of:
; object status (e.g. only free valid object)
; head of the free list? 
;
; Alternative models (archeap's shadow memory)
;; - datastructure + containers + global buffer
;; - free list datastructure
;; - allocated objects (as a list, w/o free list management)

; free - generate an index into allocated-object list 
; write - write according to 

;; lifted list operations

(define (head s)
  (match s
    [(heap-model nil) (assert #f)]
    [(heap-model (cons x:any any))
     x]))

(define (tail s)
    (match s
    [(heap-model nil) (assert #f)]
    [(heap-model (cons any tl:any))
     tl]))
          
(define/contract (nth s i)
  (-> any/c natural-number/c any/c)
  ;(displayln (format "Nth with i: ~a" i))
  (match i
    [(heap-model 0)
     (head s)]
    [(heap-model i:natural)
     (nth (tail s) (- i 1))]))
      

; replace the ith element in l with v
; list* -> integer* -> value* -> list*
(define (replace l i v)
  (match i
    [(heap-model 0)
     (heap-model (cons ,v ,(tail l)))]
    [(heap-model i:natural)
      (heap-model (cons ,(head l) ,(replace (tail l) (- i 1) v)))]))

; create a list repeating v i times
(define (repeat v i)
  (if (equal? i 0)
      (heap-model nil)
      (heap-model (cons ,v ,(repeat v (- i 1))))))

;; Heap, Buff and State operations


; write value at the ith position of cell
; TODO: confirm this is same as replace on list?
(define/contract (write hp i v)
  (-> any/c natural-number/c any/c any/c)
  (if (equal? i 0)
      (heap-model (,v ,(tail hp)))
      (heap-model (,(head hp) ,(write (tail hp) (- i 1) v)))))

; init a state with buf size b-i and heap size (in cells) h-i
; integer -> integer -> state*
(define (init-state b-i h-i)
  (heap-model (,(repeat (heap-model 0) b-i) ,(repeat (heap-model null) (* h-i 4)) null)))


; pointer* -> boolean
(define (is-null? p)
  (match p
    [(heap-model null)
     #t]
    [(heap-model n:integer)
                 #f]))

(define (pointer-addr p)
  (match p
    [(heap-model n:natural)
     n]))
#;(define/contract (pointer-addr p )
  (-> any/c natural-number/c)
  (match p
    [(heap-model n:natural)
     (+ (* n 4) 2)]))

; Function to calculate the address of a heap-loc in the heap
(define (heap-loc-addr hl)
  (match hl
    [(heap-model n:natural)
     n]))

#;(define/contract (heap-loc-addr hl)
  (-> any/c natural-number/c)
  (match hl
       [(heap-model (p:natural o:natural))
        (+ (+ (* p 4) 2) o)]))

; Allocate the first free block of memory in h,
; starting with i = 0...
; first look at i if allocated
; if not, alloc a new block at i,
; o.w., see size in i, and continue with i' = i + size + 1
; return the pointer to new block X new heap
(define (interpret-alloc-no-free h)
  (define (interpret-alloc-no-free+ h i)
    ;(displayln (format "In alloc-no-free at ~a" i))
    (let ([val (nth h i)])
          (if (is-null? val)
              ; allocate block at i
              (let* ([h+ (replace h i (heap-model 2))]
                     [h++ (replace h+ (+ i 1) (heap-model 0))]
                     [h+++ (replace h++ (+ i 2) (heap-model 0))]
                     [h+4 (replace h+++ (+ i 3) (heap-model 1))])
                ;(displayln (format "allocated at ~a a block of size ~a" i 2))
                (cons (heap-model ,(+ i 1)) h+4))
              (interpret-alloc-no-free+ h (+ i val 2)))))
  (interpret-alloc-no-free+ h 0))

; reallocate the block at the head of the free-list
; heap* -> natural -> (pointer* x heap*)
; returns new free pointer X new heap
(define (interpret-alloc-free h n)
  (let* ([newf (nth h n)] ; get the tail of the free-list
         [size (nth h (- n 1))]) ; get the size of this block
       (match size
         [(heap-model sz:natural)
          (let* ([h+ (replace h (+ n sz) (heap-model 1))])            
            (match newf
              [(heap-model nf:natural)
               (let* ([h++ (replace h+ (+ nf 1) (heap-model null))])
                 (cons newf h++))]
               [(heap-model null)
                (cons newf h+)]))])))


; free block at p in h, adding it to the free-list headed at f
;; (1) find the size of block (at p-1)
;; (2) add p to the fp list
;; (3) set prev-in-use (at p+sz) to 0

(define (interpret-free h f p)
  (match p
    [(heap-model n:natural)
     ;(displayln (format "In free, pointer ~a" n))
     (let* ([size (nth h (- n 1))])
       (match size
         [(heap-model sz:natural)
          ;(displayln (format "size ~a" sz))
          (let* ([h+ (replace h (+ n sz) (heap-model 0))]
                 [h++ (replace h+ n f)]
                 [h+++ (replace h++ (+ n 1) (heap-model null))])
            (match f ; update the whole fp head to point to new head
              [(heap-model null)
               (cons p h+++)]
              [(heap-model nf:natural)
               (let* ([h+4 (replace h+++ (+ nf 1) p)])
                 (cons p h+4))]))]
         [_
          ;(displayln "trying to free a block which wasn't allocated")
          (cons f h)]))]))


; apply a single action on a state
(define (interpret-action a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     ;(displayln "matched heap")
     (match a
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)]
               [fh+ (interpret-free h f p)])
          (heap-model (,b ,(cdr fh+) ,(car fh+))))]
       [(heap-model (alloc bl:buf-loc n:natural))
        (match f
          [(heap-model n:natural)
           (let* ([ph+ (interpret-alloc-free h n)]
                  [b+ (replace b bl f)])
             (heap-model (,b+ ,(cdr ph+) ,(car ph+))))]
          [(heap-model null)
           (let* ([ph+ (interpret-alloc-no-free h)]
                  [b+ (replace b bl (car ph+))])
             (heap-model (,b+ ,(cdr ph+) ,f)))])]
       [(heap-model (set bl:buf-loc val:nnvalue))
        (let* ([b+ (replace b bl val)])
          (heap-model (,b+ ,h ,f)))]
       [(heap-model (read bl:buf-loc hl:heap-loc))
        ;(displayln "action read")
                    (let* ([loc (heap-loc-addr hl)]
                           [val (nth h loc)]
                           [b+ (if (is-null? val)
                                   (replace b bl (heap-model -1))
                                   (replace b bl val))])
                      (heap-model (,b+ ,h ,f)))]
       [(heap-model (write hl:heap-loc bl:buf-loc))
        ;(displayln "action write")
        (let* ([val (nth b bl)]
               [loc (heap-loc-addr hl)]
               [h+ (write h loc val)])
          (heap-model (,b ,h+ ,f)))])]))

; apply a sequence of action on a state
; interaction -> state -> state
(define (interpret-interaction i s)
  (match i
    [(heap-model (a:action i+:interaction))
     (interpret-interaction i+ (interpret-action a s))]
    [(heap-model nop)
     s]))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (print-nnvalue nv)
  (match nv
    [(heap-model i:integer)
     (format "~a" i)]))

(define (print-pointer p)
  (match p
    [(heap-model n:natural)
     (format "~a" n)]
    [(heap-model null)
     "null"]))
                 

(define (print-value v)
  (match v
    [(heap-model p:pointer)
     (print-pointer p)]
    [(heap-model nv:nnvalue)
     (print-nnvalue nv)]))

(define (display-buf b)
  (define (display-buf+ b addr)
    (match b
      [(heap-model nil)
       (displayln "")]
      [(heap-model (cons h:nnvalue b+:buf))
       (displayln (format "~a > ~a" addr (print-nnvalue h)))
       (display-buf+ b+ (+ addr 1))]))
  (display-buf+ b 0))


(define (display-heap h)
  (define (display-heap+ h addr)
    (match h
      [(heap-model nil)
       (displayln "")]
      [(heap-model (cons h1:value (cons h2:value (cons h3:value (cons h4:value h+:heap)))))
       (displayln (format "~a > | ~a | ~a | ~a | ~a |" addr (print-value h1) (print-value h2) (print-value h3) (print-value h4)))
       (display-heap+ h+ (+ addr 4))]))
  (display-heap+ h 0))

(define (display-state s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     (begin
       (displayln "BUFFER:")
       (display-buf b)
       (displayln "HEAP:")
       (display-heap h)
       (displayln "FP HEAD:")
       (displayln (print-pointer f)))]))


(define d (init-state 4 2))
(define aw (heap-model (write 2 0)))
(define ar (heap-model (read 0 2)))
(define aa (heap-model (alloc 0 1)))
(define aa2 (heap-model (alloc 1 1)))
(define aa3 (heap-model (alloc 2 1)))


(define af (heap-model (free 0)))
(define af2 (heap-model (free 1)))


(define d++ (interpret-action aa2 (interpret-action aa d)))
(define d+4 (interpret-action af2 (interpret-action af d++)))
(define d+5 (interpret-action aa3 d+4))
