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
  ;  (writevalue ::= (start natural) (end natural)) ; NOTE: could limit the offset of writes to start or end of blocks
  (buf-loc ::= natural)
  (buf ::= list<value>)
  (heap-loc ::= pointer)
  (heap ::= list<value>) 
  (state ::= (buf heap pointer)) ; global buffer, heap and free list pointer
  (action ::=
          (set buf-loc nnvalue) ; Set element at buf-loc in buffer to nnvalue
          (read buf-loc buf-loc) ; place the element at pointer (1)buf-loc in heap into the buffer at (2)buf-loc
          (write buf-loc buf-loc); place the element at (1)buf-loc in buffer into the heap pointer (2)buf-loc
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc natural)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= ; list of actions
               (action interaction)
               nop)
  (action-hl ::= ; like action but with heap-loc
             (set buf-loc nnvalue)
             (read heap-loc buf-loc)
             (write buf-loc heap-loc)
             (free heap-loc)
             (alloc buf-loc natural))
  (interaction-hl ::= ; like interaction but with heap-loc
                  (action-hl interaction-hl)
                  nop)
  (observation ::=
               (get buf-loc))
  (total-interaction ::= ; perform interaction, then get nth value from buffer
                     (interaction observation))
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

(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

;; lifted list operations
(define (length s)
  (match s
    [(heap-model nil) 0]
    [(heap-model (cons any h:any))
     (+ 1 (length h))]))

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

(define (append s1 s2)
  (match s1
    [(heap-model nil) s2]
    [(heap-model (cons hd:any tl:any))
     (heap-model (cons ,hd ,(append tl s2)))]))

; TODO: make interaction a list...
(define (append-interaction i1 i2)
  (match i1
    [(heap-model nop) i2]
    [(heap-model (hd:any tl:any))
                 (heap-model (,hd ,(append-interaction tl i2)))]))

(define/contract (nth s i)
  (-> any/c natural-number/c any/c)
  (if (= i 0)
     (head s)
     (nth (tail s) (- i 1))))

; add v at the end of list s
(define (snoc s v)
    (match s
      [(heap-model nil)
       (heap-model (cons ,v nil))]
      [(heap-model (cons hd:any s+:any))
       (heap-model (cons ,hd ,(snoc s+ v)))]))


; replace the ith element in l with v
; list* -> integer* -> value* -> list*
(define (replace l i v)
  (match i
    [(heap-model 0)
     (heap-model (cons ,v ,(tail l)))]
    [(heap-model i:natural)
     (heap-model (cons ,(head l) ,(replace (tail l) (- i 1) v)))]))

; remove the first occurence of v from the list
(define (remove-one-elem l v)
  (match l
    [(heap-model nil)
     l]
    [(heap-model (cons hd:any l+:any))
     (if (equal? hd v)
         l+
         (heap-model (cons ,hd ,(remove-one-elem l+ v))))]))


; create a list repeating v i times
(define (repeat v i)
  (if (equal? i 0)
      (heap-model nil)
      (heap-model (cons ,v ,(repeat v (- i 1))))))

; returns a string concatenating
; f applied to each of the elements
; of vs
(define (print-list f vs)
  (match vs
    [(heap-model nil)
     ""]
    [(heap-model (cons v:any vs+:list<any>))
     (format "~a, ~a" (f v) (print-list f vs+))]))



;; Heap, Buff and State operations
; write value at the ith position of cell
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

; calculate the address of a heap-loc in the heap
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
;;; Returns the updated heap

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
               h+++]
              [(heap-model nf:natural)
               (let* ([h+4 (replace h+++ (+ nf 1) p)])
                 h+4)]))]
         [_
          ;(displayln "trying to free a block which wasn't allocated")
          ;(cons f h)
          (assert false)
          ]))]))


; apply a single action on a state
; heap-model.action -> heap-model.state -> heap-model.state
(define (interpret-action a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     ;(displayln "matched heap")
     (match a
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)]
               [b+ (replace b bl (heap-model null))]
               [h+ (interpret-free h f p)])
          (heap-model (,b+ ,h+ ,p)))]
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
       [(heap-model (read bhl:buf-loc bl:buf-loc))
        ;(displayln "action read")
        (let* ([hl (nth b bhl)] ; get the pointer
               [loc (heap-loc-addr hl)] ; compute the address
               [val (nth h loc)] ; get the value at the location
               [b+ (replace b bl val)]) ; place the value in the buffer
               (heap-model (,b+ ,h ,f)))]
       [(heap-model (write bl:buf-loc bhl:buf-loc))
        ;(displayln "action write")
        (let* ([val (nth b bl)] ; get the value from the buffer
               [hl (nth b bhl)] ; get the pointer from the buffer
               [loc (heap-loc-addr hl)] ; compute the address in the heap
               [h+ (write h loc val)]) ; overwrite the location in the heap with the value
          (heap-model (,b ,h+ ,f)))])]))

; apply a sequence of action on a state
; interaction -> state -> state
(define (interpret-interaction i s)
  (match i
    [(heap-model (a:action i+:interaction))
     (interpret-interaction i+ (interpret-action a s))]
    [(heap-model nop)
     s]))

(define (interpret-observation o s)
  (match o 
    [(heap-model (get n:natural))
     (match s
       [(heap-model (b:buf any any))
        (nth b n)])]))

(define (interpret-total-interaction ig s)
  (match ig
    [(heap-model (i:interaction o:observation))
     (let ([s+ (interpret-interaction i s)])
       (interpret-observation o s+))]))



(define-language heap-lang
  #:grammar heap-model
  #:expression interaction #:size 4
  #:context state #:size 8
  #:link cons
  #:evaluate (uncurry interpret-interaction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Alternative interaction language (where heap-loc provided directly)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (interpret-action-hl a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     ;(displayln "matched heap")
     (match a
       [(heap-model (free p:heap-loc))
          (heap-model (,b ,(interpret-free h f p) ,p))]
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
       [(heap-model (read hl:heap-loc bl:buf-loc))
        (let* ([loc (heap-loc-addr hl)] ; compute the address
               [val (nth h loc)] ; get the value at the location
               [b+ (replace b bl val)]) ; place the value in the buffer
               (heap-model (,b+ ,h ,f)))]
       [(heap-model (write bl:buf-loc hl:heap-loc))
        (let* ([val (nth b bl)] ; get the value from the buffer
               [loc (heap-loc-addr hl)] ; compute the address in the heap
               [h+ (write h loc val)]) ; overwrite the location in the heap with the value
          (heap-model (,b ,h+ ,f)))])]))


(define (interpret-interaction-hl i s)
    (match i
    [(heap-model (a:action-hl i+:interaction-hl))
     (interpret-interaction-hl i+ (interpret-action-hl a s))]
    [(heap-model nop)
     s]))

; translate an action into a list of action-hl
; heap-model.action -> heap-model.interaction-hl
(define (translate-action-hl a s)
    (match s
    [(heap-model (b:buf h:heap f:pointer))
     ;(displayln "matched heap")
     (match a
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)])
          (heap-model ((free ,p) ((set ,bl null) nop))))]
        [(heap-model (read bhl:buf-loc bl:buf-loc))
        ;(displayln "action read")
         (let* ([hl (nth b bhl)]) ; get the pointer
                (heap-model ((read ,hl ,bl) nop)))]
       [(heap-model (write bl:buf-loc bhl:buf-loc))
        ;(displayln "action write")
        (let* ([hl (nth b bhl)])
          (heap-model ((write ,bl ,hl) nop)))]
       [(heap-model any) ; set, alloc
        (heap-model (,a nop))]
       )]))

; translate an interaction into an interaction-hl
; heap-model.interaction -> heap-model.state -> heap-model.interaction-hl
(define (translate-interaction-hl i s)
  (match i
    [(heap-model nop)
     (heap-model nop)]
    [(heap-model (a:action i+:interaction))
     (let* ([i-hl (translate-action-hl a s)]
            [s+ (interpret-action a s)]
            [i-hl+ (translate-interaction-hl i+ s+)])
       (heap-model ,(append-interaction i-hl i-hl+)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Validity predicate for heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; heap -> pointer -> boolean
; true if the pointer is wellscoped in heap
(define (scoped-pointer? h p)
  (match p
    [(heap-model null)
     #t]
    [(heap-model l:natural)
     ; checks if l is smaller than the length of h
     (not (< (seec-length h) l))]))



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
      [(heap-model (cons h:value b+:buf))
       (displayln (format "~a > ~a"
                          (~a addr #:width 2)
                          (print-value h)))
       (display-buf+ b+ (+ addr 1))]))
  (display-buf+ b 0))


(define (display-heap h)
  (define (display-heap+ h addr)
    (match h
      [(heap-model nil)
       (displayln "")]
      [(heap-model (cons h1:value (cons h2:value (cons h3:value (cons h4:value h+:heap)))))
       (displayln (format "~a > | ~a | ~a | ~a | ~a |"
                          (~a addr #:width 2)
                          (~a (print-value h1) #:width 4)
                          (~a (print-value h2) #:width 4)
                          (~a (print-value h3) #:width 4)
                          (~a (print-value h4) #:width 4)))
       (display-heap+ h+ (+ addr 4))]
      [(heap-model any)
       (displayln "HEAP not a multiple of 4")
       (displayln (print-list print-value h))
       ]))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Predicate to validate heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; all the buf and heap-loc in the action/interaction are scoped (to the size of buf)
(define (heap-model-valid-action b-size a)
  (match a
    [(heap-model (set b:buf-loc any))
     (<= b b-size)]
    [(heap-model (read b1:buf-loc b2:buf-loc))
     (and (<= b1 b-size)
          (<= b2 b-size))]
    [(heap-model (write b1:buf-loc b2:buf-loc))
          (and (<= b1 b-size)
          (<= b2 b-size))]
    [(heap-model (free b:buf-loc))
          (<= b b-size)]
    [(heap-model (alloc b:buf-loc natural))
     (<= b b-size)]))

(define (heap-model-valid-interaction s i)
  (define (heap-model-valid-interaction+ b-size h-size i)
    (match i
      [(heap-model nop)
       #t]
      [(heap-model (a:action i+:interaction))
       (and (heap-model-valid-action b-size a)
            (heap-model-valid-interaction b-size h-size i+))]))
  (match s
    [(heap-model (b:buf h:heap any))
     (heap-model-valid-interaction+ (seec-length b) (seec-length h) i)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define d (init-state 4 2))
(define aa0 (heap-model (alloc 0 1)))
(define aa1 (heap-model (alloc 1 1)))
(define as (heap-model (set 2 42)))
(define aw (heap-model (write 2 0)))
(define ar (heap-model (read 0 3)))


(define af0 (heap-model (free 0)))
(define af1 (heap-model (free 1)))


(define d++ (interpret-action aa1 (interpret-action aa0 d)))
(define d+4* (interpret-action af1 (interpret-action af0 d++)))


(define d+3 (interpret-action as d++))
(define d+4 (interpret-action aw d+3))
(define d+5 (interpret-action ar d+4))

(define i (heap-model (,aa1 (,aa0 (,as (,aw (,ar nop)))))))
(define o (heap-model (get 2)))
(define ti (heap-model (,i ,o)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMBOLIC TESTING heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (d-test0)
  (begin
    (define b0* (heap-model buf 4))
    (define h0* (heap-model heap 5))
    (define fp0* (heap-model pointer 1))
    (define s0* (heap-model (,b0* ,h0* ,fp0*)))
    (define s0+* (heap-model state 6))
    (define i0* (heap-model interaction 4))
    (define d0+* (interpret-interaction i0* d+5))
    (define beh0* (interpret-observation o  s0*))
    (define sol (verify #:guarantee (assert (not (equal? beh0* 5)))))
    (define s0 (concretize s0* sol))
    (define d0+ (concretize d0+* sol))
    (define i0 (concretize i0* sol))
    (define beh0 (concretize beh0* sol))
    (displayln "State:")
    (display-state s0)
    (displayln "Interaction:")
    (displayln i0)
    (displayln "Behavior:")
    (displayln beh0)))

    
