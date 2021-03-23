 #lang seec

(require seec/private/util)
(require seec/private/monad)
(require racket/format)
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
(require (file "lib.rkt"))
(provide (all-defined-out))



;
; Heap allocator model (buf-loc version)
; Inspired by ARCHEAP
; blocks have the form | In use? | size | payload ... |
; blocks in the freelist have the form | 0 | size | fw | bw | ... | 
; state is initialize with wilderness (in use? = 0, not in the freelist) and freelist = null

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
          (copy buf-loc buf-loc) ; overwrite (2) with value of (1)
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= list<action>)
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


(define (fold f l s)
  (match l
    [(heap-model nil)
     s]
    [(heap-model (cons hd:any l+:list<any>))
     (f s (fold f l+ s))]))


;; lifted list operations
(define (length s)
  (match s
    [(heap-model nil) 0]
    [(heap-model (cons any h:any))
     (+ 1 (length h))]))

(define (head s)
  (match s
    [(heap-model (cons x:any any))
     x]
    [_  (assert #f)
        ]))

(define (tail s)
    (match s
    [(heap-model (cons any tl:any))
     tl]    
    [_ (assert #f)
       ]))

; get the first nth value from the head of l
(define (first-nth n l)
  (if (equal? n 0)
      (heap-model nil)
      (heap-model (cons ,(head l) ,(first-nth (- n 1) (tail l))))))

(define (skip n l)
  (if (equal? n 0)
      l
      (let  ([tl (tail l)])
          (skip (- n 1) tl))))
    

(define (append s1 s2)
  (match s1
    [(heap-model nil) s2]
    [(heap-model (cons hd:any tl:any))
     (heap-model (cons ,hd ,(append tl s2)))]))

; fails if out of bound
(define (nth s i)
  ;  (-> any/c natural-number/c any/c)
  (if (equal? i 0)
      (head s)
      (let ([ts  (tail s)])
          (nth ts (- i 1)))))

(define (opt-nth s i)
  (if (and (<= 0 i)
           (< i (length s)))
           
      (nth s i)
      *fail*))


; add v at the end of list s
(define (enqueue s v)
    (match s
      [(heap-model nil)
       (heap-model (cons ,v nil))]
      [(heap-model (cons hd:any s+:any))
       (heap-model (cons ,hd ,(enqueue s+ v)))]))


; replace the ith element in l with v
; list* -> integer* -> value* -> list*
(define (replace l i v)
  (match i
    [(heap-model 0)
     (do tl <- (tail l)
         (heap-model (cons ,v ,tl)))]
    [(heap-model i:natural)
     (do hl <- (head l)
         tl <- (tail l)
         rl <- (replace tl (- i 1) v)
         (heap-model (cons ,hl ,rl)))]))

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
(define (write hp i v)
  ;(-> any/c natural-number/c any/c any/c)
  (if (equal? i 0)
      (heap-model (,v ,(tail hp)))
      (heap-model (,(head hp) ,(write (tail hp) (- i 1) v)))))

; init a state with buf size b-i and heap size (in cells) h-i
; heap has a wilderness (unused block not in free list) of size (h-i*4)-2

; natural -> natural -> state*
(define (init-state b-i h-i)
  (if (< h-i 1)
      false
      (let* ([payload (repeat (heap-model 0) (- (* h-i 4) 2))]           
             [hp (heap-model (cons ,(- (* h-i 4) 2) ,payload))]
             [hp+ (heap-model (cons 0 ,hp))])        
      (heap-model (,(repeat (heap-model 0) b-i) ,hp+ null)))))


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

; calculate the address of a heap-loc in the heap
(define (heap-loc-addr hl)
  (match hl
    [(heap-model n:natural)
     n]))


(define/debug (interpret-alloc-no-free h)
  (match h
    [(heap-model (cons in-use:value h+1:heap))
     (match h+1
       [(heap-model (cons size:value h+2:heap))
        (if (and (equal? in-use (heap-model 0))
                 (> size 1)) ; need enough space for that alloc
            (match h+2 ; skip 2
              [(heap-model (cons p1:value h+3:heap))
               (match h+3
                 [(heap-model (cons p2:value h+4:heap))
                  (if (> size 4) ; need to create a new wilderness
                      (match h+4
                        [(heap-model (cons p3:value h+5:heap))
                         (match h+5
                           [(heap-model (cons p4:value h+6:heap))
                            (cons 2 (heap-model (cons 1 (cons 2 (cons ,p1 (cons ,p2 (cons 0 (cons ,(- size 4) ,h+6))))))))])])
                      ; free block is fully used (i.e. 2 or 3...)
                      (cons 2 (heap-model (cons 1 (cons ,size ,h+2)))))])])
            ; block is in use or too small, move to rest of heap
            (let* ([r (interpret-alloc-no-free (skip size h+2))])
              (match r
                [(cons i hr)
                 (let* ([new-i (+ i (+ size 2))]
                        [old-payload (first-nth size h+2)]
                        [old-block (heap-model (cons ,in-use (cons ,size ,old-payload)))]
                        [new-hr (append old-block hr)])
                   (cons new-i new-hr))])))])]))
     


; reallocate the block at the head of the free-list
; heap* -> natural -> (pointer* x heap*)
; returns new free pointer X new heap
(define (interpret-alloc-free h n)
  (do newf <- (nth h n) ; get the tail of the free-list
      size <- (nth h (- n 1)) ; get the size of this block
       (match size
         [(heap-model sz:natural)
          (do h+ <- (replace h (- n 2) (heap-model 1))
            (match newf
              [(heap-model nf:natural)
               (do h++ <- (replace h+ (+ nf 1) (heap-model null))
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
     (do size <- (nth h (- n 1))
       (match size
         [(heap-model sz:natural)
          (do h+ <- (replace h (- n 2) (heap-model 0))
              h++ <- (replace h+ n f)
              h+++ <- (replace h++ (+ n 1) (heap-model null))
              (match f 
                [(heap-model null)
               h+++]
                [(heap-model nf:natural)
                 (do h+4 <- (replace h+++ (+ nf 1) p)
                     h+4)]))]
         [_
          (assert #f)
          ]))]))



(define (interpret-action a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     ;(displayln "matched heap")
     (match a
       [(heap-model (copy bl0:buf-loc bl1:buf-loc))
        (let* ([val (nth b bl0)]
               [b+ (replace b bl1 val)])
          (heap-model (,b+ ,h ,f)))]                    
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)]
               [b+ (replace b bl (heap-model null))]
               [h+ (interpret-free h f p)])
          (heap-model (,b+ ,h+ ,p)))]
       [(heap-model (alloc bl:buf-loc))
        (match f
          [(heap-model n:natural)
           (let* ([ph+ (interpret-alloc-free h n)]
                  [b+ (replace b bl f)])
             (heap-model (,b+ ,(cdr ph+) ,(car ph+))))]
          [(heap-model null)
           (let* ([ph+ (interpret-alloc-no-free h)]
                  [b+  (replace b bl (heap-model ,(car ph+)))])
             (heap-model (,b+ ,(cdr ph+) ,f)))])]
       [(heap-model (set bl:buf-loc val:nnvalue))
        (let* ([b+ (replace b bl val)])
          (heap-model (,b+ ,h ,f)))]
       [(heap-model (read bhl:buf-loc bl:buf-loc))
        ;(displayln "action read")
        (let* ([loc (nth b bhl)] ; get the pointer
               [val (nth h loc)] ; get the value at the location
               [b+ (replace b bl val)]) ; place the value in the buffer
             (heap-model (,b+ ,h ,f)))]
       [(heap-model (write bl:buf-loc bhl:buf-loc))
        ;(displayln "action write")
        (let* ([val (nth b bl)]
               [loc (nth b bhl)]
               [h+ (write h loc val)])
          (heap-model (,b ,h+ ,f)))])]))


(define (interpret-interaction i s)
    (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction i+ (interpret-action a s))]
    [(heap-model nil)
     s]))

(define-language heap-lang
  #:grammar heap-model
  #:expression interaction #:size 3
  #:context state #:size 8
  #:link snoc
  #:evaluate (uncurry interpret-interaction))

;; checks that the heap block layout is valid
;; every slot on the heap is either null or a size s followed s+1 slots
(define (valid-heap-block-size h)
  (match h
    [(heap-model nil)
     #t]
    [(heap-model (cons in-use:natural h+:heap))
     (match h+
       [(heap-model (cons size:natural h++:heap))
        (if (and (< in-use 2) ; s should be 0 or 1
                 (equal? size 2)) ; temporary
            (valid-heap-block-size (skip size h++))
            #f)]
       [(heap-model any)
        #f])]
    [(heap-model any)
     #f]))

(define (valid-state-block s)
    (match s
      [(heap-model (b:buf h:heap p:pointer))
       (and
        (valid-heap-block-size h)
        #;(valid-freelist fuel h p))]))

(define/debug (valid-freelist fuel h p)
  (define/debug #:suffix (valid-freelist+ fuel h p prev-p)
    (if (<= fuel 0)
        #t
        (match p      
          [(heap-model null)
           #t]
          [(heap-model l:natural)
           (do forward-p <- (nth h l)
               backward-p <- (nth h (+ l 1))
               check-v <- (nth h (- l 2))
             (if (and (equal? check-v (heap-model 0)) ; validation bit (size of pred) is properly set
                      (equal? backward-p prev-p)) ; backward pointer is properly set 
                      (valid-freelist+ (- fuel 1) h forward-p p)
             (begin
               #f)))]
          [(heap-model any)
           #f])))
  (not (failure? (valid-freelist+ fuel h p (heap-model null))))) ; capture failures 

(define (valid-freelist-state s)
  (match s
    [(heap-model (b:buf h:heap p:pointer))
     (valid-freelist 3 h p)]))


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

(define (print-list-value h)
  (match h
    [(heap-model nil)
     ""]
    [(heap-model (cons v:value h+:heap))
     (let ([sh+ (print-list-value h+)])
       (format " ~a |~a "
               (~a (print-value v) #:width 4)
               (~a sh+)))]))

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
       ;       (displayln "HEAP not a multiple of 4")
       (display (format "~a > |"
                        (~a addr #:width 2)))
       (displayln (print-list-value h))
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
; TESTING heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define d (init-state 4 2))
(define aa0 (heap-model (alloc 0)))
(define aa1 (heap-model (alloc 1)))
(define as (heap-model (set 2 7)))
(define aw (heap-model (write 2 0)))
(define ar (heap-model (read 0 3)))

(define af0 (heap-model (free 0)))
(define af1 (heap-model (free 1)))

(define d+  (interpret-action aa0 d))
(define d++ (interpret-action aa1 d+))


(define d+3* (interpret-action af0 d++))
(define d+4* (interpret-action af1 d+3*))


(define d+3 (interpret-action as d++))
(define d+4 (interpret-action aw d+3))
(define d+5 (interpret-action ar d+4))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Trying to create gadgets
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;; Allocate at (force the next block to be allocated to be at a certain place on the heap ;;;
; Starting state: any
; Goal: on end state, next (alloc x) has buf.x = hl
(define db (init-state 4 4))
(define db+  (interpret-action aa0 db))
(define db++ (interpret-action aa1 db+))



; assumes: bl0 bl1 disjoint
; result: bl0 points to head of list
; TODO: try to synthesize this gadget
(define (find-freelist-head bl0 bl1)
       (heap-model (cons (alloc ,bl1)
                         (cons (copy ,bl1 ,bl0)
                               (cons (free ,bl1) nil)))))

(define (find-freelist-head-gadget n)
  (lambda (s s+)
    (match s+
      [(heap-model (b:buf h:heap f:pointer))
       (equal? f n)])))

(define d+3*-a (interpret-interaction (find-freelist-head 0 1) d+3*))
; Assume: hd of freelist is at bl0, and bl1, bl2 and bl0 are disjoint cells
; Result: freelist is still headed at *bl0, but block at hl is now linked (as second element)
(define (insert-in-freelist bl0 bl1 bl2 hl)
       (heap-model (cons (read ,bl0 ,bl1) ; read next (fwd*bl0)
                         (cons (set ,bl2 ,hl) ; set bl2 to hl
                               (cons (write ,bl2 ,bl0) ; at this point fwd*bl0 points to hl
                                     (cons (write ,bl1 ,bl2) ; at this point fwd*hl points to next
                                           (cons (set ,bl2 ,(+ hl 1)) ; set bl2 to bwd*hl
                                                 (cons (write ,bl0 ,bl2) ;set bwd*hl to hd
                                                       (cons (set ,bl2 ,(- hl 2))
                                                             (cons (set ,bl1 0)
                                                                   (cons (write ,bl1 ,bl2)
                                                                         nil)))))))))))

; Assume: hd of freelist is at bl0, and bl0, bl1, bl2 are disjoint cells
; Result: freelist is still headed at *bl0, fwd points to hl (but freelist may be invalid)
(define (insert-in-freelist-unsafe bl0 bl1 bl2 hl)
  (heap-model (cons (read ,bl0 ,bl1)
                    (cons (set ,bl2 ,hl) ; set bl1 to hl
                          (cons (write ,bl2 ,bl0) ; at this point fwd*bl0 points to hl
                                (cons (write ,bl1 ,bl2) ; set fwd*hl to next
                                      nil))))))

(define d+3*-a+u (interpret-interaction (insert-in-freelist-unsafe 0 1 2 6) d+3*-a))
(define d+3*-a+ (interpret-interaction (insert-in-freelist 0 1 2 6) d+3*-a))


(define (insert-in-freelist-gadget hl)
  (lambda (s s+)
    (let* ([s++ (interpret-action (heap-model (alloc 0)) s+)])           
      (match s++
        [(heap-model (b:buf h:heap f:pointer))
         (equal? (nth b 0) hl)]))))


; Allocate a block at location hl
; assumes: hl-2 to hl+1 are valid locations, there is space for one extra block on freelist
(define (allocate-at hl)
  (append (find-freelist-head 0 1)
          (append (insert-in-freelist 0 1 2 hl)
                  (heap-model (cons (alloc 0)
                                    (cons (alloc 0) nil))))))

(define d+3*-alloc (interpret-interaction (allocate-at 6) d+3*))


;;;; Resize (merge a certain block with the next block) ;;;
; Starting state: hl is allocated, with size n, and block at hl+n+2 has size m 
; end state:  hl has size n+m
