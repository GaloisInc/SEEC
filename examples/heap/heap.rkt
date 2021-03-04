#lang seec
(set-bitwidth 4)
(require seec/private/util)
(require seec/private/monad)
(require racket/format)
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
;(require racket/contract)
(provide (all-defined-out))


(use-contracts-globally #t)

;
; Heap allocator model 
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
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc natural)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= list<action>) ; list of actions
  (action-hl ::= ; like action but with heap-loc
             (set buf-loc nnvalue)
             (read heap-loc buf-loc)
             (write buf-loc heap-loc)
             (free heap-loc)
             (alloc buf-loc natural))
  (interaction-hl ::= list<action-hl>) ; like interaction but with heap-loc
  (observation ::=
               (get buf-loc))
  (total-interaction ::= ; perform interaction, then get nth value from buffer
                     (interaction observation))
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
    [(heap-model (cons x:any any))
     x]
    [(heap-model any)  #f]))

(define (tail s)
    (match s
    [(heap-model (cons any tl:any))
     tl]
    [(heap-model any) #f]))

(define (skip n l)
  (if (equal? n 0)
      l
      (skip (- n 1) (tail l))))
    

(define (append s1 s2)
  (match s1
    [(heap-model nil) s2]
    [(heap-model (cons hd:any tl:any))
     (heap-model (cons ,hd ,(append tl s2)))]))

; false if out of bound
(define (nth s i)
  ;  (-> any/c natural-number/c any/c)
  (if (equal? i 0)
      (head s)
      (let* ([tls (tail s)])
             (if tls
                 (nth tls (- i 1))
                 #f))))

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
    (let ([in-use (nth h i)]
          [size (nth h (+ i 1))])
      (if (equal? in-use (heap-model 0))
          ; found the wilderness, copy its size (at i+1), then allocate a new block pushing back the wilderness
            (let* ([h+ (replace h i (heap-model 1))]
                   [h++ (replace h+ (+ i 1) (heap-model 2))]
                   [h+++ (if (> size 4) (replace h++ (+ i 4) (heap-model 0)) h++)]
                   [h+4 (if (> size 4) (replace h+++ (+ i 5) (- size 4)) h+++)])
                ;(displayln (format "allocated at ~a a block of size ~a" i 2))
              (cons (heap-model ,(+ i 2)) h+4))
          (interpret-alloc-no-free+ h (+ i size 2)))))
  (interpret-alloc-no-free+ h 0))

; reallocate the block at the head of the free-list
; heap* -> natural -> (pointer* x heap*)
; returns new free pointer X new heap
(define (interpret-alloc-free h n)
  (let* ([newf (nth h n)] ; get the tail of the free-list
         [size (nth h (- n 1))]) ; get the size of this block
       (match size
         [(heap-model sz:natural)
          (let* ([h+ (replace h (- n 2) (heap-model 1))])            
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
          (let* ([h+ (replace h (- n 2) (heap-model 0))]
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
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction i+ (interpret-action a s))]
    [(heap-model nil)
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
    [(heap-model (cons a:action-hl i+:interaction-hl))
     (interpret-interaction-hl i+ (interpret-action-hl a s))]
    [(heap-model nil)
     s]))

; translate an action into a list of action-hl
; heap-model.action -> heap-model.interaction-hl
(define (translate-action-hl a s)
    (match s
    [(heap-model (b:buf h:heap f:pointer))
     (match a
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)])
          (heap-model (cons (free ,p) (cons (set ,bl null) nil))))]
        [(heap-model (read bhl:buf-loc bl:buf-loc))
         (let* ([hl (nth b bhl)]) ; get the pointer
                (heap-model (cons (read ,hl ,bl) nil)))]
       [(heap-model (write bl:buf-loc bhl:buf-loc))
        (let* ([hl (nth b bhl)])
          (heap-model (cons (write ,bl ,hl) nil)))]
       [(heap-model any) ; set, alloc
        (heap-model (cons ,a nil))]
       )]))

; translate an interaction into an interaction-hl
; heap-model.interaction -> heap-model.state -> heap-model.interaction-hl
(define (translate-interaction-hl i s)
  (match i
    [(heap-model nil)
     (heap-model nil)]
    [(heap-model (cons a:action i+:interaction))
     (let* ([i-hl (translate-action-hl a s)]
            [s+ (interpret-action a s)]
            [i-hl+ (translate-interaction-hl i+ s+)])
       (heap-model ,(append i-hl i-hl+)))]))

;;;
; Operations on pointers
;;;

; on aligned pointers
(define (fwd-pointer p)
  (match p      
    [(heap-model null)
     #f]
    [(heap-model l:natural)
     p]))

; on aligned pointers
(define (bwd-pointer p)
  (match p      
    [(heap-model null)
     #f]
    [(heap-model l:natural)
     (heap-model ,(+ l 1))]))

; on all pointers 
(define (in-use-pointer p)
  (match p      
    [(heap-model null)
     #t]
    [(heap-model l:natural)
     (heap-model ,(modulo l 4))]))

; on all pointers 
(define (size-pointer p)
  (match p      
    [(heap-model null)
     #t]
    [(heap-model l:natural)
     (heap-model ,(+ (modulo l 4) 1))]))


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
     ; TODO: I think < is not properly lifted to seec-rosette
     (not (< (seec-length h) l))]))


; pointer -> boolean
; true if p%4 = 1 
(define (fwd-pointer-alligned p)
  (match p
    [(heap-model null)
     #t]
    [(heap-model l:natural)
     (equal? 2 (remainder l 4))]))

; heap -> pointer -> boolean
; p is the head of a freelist in h
(define (valid-freelist fuel h p)
  (define (valid-freelist+ fuel h p prev-p)
    (if (<= fuel 0)
        #t
        (match p      
          [(heap-model null)
           #t]
          [(heap-model l:natural)
           (let* ([forward-p (nth h l)]
                  [backward-p (nth h (+ l 1))]
                  [check-v (nth h (- l 2))])
             (if (and forward-p
                      backward-p
                      check-v
                      (equal? check-v (heap-model 0)) ; validation bit (size of pred) is properly set
                      (fwd-pointer-alligned forward-p) ; fwd is pointing alligned 
                      (equal? backward-p prev-p)) ; backward pointer is properly set
                       
                 (valid-freelist+ (- fuel 1) h forward-p p)
             (begin
               #f)))])))
  (valid-freelist+ fuel h p (heap-model null)))

(define (valid-freelist-state fuel s)
  (match s
    [(heap-model (b:buf h:heap p:pointer))
     (valid-freelist fuel h p)]))


;; heap in heap-model is valid if length is divisible by 4
(define (valid-heap-size h)
  (zero? (remainder (seec-length h) 4)))

;; checks that the heap block layout is valid
;; every slot on the heap is either null or a size s followed s+1 slots
(define (valid-heap-block-size h)
  (match h
    [(heap-model nil)
     #t]
    [(heap-model (cons in-use:natural h+:heap))
     (match h+
       [(heap-model (cons size:natural h++:heap))
        (if (< in-use 2) ; s should be 0 or 1
            (valid-heap-block-size (skip size h++))
            #f)]
       [(heap-model any)
        #f])]
    [(heap-model any)
     #f]))

(define (valid-state fuel s)
  (match s
    [(heap-model (b:buf h:heap p:pointer))
     (and (<= 1 (seec-length b))
          (fwd-pointer-alligned p)
          (valid-heap-block-size h)
          (valid-heap-size h)
          (valid-freelist fuel h p))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Other predicates for heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; returns the length of the free-list 
(define (freelist-length fuel s)
  (define (freelist-length+ fuel h p)
    (if (<= fuel 0)
        #f
        (match p
          [(heap-model null)
           0]
          [(heap-model l:natural)
           (let* ([forward-p (nth h l)])
             (if forward-p
                 (+ (freelist-length+ (- fuel 1) h forward-p) 1)
                 #f))])))
    (match s
      [(heap-model (b:buf h:heap p:pointer))
       (freelist-length+ fuel h p)
       ]))


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




(define (heap-model-valid-interaction i s)
  (define (heap-model-valid-interaction+ b-size h-size i)
    (match i
      [(heap-model nil)
       #t]
      [(heap-model (cons a:action i+:interaction))
       (and (heap-model-valid-action b-size a)
            (heap-model-valid-interaction+ b-size h-size i+))]))
  (match s
    [(heap-model (b:buf h:heap any))
     (heap-model-valid-interaction+ (seec-length b) (seec-length h) i)]))


; true if p points to a valid payload:
; 0) p is non-null
; 1) p is not a header or footer
; 2) p's foot in 1
(define (safe-write p s)
  (match p
    [(heap-model null)
     #f]
    [(heap-model l:natural)
     (and (not (equal? 0 (remainder l 4)))
          (not (equal? 3 (remainder l 4))))
     ]))


; true if point p can be safely freed in state s
; 0) p is non-null
; 1) p is alligned
; 2) p is in use
(define (safe-free p s)
  (match p
    [(heap-model null)
     #f]
    [(heap-model l:natural)
     (match s
       [(heap-model (b:buf h:heap p+:pointer))
        (if (fwd-pointer-alligned p)
            (let* ([v-bit (nth (+ l 2) h)])
              (equal? v-bit (heap-model 1)))
            #f)])]))


(define (heap-model-safe-action a s)
  (match s
    [(heap-model (b:buf h:heap p+:pointer))
     (match a
       [(heap-model (set b:buf-loc any))
        #t]
       [(heap-model (read b1:buf-loc b2:buf-loc))
        #t]
       [(heap-model (write b1:buf-loc b2:buf-loc))
        (let* ([p (nth b b2)])
        (safe-write p s))]
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)])
            (safe-free p s))]
       [(heap-model (alloc b:buf-loc natural))
        #t])]))

(define (heap-model-safe-interaction i s)
    (match i
      [(heap-model nil)
       #t]
      [(heap-model (cons a:action i+:interaction))
       (and (heap-model-safe-action a s)
            (heap-model-safe-interaction i+ s))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define d (init-state 4 2))
(define aa0 (heap-model (alloc 0 1)))
(define aa1 (heap-model (alloc 1 1)))
(define as (heap-model (set 2 7)))
(define aw (heap-model (write 2 0)))
(define ar (heap-model (read 0 3)))


(define af0 (heap-model (free 0)))
(define af1 (heap-model (free 1)))

(define d+ (interpret-action aa0 d))
(define d++ (interpret-action aa1 d+))
(define d+3* (interpret-action af0 d++))
(define d+4* (interpret-action af1 d+3*))


(define d+3 (interpret-action as d++))
(define d+4 (interpret-action aw d+3))
(define d+5 (interpret-action ar d+4))

(define i (heap-model (cons ,aa1 (cons ,aa0 (cons ,as (cons ,aw (cons ,ar nil)))))))
(define o (heap-model (get 2)))
(define ti (heap-model (,i ,o)))

(define i-attack (heap-model (cons (set 0 2) (cons (set 1 3) (cons (write 0 1) nil)))))
(define d+5* (interpret-interaction i-attack d+4*))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMBOLIC TESTING heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define b0* (heap-model buf 4))
(define h0* (heap-model heap 9))
(define fp0* (heap-model pointer 1))
(define s0* (heap-model (,b0* ,h0* ,fp0*)))
;(valid-freelist-state 3 s0*)
;(valid-state 3 s0*) 

; Create a symbolic state that has (o s) != 5) and find some interaction that makes (o s+) = 5
(define (d-test0)
  (begin
    (define b0* (heap-model buf 4))
    (define h0* (heap-model heap 9))
    (define fp0* (heap-model pointer 1))
    (define s0* (heap-model (,b0* ,h0* ,fp0*)))
    (assert (valid-state 3 s0*))
    (define beh0* (interpret-observation o s0*))
    (assert (not (equal? beh0* 5)))    
    (define i0* (heap-model interaction 4))
    (define s0+* (interpret-interaction i0* s0*))
    (define beh0+* (interpret-observation o  s0+*))
    (define sol (solve (assert (equal? beh0+* 5))))
    (define s0 (concretize s0* sol))
    (define i0 (concretize i0* sol))
    (define beh0+ (concretize beh0+* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s0)
    (displayln "Interaction:")
    (displayln i0)
    (displayln "Behavior:")
    (displayln beh0+)))

; create a heap with a free-list of length 2 (fails at the moment, only 0 works)
(define (d-test1)
  (begin
    (define b1* (heap-model buf 4))
    (define h1* (heap-model heap 9))
    (define fp1* (heap-model pointer 1))
    (define s1* (heap-model (,b1* ,h1* ,fp1*)))
    (assert (valid-state 3 s1*))
    (define sol (solve (assert (equal? 0 (freelist-length 3 s1*)))))
    (define s1 (concretize s1* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s1)))



(define (d-test3)
  (begin
    (define b3* (heap-model buf 5))
    (define h3* (heap-model heap 9))
    (define fp3* (heap-model pointer 1))
    (define s3* (heap-model (,b3* ,h3* ,fp3*)))
    
   (assert (valid-state 3 s3*))
    (define sol (solve (assert (equal? d+4* s3*))))
    (define s3 (concretize s3* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s3)))



; try to make the state a concrete state
; works with d+4* [find two bugs before safe-interaction]
; doesn't terminate? with d+3/d+5
;
(define (d-test2)
  (begin
    (define s2* d+4*)
    (define i2* (heap-model interaction 4))
    (define s2+* (interpret-interaction i2* s2*))
;    (assert (heap-model-valid-interaction i2* s2*))
;    (assert (heap-model-safe-interaction i2* s2*))
    (define sol (solve (assert (not (valid-state 3 s2+*)))))
    (define s2 (concretize s2* sol))
    (define i2 (concretize i2* sol))
    (define s2+ (concretize s2+* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s2)
    (displayln "Interaction:")
    (displayln i2)
    (displayln (heap-model-safe-interaction i2 s2))
    (displayln (heap-model-valid-interaction i2 s2))
    (displayln "State+:")
    (display-state s2+)
    (displayln (valid-state 3 s2+))))



    
