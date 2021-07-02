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
; blocks have the form | In use? | size | payload ... |
; blocks in the freelist have the form | 0 | size | fw | bw | ... | 
; state is initialize with wilderness (in use? = 0, not in the freelist) and freelist = null
(define-grammar heap-model
  (pointer ::= natural null)
  (offset ::= integer)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer)
  (buf-loc ::= natural)
  (buf ::= list<value>)
  (heap-loc ::= pointer)
  (heap ::= list<value>) 
  (action ::=
          (read buf-loc buf-loc) ; place the element at pointer (1)buf-loc in heap into the buffer at (2)buf-loc
          (write buf-loc buf-loc); place the element at (1)buf-loc in buffer into the heap pointer (2)buf-loc
          (copy buf-loc buf-loc) ; overwrite (2) with value of (1)
          (incr buf-loc) ; add 1 to value at buf-loc
          (decr buf-loc) ; remove 1 to value at buf-loc
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= list<action>)
  (saction ::=
           (set buf-loc nnvalue))
  (setup ::= list<saction>)
  (complete-interaction ::= (setup interaction))
  (state-con ::= (buf heap pointer))
 )


(struct state (buf heap pointer))

(define (make-state b h p)
  (state b h p))

; from state-con to state
(define (make-state-struct s)
  (match s
    [(heap-model (b:buf h:heap p:pointer))
     (make-state b h p)]))
                 
    
; from state to state-con
(define (make-state-con s)
  (heap-model (,(state->buf s) ,(state->heap s) ,(state->pointer s))))

(define state->buf
  state-buf)
(define state->heap
  state-heap)
(define state->pointer
  state-pointer)



(define (fold f l s)
  (match l
    [(heap-model nil)
     s]
    [(heap-model (cons hd:any l+:list<any>))
     (f s (fold f l+ s))]))


;; lifted list operations
(define (s-length s)
  (match s
    [(heap-model nil) 0]
    [(heap-model (cons any h:any))
     (+ 1 (s-length h))]))

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

(define (drop-nth n l)
  (append (first-nth n l) (skip (+ n 1) l)))

; fails if out of bound
;(define/debug #:suffix (nth s i)
(define (nth s i)
  (for/all ([i i #:exhaustive])
  ;  (-> any/c natural-number/c any/c)
  (if (equal? i 0)
      (head s)
      (let ([ts  (tail s)])
          (nth ts (- i 1))))))

(define (opt-nth s i)
  (if (and (<= 0 i)
           (< i (s-length s)))
           
      (nth s i)
      *fail*))

(define (map f l)
  (match l
    [(heap-model nil)
     l]
    [(heap-model (cons hd:any l+:any))
     (heap-model (cons ,(f hd) ,(map f l+)))]))

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


(define (and-seec-list f l)
  (match l
    [(heap-model nil)
     #t]
    [(heap-model (cons hd:any l+:any))
     (and (f hd)
          (and-seec-list f l+))]))

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

; return the address of the nth block
(define (block-addr n)
  (+ (* n 4) 2))


; return #t if h doesn't contain any allocated blocks
(define (empty-heap? h)
  (match h
    [(heap-model nil)
     #t]
    [(heap-model (cons v-alloc:natural (cons v-size:natural h+:heap)))
     (if (equal? v-alloc 0)
         (empty-heap? (skip v-size h+))
         #f)]
    [(heap-model any)
     #f]))

; return #t if the heap consists of allocated and unallocated blocks of size 2
(define (valid-heap? h)
  (match h
    [(heap-model nil)
     #t]
    [(heap-model (cons v-alloc:natural (cons 2:natural (cons any (cons any h+:heap)))))
     (if (or (equal? v-alloc 0)
             (equal? v-alloc 1))
         (valid-heap? h+)
         #f)]
    [(heap-model any)
     #f]))

; write value at the ith position of cell
(define (write hp i v)
  ;(-> any/c natural-number/c any/c any/c)
  (if (equal? i 0)
      (heap-model (,v ,(tail hp)))
      (heap-model (,(head hp) ,(write (tail hp) (- i 1) v)))))

; init a state with buf size b-i and heap size (in cells) h-i
; heap has a wilderness (unused block not in free list) of size (h-i*4)-2
; buf -> natural -> state*
(define (init-state b h-i)
  (if (< h-i 1)
      false
      (let* ([payload (repeat (heap-model 0) (- (* h-i 4) 2))]           
             [hp (heap-model (cons ,(- (* h-i 4) 2) ,payload))]
             [hp+ (heap-model (cons 0 ,hp))])        
      (state b hp+ (heap-model null)))))

(define (init-empty-state b-i h-i)
  (init-state (repeat (heap-model 0) b-i) h-i))


; set loc bl in buffer of s to val
(define (state-buf-set bl v s)
  (let* ([b (state->buf s)]
        [b+ (replace b bl v)])
    (state b+ (state->heap s) (state->pointer s))))

(define (state-fp-set fp s)
  (state (state->buf s) (state->heap s) fp))

; check if p is a valid pointer in s->heap
(define (state-safe-write i s)
  (< i (s-length (state->heap s))))


; check if the size of the buf and heap of the state are exactly bs and hs.
(define (state-size bs hs)
  (lambda (s)
    (and (equal? (s-length (state->buf s)) bs)
         (equal? (s-length (state->heap s)) hs))))

(define (state-con-size bs hs)
  (lambda (s)
    ((state-size bs hs) (make-state-struct s))))

(define (state-same-heap s s+)
  (equal? (state->heap s) (state->heap s+)))

(define (state-con-same-heap s s+)
  (state-same-heap (make-state-struct s) (make-state-struct s+)))


(define (prog-state-size bs hs)
  (lambda (p)
    (let ([s (cdr p)])
      ((state-size bs hs) s))))

    
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

(define (find-interaction-size size i)
  (begin
    (define i* (heap-model interaction size))
    (define sol (solve (assert (equal? i* i))))
    (if (unsat? sol)
        (displayln "UNSAT")
        (displayln "SAT"))))


; calculate the address of a heap-loc in the heap
(define (heap-loc-addr hl)
  (match hl
    [(heap-model n:natural)
     n]))


(define (interpret-alloc-no-free h)
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
  (let* ([newf  (nth h n)] ; get the tail of the free-list
         [h+ (replace h (- n 2) (heap-model 1))]) ; alloc the head of the free-list
          (match newf
            [(heap-model nf:natural)
             (do h++ <- (replace h+ (+ nf 1) (heap-model null)) ; change the new head's backward pointer to be null
                 (cons newf h++))]
            [(heap-model null)
             (cons newf h+)])))



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



(define/debug (interpret-action a s)
 (for/all ([a a])
;            [s s])
    (debug-display "~a" a)
    (let ([b (state->buf s)]
          [h (state->heap s)]
          [f (state->pointer s)])
     (match a
       [(heap-model (copy bl0:buf-loc bl1:buf-loc))
        (let* ([val (nth b bl0)]
               [b+ (replace b bl1 val)])
          (state b+ h f))]                    
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)]
               [b+ (replace b bl (heap-model null))]
               [h+ (interpret-free h f p)])
          (state b+ h+ p))]
       [(heap-model (alloc bl:buf-loc))
        (match f
          [(heap-model n:natural)
           (let* ([ph+ (interpret-alloc-free h n)]
                  [b+ (replace b bl f)])
             (state b+ (cdr ph+) (car ph+)))]
          [(heap-model null)
           (let* ([ph+ (interpret-alloc-no-free h)]
                  [b+  (replace b bl (heap-model ,(car ph+)))])
             (state b+ (cdr ph+) f))])]
       [(heap-model (incr bl:buf-loc))
        (let* ([val (nth b bl)]
               [b+ (replace b bl (+ val 1))])
          (state b+ h f))]
       [(heap-model (decr bl:buf-loc))
        (let* ([val (nth b bl)]
               [b+ (replace b bl (- val 1))])
          (state b+ h f))]
       [(heap-model (read bhl:buf-loc bl:buf-loc))
        (let* ([loc (nth b bhl)] ; get the pointer
               [val (nth h loc)] ; get the value at the location
               [b+ (replace b bl val)]) ; place the value in the buffer
             (state b+ h f))]
       [(heap-model (write bl:buf-loc bhl:buf-loc))
        (let* ([val (nth b bl)]
               [loc (nth b bhl)]
               [h+ (write h loc val)])
          (state b h+ f))]))))


(define (interpret-interaction i s)
    (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction i+ (interpret-action a s))]
    [(heap-model nil)
     s]))

(define (interpret-saction a s)
  (match a
    [(heap-model (set bl:buf-loc v:nnvalue))
     (state-buf-set bl v s)]))
                 


(define (interpret-setup setup s)
  (match setup
    [(heap-model nil)
     s]
    [(heap-model (cons a:saction setup+:setup))
     (interpret-setup setup+ (interpret-saction a s))]))

(define (interpret-complete-interaction ci s)
  (match ci
    [(heap-model (v:setup i:interaction))
     (interpret-interaction i (interpret-setup v s))]))


(define (default-val val def)
  (match val
    [(heap-model null)
     def]
    [(heap-model i:integer)
     i]))

(define (obs-buf n s)
  (nth (state->buf s) n))

(define (obs-buf-def n def s)
  (default-val (obs-buf n s) def))

(define (obs-heap n s)
  (nth (state->heap s) n))

(define (obs-heap-def n def s)
  (default-val (obs-heap n s) def))


(define heap-lang-link
  (lambda (state inte)
           (match state
             [(heap-model (b:buf h:heap p:pointer))
              (cons inte (make-state b h p))])))

(define heap-lang-link-state
  (lambda (inte state)
           (match state
             [(heap-model (b:buf h:heap p:pointer))
              (cons inte (make-state b h p))])))


(define-language heap-lang
  #:grammar heap-model
  #:expression interaction #:size 4
  #:context state-con #:size 10
  #:link heap-lang-link
  #:evaluate (uncurry interpret-interaction))

(define-language heap-lang-state
  #:grammar heap-model
  #:expression state-con #:size 10
  #:context action #:size 3
  #:link heap-lang-link-state
  #:evaluate (uncurry interpret-action))



(define (synthesize-interaction-gadget size ctx spec)
  (let* ([sol (find-gadget heap-lang
                           spec
                           #:expression-size size
                           #:expression-witness-only #t
                           #:context (make-state-con ctx))])
    (if sol
        (first sol)
        #f)))



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
  (begin
    (displayln "BUFFER:")
    (display-buf (state->buf s))
    (displayln "HEAP:")
    (display-heap (state->heap s))
    (displayln "FP HEAD:")
    (displayln (print-pointer (state->pointer s)))))
      



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define d (init-empty-state 4 2))
(define aa0 (heap-model (alloc 0)))
(define aa1 (heap-model (alloc 1)))
(define aw (heap-model (write 2 0)))
(define ar (heap-model (read 0 3)))

(define af0 (heap-model (free 0)))
(define af1 (heap-model (free 1)))

(define d+  (interpret-action aa0 d))
(define d++ (interpret-action aa1 d+))


(define d+3* (interpret-action af0 d++))
(define d+3** (interpret-action af1 d++))
(define d+4* (interpret-action af1 d+3*))
(define d+5* (interpret-action aa0 d+4*))
(define d+4** (interpret-action af0 d+3**))

(define d+3  (state-buf-set 2 7 d++))
(define d+4 (interpret-action aw d+3))
(define d+5 (interpret-action ar d+4))


(define (clear-buf s)
  (state (repeat (heap-model null) 4) (state->heap s) (state->pointer s)))

(define dc (clear-buf d+3*))











