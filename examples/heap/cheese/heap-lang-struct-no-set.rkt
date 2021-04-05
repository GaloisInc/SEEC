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
  (state-con ::= (buf heap pointer))
 )


(struct state (buf heap pointer))

(define (make-state b h p)
  (state b h p))

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
  (< i (length (state->heap s))))

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



(define (interpret-action a s)
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

#;(define-language heap-lang
  #:grammar heap-model
  #:expression interaction #:size 3
  #:context state #:size 8
  #:link snoc
  #:evaluate (uncurry interpret-interaction))

(define-language heap-lang
  #:grammar heap-model
  #:expression interaction #:size 4
  #:context state-con #:size 8
  #:link (lambda (state inte)
           (match state
             [(heap-model (b:buf h:heap p:pointer))
              (cons inte (make-state b h p))]))
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
  (valid-heap-block-size (state->heap s)))

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
     (valid-freelist 3 (state->heap s) (state->pointer s)))


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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Trying to find a Resize gadget
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;; Resize (merge a certain block with the next block) ;;;
; Starting state: hl is allocated, with size n
; end state: hl is allocated, with size m
(define (resize-spec bl-size bl-block)
    (lambda (p s+)
      (let* ([s (cdr p)]
             [size (nth (state->buf s) bl-size)]
             [hl (nth (state->buf s) bl-block)]
             [val (nth (state->heap s+) (- hl 1))])
        (equal? size val))))

(define (resize-gadget-query)
  (begin
    (define target (heap-model integer 2))
    (define s* (make-state-con (state-buf-set 3 target d+3*)))
    (find-gadget heap-lang (resize-spec 3 1) #:context s*)))
    
  
(define (resize-gadget-syn)
  (begin
    (define s--* dc)
    (define s-* (state-buf-set 1 6 s--*))
    (define target* (heap-model integer 2))
    (define s* (state-buf-set 3 target* s-*))
    (define i* (heap-model interaction 4))
    (define p* (cons i* s*))
    (define s+* (interpret-interaction i* s*))
    (define sol (synthesize #:forall (list target*)
                            #:guarantee (assert ((resize-spec 3 1) p* s+*))))
    (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (displayln "SAT")
          (define s-- (concretize s--* sol))
          (define target 42)
          (define s- (state-buf-set 1 6 s--))
          (define s (state-buf-set 3 target s-))
          (define i (concretize i* sol))
          (define s+ (interpret-interaction i s))
          (displayln "Interaction: ")
          (display "set buf[3] to any integer (here 42) and buf[1] to the target block, then ")
          (displayln i)
          (displayln "State:")
          (display-state s--)
          (displayln "Results in State:")
          (display-state s+)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Trying to find a next-alloc gadget
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;; Forces next alloc to return a specific pointer ;;;
(define (next-alloc-spec bl-target)
  (lambda (p s+)
    (let* ([s (cdr p)]
           [target (nth (state->buf s) bl-target)])
         (equal? (state->pointer s+) target))))

; WARNING: this is very slow at |i*| < 6
(define (next-alloc-gadget-syn)
  (begin
    (define s-* (clear-buf d+3*))
    (define target* (heap-model integer 2))
    (define s* (state-buf-set 0 target* s-*))
    (define i* (heap-model interaction 5))
    (define p* (cons i* s*))
    (define s+* (interpret-interaction i* s*))
    (define sol (synthesize
                   #:forall (list target*)
                   #:assume (assert (state-safe-write (+ target* 1) s*)) ; making sure target+1 is writable for next (alloc) to succeed
                   #:guarantee (assert ((next-alloc-spec 0) p* s+*))))
    (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (displayln "SAT")
          (define target 4)
          (define s- (concretize s-* sol))
          (define i (concretize i* sol))
          (display "Interaction: ")
          (display "Set b[1] to ")
          (display target)
          (display ", then")
          (displayln i)
          (define s (state-buf-set 0 target s-))
          (displayln  "Done s")
          (define s+ (interpret-interaction i s))
          (displayln "in initial state:")
          (display-state s-)
          (display "Results in state: ")
          (display-state s+)))))

; Try to find a simpler gadget where the head of the freelist is already known
(define (insert-in-freelist-gadget-syn)
  (begin
    (define s--* (clear-buf d+3*))
    (define target* (heap-model integer 2))
    (define s-* (state-buf-set 1 target* s--*))
    (define s* (state-buf-set 0 (state->pointer s-*) s-*))
    (define i* (heap-model interaction 4))
    (define p* (cons i* s*))
    (define s+* (interpret-interaction i* s*))
    (define sol (synthesize
                   #:forall (list target*)
                   #:assume (assert (state-safe-write (+ target* 1) s*)) 
                   #:guarantee (assert ((next-alloc-spec 1) p* s+*))))
    (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (displayln "SAT")
          (define target 4)
          (define s-- (concretize s--* sol))
          (define i (concretize i* sol))
          (display "Interaction: ")
          (display "Set b[1] to ")
          (display target)
          (display " and b[0] to fp, then")
          (displayln i)
          (define s- (state-buf-set 1 target s--))
          (displayln  "Done s-")
          (define s (state-buf-set 0 (state->pointer s-) s-))
          (displayln  "Done s")
          (define s+ (interpret-interaction i s))
          (displayln "in initial state:")
          (display-state s--)
          (display "Results in state: ")
          (display-state s+)))))


; Then, try to find a gadget that discovers the head of the freelist
(define (find-freelist-head-spec bl0)
  (lambda (s s+)
       (let* ([val (nth (state->buf s+) bl0)])
               (equal? (state->pointer s+) val))))


(define (find-freelist-head-gadget-syn)
  (begin
    (define fp* (heap-model pointer 2))
    (define s-* dc)
    (define s* (state-fp-set fp* s-*))
    (define i* (heap-model interaction 5))
    (define s+* (interpret-interaction i* s*))
    (define sol (synthesize
                 #:forall (list fp*)
                 #:guarantee (assert ((find-freelist-head-spec 2) s* s+*))))
    (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (displayln "SAT")
          (define fp 2)
          (define s- (concretize s-* sol))
          (define s (state-fp-set fp s-))
          (define i (concretize i* sol))
          (define s+ (interpret-interaction i s))
          (display "For any fp (here ")
          (display fp)
          (displayln "), State:")
          (display-state s)
          (display "Interaction: ")
          (displayln i)
          (displayln "Results in state: ")
          (display-state s+)))))
    


; Can now compose the result of find-freelist-head and insert-in-freelist to form next-alloc (of SEEC size 7)
(define (next-alloc bl-target bl0 bl1)
  (heap-model (cons (alloc ,bl0)
                    (cons (copy ,bl0 ,bl1)
                          (cons (free ,bl0) ; at this point, head of the free list is in bl1
                                (cons (write ,bl-target ,bl1)
                                      (cons (alloc ,bl0) nil)))))))

(define (next-alloc-gadget-verify)
  (begin
    (define s-* (clear-buf d+3*))
    (define target* (heap-model integer 2))
    (define s* (state-buf-set 0 target* s-*))
    (define i* (next-alloc 0 1 2))
    (define p* (cons i* s*))
    (define s+* (interpret-interaction i* s*))
    (define sol (verify (assert ((next-alloc-spec 0) p* s+*))))
    (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (displayln "SAT")          
          (define target (concretize target* sol))
          (define s- (concretize s-* sol))
          (define i (concretize i* sol))
          (display "Interaction: ")
          (display "Set b[1] to ")
          (display target)
          (display ", then")
          (displayln i)
          (define s (state-buf-set 0 target s-))
          (displayln  "Done s")
          (define s+ (interpret-interaction i s))
          (displayln "in initial state:")
          (display-state s-)
          (display "Results in state: ")
          (display-state s+)))))









