#lang seec


(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))

(require (file "heap-lang.rkt"))
(require (file "abstract-lang.rkt"))
(require (file "abstract-to-heap-compiler.rkt"))



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


;; need to create an abstract schema that has a freelist, and where an element in the buffer contains the target, and another a pointer to the valid block
(define (resize-query)
  (begin
    (define target (heap-model integer 1))
    (define s-* (state-buf-set 1 6 dc))
    (define s* (state-buf-set 3 target s-*))
    (define gadget (synthesize-interaction-gadget 4 s* (resize-spec 3 1)))
    (displayln "Gadget:")
    (displayln gadget)))
    
  
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

(define (next-alloc-query)
  (begin
    (define target (heap-model integer 2))
    (define s* (state-buf-set 0 target dc))
    (define gadget (synthesize-interaction-gadget 4 s* (next-alloc-spec 0)))
    (displayln "Gadget:")
    (displayln gadget)))

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
(define (insert-in-freelist-query)
  (begin
    (define target (heap-model integer 2))
    (define s-* (state-buf-set 3 (state->pointer dc) dc))
    (define s* (state-buf-set 1 target s-*))
    (define gadget (synthesize-interaction-gadget 4 s* (next-alloc-spec 1)))
    (displayln "Gadget:")
    (displayln gadget)))


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
          (define s (state-buf-set 0 (state->pointer s-) s-))
          (define s+ (interpret-interaction i s))
          (displayln "in initial state:")
          (display-state s--)
          (display "Results in state: ")
          (display-state s+)))))


; Then, try to find a gadget that discovers the head of the freelist
(define (find-freelist-head-spec bl0)
  (lambda (p s+)
    (let* ([s (cdr p)]
           [val (nth (state->buf s+) bl0)])
       (equal? (state->pointer s+) val))))

(define (find-freelist-head-query)
  (begin
    (define fp* (heap-model pointer 2))
    (define s* (state-fp-set fp* dc))
    (define gadget (synthesize-interaction-gadget 5 s* (find-freelist-head-spec 2)))
    (displayln "Gadget:")
    (displayln gadget)))

(define (find-freelist-head-gadget-syn)
  (begin
    (define fp* (heap-model pointer 2))
    (define s-* dc)
    (define s* (state-fp-set fp* s-*))
    (define i* (heap-model interaction 5))
    (define p* (cons i* s*))
    (define s+* (interpret-interaction i* s*))
    (define sol (synthesize
                 #:forall (list fp*)
                 #:guarantee (assert ((find-freelist-head-spec 2) p* s+*))))
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
    (define s-* dc)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Trying to find gadgets and decoders at the same time
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; type: Integer
(define-attack obs-heap
  #:grammar heap-model
  #:gadget complete-interaction #:size 5
  #:evaluate-gadget interpret-complete-interaction
  #:decoder interaction #:size 4
  #:evaluate-decoder (lambda (dec state) (obs-buf-def 0 0 (interpret-interaction dec state))))

; type: Boolean
(define-attack obs-alloc
  #:grammar heap-model
  #:gadget complete-interaction #:size 5
  #:evaluate-gadget interpret-complete-interaction
  #:decoder interaction #:size 4
  #:evaluate-decoder (lambda (dec state) (equal?
                                          1
                                          (obs-heap-def 0 0 (interpret-interaction dec state))))
  )


; based on obs-heap
; assumes: state is valid, with head of the freelist in 0 (make that a validity predicate)
; should find: 
; get: find the head of the freelist (in 0), as decoder
; put n: new head of the freelist is n (e.g. 6)
(define (get-put-head-gadgets)
  (define s-* dc)
  (define s* (state-buf-set 0 2 s-*))
  (define dec* (heap-model interaction 5)) ; find the head of the freelist
  (define target* (heap-model integer 2))
  (define s+* (state-buf-set 1 target* s*))  
  (define gadget* (heap-model interaction 4)) ; set the next block to be 
  (define s++* (interpret-interaction gadget* s+*));
  (define s+++* (interpret-interaction dec* s++*))
  (define sol (synthesize
               #:forall (list target*)
               #:guarantee (assert (equal? target*
                                           (obs-buf 0 s+++*)))))
  (if (unsat? sol)
      (displayln "UNSAT")
      (begin
        (displayln "SAT")
        (define target 4)
        (define dec (concretize dec sol))
        (define gadget (concretize gadget sol))
        (displayln "Dec:")
        (displayln dec)
        (displayln "Gadget:")
        (displayln gadget))))

; based on obs-alloc
; trying to get a gadget which toggles the alloc state of a block
; and a decoder which observes the alloc state of a block
(define (toggle-alloc)
  (define s-* dc)
  (define s* (state-buf-set 0 2 s-*))
  (define dec* (heap-model interaction 4)) ; get the value of nth
  (define target* (heap-model integer 2))
  (define s+* (state-buf-set 1 target* s*))  
  (define gadget* (heap-model interaction 4)) ; set the next block to be 
  (define s++* (interpret-interaction gadget* s+*));
  (define s+++* (interpret-interaction dec* s++*))
  (define sol (synthesize
               #:forall (list target*)
               #:guarantee (assert (not (equal? (obs-heap 0 s-*)
                                                (obs-heap 0 s++*))))))
  (if (unsat? sol)
      (displayln "UNSAT")
      (begin
        (displayln "SAT")
        (define target 4)
        (define dec (concretize dec sol))
        (define gadget (concretize gadget sol))
        (displayln "Dec:")
        (displayln dec)
        (displayln "Gadget:")
        (displayln gadget)))
  #f)
  
