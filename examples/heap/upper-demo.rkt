#lang seec


(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang.rkt"))
(require (file "heap-abstract-lang.rkt"))
(require (file "abstract-to-heap-compiler.rkt"))


(define (demo1)
  (display-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd as*)))))

; Found (free 3) when 1 also points to same block, resulting in dangling pointer
; Solution: treat null as undef
(define (bounded-equiv-val+ ah h n av v)
  (match av
    [(abstract-model N)
     #t]
    [(abstract-model any)
     (bounded-equiv-val ah h n av v)]))

(define (bounded-equiv-buf+ ah h n ab b)
    (match ab
      [(abstract-model nil)
       (match b
         [(heap-model nil) #t]
         [(heap-model any) #f])]
      [(abstract-model (cons av:any ab+:any))
       (match b
         [(heap-model (cons v:any b+:any))
          (and (bounded-equiv-val+ ah h n av v)
               (bounded-equiv-buf+ ah h n ab+ b+))]
         [(heap-model nil) #f])]))

(define/debug (bounded-equiv-state+ n)
  (lambda (as s)
    (match as
      [(abstract-model (ab:any ah:any))
       (and
        (valid-heap? (state->heap s))
        (bounded-equiv-buf+ ah (state->heap s) n ab (state->buf s)))])))

(define-compiler abstract-to-heap-nd+
  #:source abstract-lang
  #:target heap-lang-state
  #:behavior-relation (bounded-equiv-state+ 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo2)
  (display-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd+ as*)))))

; found (free 2) where 2 is P 0 b
; solution is to prevent free with offsets (either in implementation or abstraction)
(define (abs-free+ b h bl)
  (let* ([p (nth b bl)]) ; get the pointer
    (match p
      [(abstract-model (P n:natural a))
       (let* ([b+ (replace b bl (abstract-model N))]
              [h+ (drop-nth n h)]
              [b++ (abs-shift-buf n b+)]
              [h++ (abs-shift-heap n h+)])
        (abs-state b++ h++))]
      [any
       (assert #f)])))

(define (abs-interpret-action+ a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
     (match a
       [(abstract-model (free bl:buf-loc))
        (abs-free+ b h bl)]
       [(abstract-model any)
        (abs-interpret-action a s)]))))

(define-language abstract-lang+
  #:grammar abstract-model
  #:expression state #:size 10
  #:context action #:size 3
  #:link cons
  #:evaluate (uncurry abs-interpret-action+))

(define-compiler abstract-to-heap-nd++
  #:source abstract-lang+
  #:target heap-lang-state
  #:behavior-relation (bounded-equiv-state+ 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo3)
  (display-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd++ as*)))))

; found (alloc 3) since implementation alloc doesn't clear the data on the heap
(define (interpret-alloc-free+ h n)
  (let* ([newf  (nth h n)] ; get the tail of the free-list
         [h+ (replace h (- n 2) (heap-model 1))]  ; alloc the head of the free-list
         [h++ (replace h+ n (heap-model 0))] ; set the payload to 0
         [h+3 (replace h++ (+ n 1) (heap-model 0))])
          (match newf
            [(heap-model nf:natural)
             (do h+4 <- (replace h+3 (+ nf 1) (heap-model null)) ; change the new head's backward pointer to be null
                 (cons newf h+4))]
            [(heap-model null)
             (cons newf h+3)])))

(define (interpret-action+ a s)
  (let ([b (state->buf s)]
        [h (state->heap s)]
        [f (state->pointer s)])
    (match f
      [(heap-model n:natural)
       (match a
         [(heap-model (alloc bl:buf-loc))
          (let* ([ph+ (interpret-alloc-free+ h n)]
                 [b+ (replace b bl f)])
            (state b+ (cdr ph+) (car ph+)))]
         [(heap-model any)
          (interpret-action a s)])]
      [(heap-model any)
       (interpret-action a s)])))

(define-language heap-lang-state+
  #:grammar heap-model
  #:expression state-con #:size 10
  #:context action #:size 3
  #:link heap-lang-link-state
  #:evaluate (uncurry interpret-action+))


(define-compiler abstract-to-heap-nd+++
  #:source abstract-lang+
  #:target heap-lang-state+
  #:behavior-relation (bounded-equiv-state+ 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo4)
  (display-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd+++ as*)))))
