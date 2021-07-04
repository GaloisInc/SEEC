#lang seec

(require (only-in racket/file
                  file->string))

(require (only-in racket/base
                  sleep))


(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang.rkt"))
(require (file "abstract-lang.rkt"))
(require (file "abstract-to-heap-compiler.rkt"))



(define (demo1)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd as*)))))

(define (recorded1)
  (begin
    (sleep 2)
    (display (file->string "./output/upper-demo-err-demo1w.txt"))))


(define (interpret-alloc-free+ h n)
  (let* ([newf  (nth h n)] 
         [h+ (replace h (- n 2) (heap-model 1))]
         [h++ (replace h+ n (heap-model 0))]
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

(define-language heap-lang+
  #:grammar heap-model
  #:expression state-con #:size 10
  #:context action #:size 3
  #:link heap-lang-link
  #:evaluate (uncurry interpret-action+))


(define-compiler abstract-to-heap-nd+
  #:source abstract-lang
  #:target heap-lang+
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))


(define (demo2)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd+ as*)))))

(define (recorded2)
  (begin
    (sleep 2)
    (display (file->string "./output/upper-demo-err-demo2w.txt"))))


; found: (write 1 2) where 2 is not a pointer
; sol: ignore read/write from non-pointers
(define/debug #:suffix (abs-interpret-action+ a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
     (match a
       [(abstract-model (read bhl:buf-loc bl:buf-loc))
        (let* ([loc (nth b bhl)] 
               [val (abs-read-heap h loc)]
               [b+ (replace b bl val)])
          (if val
              (abs-state b+ h)
              (assert #f)))]
       [(abstract-model (write bl:buf-loc bhl:buf-loc))
        (let* ([val (nth b bl)]
               [loc (nth b bhl)]
               [h+ (abs-write-heap h loc val)])
          (if h+
              (abs-state b h+)
              (assert #f)))]
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
  #:target heap-lang+
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))


(define (demo3)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd++ as*)))))

(define (recorded3)
  (begin
    (sleep 2)
    (display (file->string "./output/upper-demo-err-demo3w.txt"))))


; finds free on a non-pointers
; sol: ignore free from non-pointers
(define (abs-free+ b h bl)
  (let* ([p (nth b bl)]) ; get the pointer
    (match p
      [(abstract-model (P n:natural any))
       (let* ([b+ (replace b bl (abstract-model N))]
              [h+ (drop-nth n h)]
              [b++ (abs-shift-buf n b+)]
              [h++ (abs-shift-heap n h+)])
        (abs-state b++ h++))]
      [any
       (assert #f)])))


(define (abs-interpret-action++ a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
     (match a
       [(abstract-model (free bl:buf-loc))
        (abs-free+ b h bl)]
       [(abstract-model any)
        (abs-interpret-action+ a s)]))))

(define-language abstract-lang++
  #:grammar abstract-model
  #:expression state #:size 10
  #:context action #:size 3
  #:link cons
  #:evaluate (uncurry abs-interpret-action++))


(define-compiler abstract-to-heap-nd3
  #:source abstract-lang++
  #:target heap-lang+
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo4)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd3 as*)))))

(define (recorded4)
  (begin
    (sleep 2)
    (display (file->string "./output/upper-demo-err-demo4w.txt"))))

; finds free with an offset
; sol: change the spec of free to only be well-defined on pointers without offset
(define (abs-free++ b h bl)
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


(define (abs-interpret-action3 a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
     (match a
       [(abstract-model (free bl:buf-loc))
        (abs-free++ b h bl)]
       [(abstract-model any)
        (abs-interpret-action+ a s)]))))

(define-language abstract-lang3
  #:grammar abstract-model
  #:expression state #:size 10
  #:context action #:size 3
  #:link cons
  #:evaluate (uncurry abs-interpret-action3))


(define-compiler abstract-to-heap-nd4
  #:source abstract-lang3
  #:target heap-lang+
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo5)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd4 as*)))))

(define (recorded5)
  (begin
    (sleep 2)
    (display (file->string "./output/upper-demo-err-demo5w.txt"))))

; Found incr on a pointer with P 0 b
; Sol: ignore out of bound incr and decr
(define/debug #:suffix (abs-interpret-action4 a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
     (match a
       [(abstract-model (incr bl:buf-loc))
        (let* ([val (nth b bl)]
               [val+ (abs-incr val)]
               [b+ (replace b bl val+)])
          (if (abs-is-null? val+)
              (assert #f)
              (abs-state b+ h)))]
       [(abstract-model (decr bl:buf-loc))
        (let* ([val (nth b bl)]
               [val+ (abs-decr val)]
               [b+ (replace b bl val+)])
          (if (abs-is-null? val+)
              (assert #f)
              (abs-state b+ h)))]
       [(abstract-model any)
        (abs-interpret-action3 a s)]))))

(define-language abstract-lang4
  #:grammar abstract-model
  #:expression state #:size 10
  #:context action #:size 3
  #:link cons
  #:evaluate (uncurry abs-interpret-action4))


(define-compiler abstract-to-heap-nd5
  #:source abstract-lang4
  #:target heap-lang+
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo6)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd5 as*)))))

(define (recorded6)
  (begin
    (sleep 2)
    (display (file->string "./output/upper-demo-err-demo6w.txt"))))


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
        (bounded-equiv-buf+ ah (state->heap s) n ab (state->buf s)))]
      [(abstract-model any)
       ((bounded-equiv-state n) as s)])))

(define-compiler abstract-to-heap-nd6
  #:source abstract-lang4
  #:target heap-lang+
  #:behavior-relation (bounded-equiv-state+ 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo7)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd6 as*)))))

(define (recorded7)
  (begin
    (sleep 2)
    (display (file->string "./output/upper-demo-err-demo7w.txt"))))
