#lang seec

(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang.rkt"))
(require (file "heap-abstract-lang.rkt"))
(require (file "abstract-to-heap-compiler.rkt"))

; try to find the weird behavior with pointer overflow manually
(define (manual-weird-incr)
  (define e1* (car (make-small-abstract-state)))
  (define c1* (abstract-model action 3))
  (assert (equal? c1* (abstract-model (incr 1))))
  (define c2* (heap-model (incr 1))) ; fix c2
;  (let*-values ([(p* nondet*) (capture-nondeterminism #:nondet #t (generate-permutation-fl 2 1))])
  (let* ([p* (list 0 #f)]
         [e2* (make-state-struct (test-abs-into-heap-fl p* e1*))]
         [e1+* (abs-interpret-action c1* e1*)]
         [e2+* (interpret-action c2* e2*)])      
      (define sol (synthesize
                   #:forall (list c1*)
;                   #:assume (assert (equal? c1* (abstract-model (incr 1))))
                   #:guarantee (assert (not ((bounded-equiv-state 3) e1+* e2+*)))))
      (if (unsat? sol)
          (displayln "unsat")
          (begin
            (displayln "sat")
            (define e1 (concretize e1* sol))
            (displayln "Source state:")
            (display-abs-state e1)
            (define e2 (concretize e2* sol))
            (displayln "Compiled to target state:")
            (display-state e2)
            (define c2 (concretize c2* sol))
            (displayln "Evaluates, under action: ")
            (displayln c2)
            (define e2+ (interpret-action c2 e2))
            (displayln "to target state: ")
            (display-state e2+)
            ))))

(define e1b* (abstract-model (cons N (cons (P 0 b) (cons 0 (cons 0 nil))))))
(define e1h* (abstract-model (cons (0 0) nil)))
(define e1* (abstract-model (,e1b* ,e1h*)))
(define c2* (heap-model (incr 1)))
(define e2* (make-state-struct (test-abs-into-heap-fl (list 0 #f) e1*)))
(define e2+* (interpret-action c2* e2*))


; need to change the context-relation to accept any action rather than equal? ones
; this finds (free 3) when 1 = 3 = P 0 a, i.e. dangling pointer
(define (demo1-w)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd as* #:target-context-where (lambda (e1 c2) (equal? c2 (heap-model (incr 1)))))))))


(define (demo1)
  (display-changed-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd as*)))))

; same time as demo1 here, but may be useful as a query transformer
(define (demo1-nc)
  (let ([c1 (abstract-model action 3)])
    (display-abstract-to-heap
     (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nc as* #:source-context c1 #:target-context c1))))))

; found write-after-free activation in 150s
(define (demo1-wnc)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nc as* )))))


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

(define-compiler abstract-to-heap-nc+
  #:source abstract-lang
  #:target heap-lang-state
  #:behavior-relation (bounded-equiv-state+ 3)
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))


(define (demo2)
  (display-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd+ as*)))))
; found free 2
(define (demo2-w)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd+ as*)))))


; I'm confused by what it's giving me here
(define (demo2-wnc)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nc+ as*)))))


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

(define-compiler abstract-to-heap-nc++
  #:source abstract-lang+
  #:target heap-lang-state
  #:behavior-relation (bounded-equiv-state+ 3)
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))


(define (demo3)
  (display-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd++ as*)))))

; found the alloc bug
(define (demo3-w)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd++ as*)))))


; this finds an alloc with a free list which create payload with null-null
(define (demo3-wnc)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nc++ as*)))))


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

(define-compiler abstract-to-heap-nc+++
  #:source abstract-lang+
  #:target heap-lang-state+
  #:behavior-relation (bounded-equiv-state+ 3)
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

(define (demo4)
  (display-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-changed-behavior abstract-to-heap-nd+++ as*)))))

(define (demo4-w)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd+++ as*)))))


; this one finds (incr 0) on a buffer slot with P 0 b. One way to ignore this is (after the fix to null pointers) is to make out of bound pointers null
(define (demo4-wnc)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nc+++ as*)))))

(define (abs-incr+ val)
  (match val
    [(abstract-model i:integer)
     (abstract-model ,(+ i 1))]
    [(abstract-model (P n:natural s:selector))
     (abs-select s                 
                 (abstract-model (P ,n b))
                 (abstract-model N))]))

(define (abs-decr+ val)
  (match val
    [(abstract-model i:integer)
     (abstract-model ,(- i 1))]
    [(abstract-model (P n:natural s:selector))
     (abs-select s
                 (abstract-model N)
                 (abstract-model (P ,n a)))]))


(define (abs-interpret-action++ a s)
 (for/all ([a a])
;            [s s])
    (let ([b (abs-state->buf s)]
          [h (abs-state->heap s)])
      (match a
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
        [(abstract-model any)
         (abs-interpret-action+ a s)]))))


(define-language abstract-lang++
  #:grammar abstract-model
  #:expression state #:size 10
  #:context action #:size 3
  #:link cons
  #:evaluate (uncurry abs-interpret-action++))

(define-compiler abstract-to-heap-nd4
  #:source abstract-lang++
  #:target heap-lang-state+
  #:behavior-relation (bounded-equiv-state+ 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))


(define-compiler abstract-to-heap-nc4
  #:source abstract-lang++
  #:target heap-lang-state+
  #:behavior-relation (bounded-equiv-state+ 3)
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))

; this was already nothing on demo4 so I am confused :(
(define (demo5-w)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nd4 as*)))))


; copy 1 3...confused
(define (demo5-wnc)
  (display-weird-abstract-to-heap
   (with-abstract-schema (lambda (as*) (find-weird-behavior abstract-to-heap-nc4 as*)))))



(define test5buf (abstract-model (cons -1 (cons (P 0 a) (cons 5 (cons 4 nil))))))
(define test5heap (abstract-model (cons (N (P 0 a)) nil)))
(define test5state (abstract-model (,test5buf ,test5heap)))
(define test5state+ (abs-interpret-action (abstract-model (copy 1 3)) test5state))
(define compiled5state+ (make-state-struct (test-abs-into-heap-fl (list 0 -1) test5state+)))




