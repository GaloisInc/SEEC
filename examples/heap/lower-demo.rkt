#lang seec


(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang-hl.rkt"))
(require (file "heap-abstract-lang-hl.rkt"))
(require (file "freelist-lang.rkt"))
(require (file "abstract-to-heap-hl-compiler.rkt"))
(require (file "heap-to-freelist-compiler.rkt"))




(define (demo1)
      (display-heap-to-freelist
       (with-heap-schema (lambda (s*) (find-changed-behavior heap-to-freelist s*)))))


(define (valid-free loc h)
  (let* ([v-bit (nth (- loc 2) h)]
         [s-bit (nth (- loc 1) h)])
    (if (and (equal? v-bit 1)
             (< 1 s-bit))
        #t
        #f)))


(define (interpret-action+ a s)
  (let ([b (state->buf s)]
        [h (state->heap s)]
        [f (state->pointer s)])
    (match a
      [(heap-model (free p:heap-loc))
       (if (valid-free p h)
           (make-state b (interpret-free h f p) p)
           (assert #f))]       
      [_ (interpret-action a s)])))

(define (interpret-interaction+ i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction+ i+ (interpret-action+ a s))]
    [(heap-model nil)
     s]))


(define-language heap-state-lang+
  #:grammar heap-model
  #:expression state-con #:size 10
  #:context interaction #:size 3
  #:link heap-lang-link-state
  #:evaluate (uncurry interpret-interaction+))


(define-compiler heap-to-freelist+
  #:source heap-state-lang+
  #:target freelist-lang
  #:behavior-relation
  (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation (lambda (i fi) (equal? (compile-interaction i) fi))
  #:compile (lambda (s) (compile-heap-to-freelist (make-state-struct s))))

(define (demo2)
      (display-heap-to-freelist
       (with-heap-schema (lambda (s*) (find-changed-behavior heap-to-freelist+ s*)))))



(define (valid-write loc h)
  (let* ([loc-v (- (+ loc 3) (remainder loc 4))]
         [v-bit (nth loc-v h)])
    (if (equal? v-bit (heap-model 1))
        #t
        #f)))


(define (interpret-action++ a s)
  (let ([b (state->buf s)]
        [h (state->heap s)]
        [f (state->pointer s)])
    (match a
      [(heap-model (write bl:buf-loc hl:heap-loc))
       (let* ([val (nth b bl)]
              [loc (heap-loc-addr hl)]
              [h+ (write h loc val)])
         (if (valid-write loc h)
             (make-state b h+ f)
             (assert #f)))]
      [_ (interpret-action+ a s)])))



(define (interpret-interaction++ i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction++ i+ (interpret-action++ a s))]
    [(heap-model nil)
     s]))

(define-language heap-state-lang++
  #:grammar heap-model
  #:expression state-con #:size 10
  #:context interaction #:size 3
  #:link heap-lang-link-state
  #:evaluate (uncurry interpret-interaction++))


(define-compiler heap-to-freelist++
  #:source heap-state-lang++
  #:target freelist-lang
  #:behavior-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation (lambda (i fi) (equal? (compile-interaction i) fi))
  #:compile (lambda (s) (compile-heap-to-freelist (make-state-struct s))))

(define (demo3)
      (display-heap-to-freelist
       (with-heap-schema (lambda (s*) (find-changed-behavior heap-to-freelist++ s*)))))

;
(define ademobuf (abstract-model (cons (P 0 b) (cons -1 (cons 0 (cons 1 nil))))))
(define ademoheap (abstract-model (cons (1 2) nil)))
(define ademostate (abstract-model (,ademobuf ,ademoheap)))

(define demoperm (list 0 #f))

(define pdemostate (test-abs-into-heap-fl demoperm ademostate))
(define demostate (make-state-struct pdemostate))
(define demofreelist (compile-heap-to-freelist demostate))

(define demoattack (heap-model (cons (free 4) nil)))
(define demostate+ (interpret-interaction demoattack demostate))

(define-language heap-state-lang+++
  #:grammar heap-model
  #:expression state-con #:size 10
  #:context interaction #:size 4
  #:link heap-lang-link-state
  #:evaluate (uncurry interpret-interaction++))

(define-compiler heap-to-freelist+++
  #:source heap-state-lang+++
  #:target freelist-lang
  #:behavior-relation (lambda (s f) (and (equal? (compile-heap-to-freelist s) f)
                                         (valid-heap? (state->heap s))))
  #:context-relation (lambda (i fi) (equal? (compile-interaction i) fi))
  #:compile (lambda (s) (compile-heap-to-freelist (make-state-struct s))))

(define (demo4)
      (display-heap-to-freelist
       (with-heap-schema (lambda (s*) (find-changed-behavior heap-to-freelist+++ s*)))))
