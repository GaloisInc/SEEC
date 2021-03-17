#lang seec


(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang.rkt"))
(require (file "freelist-lang.rkt"))
(require (file "heap-to-freelist-compiler.rkt"))


(define (demo1) (display-heap-to-freelist (find-changed-component heap-to-freelist #:source-context d+3*)))


; Makes sure the block is allocated and big enough to be in the freelist
(define (valid-free loc h)
  (let* ([v-bit (nth (- loc 2) h)]
         [s-bit (nth (- loc 1) h)])
    (if (and (equal? v-bit 1)
             (< 1 s-bit))
        #t
        #f)))

(define (interpret-action+ a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     (match a
       [(heap-model (free p:heap-loc))
        (if (valid-free p h)
            (heap-model (,b ,(interpret-free h f p) ,p))
            (assert #f))]       
       [_ (interpret-action a s)])]))

(define (interpret-interaction+ i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction+ i+ (interpret-action+ a s))]
    [(heap-model nil)
     s]))

(define-language heap-lang+
  #:grammar heap-model
  #:expression interaction #:size 3
  #:context state #:size 8
  #:link snoc
  #:evaluate (uncurry interpret-interaction+))


(define-compiler heap-to-freelist+
  #:source heap-lang+
  #:target freelist-lang
  #:behavior-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:compile compile-interaction)

(define (demo2) (display-heap-to-freelist (find-changed-component heap-to-freelist+ #:source-context d+3*)))



;; Check that write is performed in the payload of an allocated block
(define (valid-write loc h)
  ; compute the location of the "allocated" bit
  (let* ([loc-v (- (+ loc 3) (remainder loc 4))]
         [v-bit (nth loc-v h)])
    (if (equal? v-bit (heap-model 1))
        #t
        #f)))


(define (interpret-action++ a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     (match a
              [(heap-model (write bl:buf-loc hl:heap-loc))
        (do val <- (nth b bl) ; get the value from the buffer
            loc <- (heap-loc-addr hl) ; compute the address in the heap
            h+ <- (write h loc val) ; overwrite the location in the heap with the value
          (if (valid-write loc h)
              (heap-model (,b ,h+ ,f))
              (assert #f)))]
       [_ (interpret-action+ a s)])]))



(define (interpret-interaction++ i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction++ i+ (interpret-action++ a s))]
    [(heap-model nil)
     s]))

(define-language heap-lang++
  #:grammar heap-model
  #:expression interaction #:size 3
  #:context state #:size 8
  #:link snoc
  #:evaluate (uncurry interpret-interaction++))


(define-compiler heap-to-freelist++
  #:source heap-lang++
  #:target freelist-lang
  #:behavior-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:compile compile-interaction)

(define (demo3) (display-heap-to-freelist (find-changed-component heap-to-freelist++ #:source-context d+3*)))



(define (demo3+) (display-heap-to-freelist (find-changed-component heap-to-freelist++)))


(define (demo3++) (display-heap-to-freelist (find-changed-component heap-to-freelist++ #:source-context-where (lambda (v c) (valid-state-block c)))))
