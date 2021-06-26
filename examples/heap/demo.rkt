#lang seec


(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang-hl.rkt"))
(require (file "freelist-lang.rkt"))
(require (file "heap-to-freelist-compiler.rkt"))


(define (show-state) (display-state d+3*))


(define (show-freelist) (displayln (compile-heap-to-freelist d+3*)))


(define (demo1) (display-heap-to-freelist
                 (find-changed-component heap-to-freelist
                                         #:source-expression (make-state-con d+3*))))

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


(define-language heap-lang+
  #:grammar heap-model
  #:expression interaction #:size 4
  #:context state-con #:size 10
  #:link (lambda (state inte)
           (match state
             [(heap-model (b:buf h:heap p:pointer))
              (cons inte (make-state b h p))]))
  #:evaluate (uncurry interpret-interaction+))


(define-compiler heap-to-freelist+
  #:source heap-lang+
  #:target freelist-lang
  #:behavior-relation
  (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation
  (lambda (s f) (equal? (compile-heap-to-freelist (make-state-struct s)) f))
  #:compile compile-interaction)

(define (demo2) (display-heap-to-freelist
                 (find-changed-component heap-to-freelist+
                                         #:source-expression (make-state-con d+3*))))


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

(define-language heap-lang++
  #:grammar heap-model
  #:expression interaction #:size 4
  #:context state-con #:size 10
  #:link (lambda (state inte)
           (match state
             [(heap-model (b:buf h:heap p:pointer))
              (cons inte (make-state b h p))]))
  #:evaluate (uncurry interpret-interaction++))


(define-compiler heap-to-freelist++
  #:source heap-lang++
  #:target freelist-lang
  #:behavior-relation
  (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation
  (lambda (s f) (equal? (compile-heap-to-freelist (make-state-struct s)) f))
  #:compile compile-interaction)

(define (demo3) (display-heap-to-freelist
                 (find-changed-component heap-to-freelist++
                                         #:source-expression (make-state-con d+3*))))

(define (demo3+) (display-heap-to-freelist
                  (find-changed-component heap-to-freelist++)))

(define (show-initial)
  (display-state d))

(define (demo3++) (display-heap-to-freelist
                   (find-changed-component heap-to-freelist++
                                           #:source-context-size 5
                                           #:source-expression (make-state-con d))))


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
        (valid-heap-block-size h)]))


(define (demo3+++) (display-heap-to-freelist
                    (find-changed-component heap-to-freelist++
                                            #:source-expression-where
                                            (lambda (v c) (valid-state-block c)))))


