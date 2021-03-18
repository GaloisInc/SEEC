#lang seec


(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang.rkt"))
(require (file "freelist-lang.rkt"))
(require (file "heap-to-freelist-compiler.rkt"))

#| Heap model in SEEC (from heap-lang.rkt)

(define-grammar heap-model
  (pointer ::= natural null)
  (value ::= integer pointer)
  (buf ::= list<value>)
  (heap ::= list<value>) 
  (state ::= (buf heap pointer))
  (action ::= (set buf-loc nnvalue)
             (read heap-loc buf-loc)
             (write buf-loc heap-loc)
             (free heap-loc)
             (alloc buf-loc))
  (interaction ::= list<action>))
...

(define-language heap-lang
  #:grammar heap-model
  #:expression interaction #:size 3
  #:context state #:size 8
  #:link snoc
  #:evaluate (uncurry interpret-interaction))

|#

(define (show-state) (display-state d+3*))

#| Freelist model (from "freelist-lang.rkt")

(define-grammar freelist
  (action ::=
          (free natural) 
          alloc)
  (interaction ::= list<action>)
  (state ::= list<natural>))
...

(define-language freelist-lang
  #:grammar freelist
  #:expression interaction #:size 3
  #:context state #:size 3
  #:link snoc
  #:evaluate (uncurry freelist-interaction))

|#

(define (show-freelist) (displayln (compile-heap-to-freelist d+3*)))

#| Starting with a concrete state, we ask SEEC if it can find interactions 
  that make the heap model and the freelist view diverge |#
(define (demo1) (display-heap-to-freelist (find-changed-component heap-to-freelist #:source-context d+3*)))


#| It find (free 2) which is an instance of double-free. We can modify
   the implementation of free to make sure the block is allocated
   and big enough to be in the freelist |#
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

#| We ask SEEC again if it can find interactions where the heap model and the freelist view diverge |#
(define (demo2) (display-heap-to-freelist (find-changed-component heap-to-freelist+ #:source-context d+3*)))


#| It finds a write into the freelist. We can prevent this by modifying write to only accept 
   allocated locations |#
(define (valid-write loc h)
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
        (let* ([val (nth b bl)]
               [loc (heap-loc-addr hl)]
               [h+ (write h loc val)])
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
  #:context state #:size 9
  #:link snoc
  #:evaluate (uncurry interpret-interaction++))


(define-compiler heap-to-freelist++
  #:source heap-lang++
  #:target freelist-lang
  #:behavior-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:compile compile-interaction)

#| We can use SEEC to confirm there are no more changed behavior using this state under the freelist view |#
(define (demo3) (display-heap-to-freelist (find-changed-component heap-to-freelist++ #:source-context d+3*)))

#| We can then run the query again without specifying a concrete state. It find a broken freelist, but in a nonsensical state |#
(define (demo3+) (display-heap-to-freelist (find-changed-component heap-to-freelist++)))

#| We could look for states reachable using interactions from the initial state, but doesn't scale (exponential blowup) |#
(define (demo3++) (display-heap-to-freelist (find-changed-component heap-to-freelist++ #:source-expression-bound 5 #:source-context d)))

#| One alternative is to write predicate to restrict the starting states to valid ones |#
(define (demo3+++) (display-heap-to-freelist (find-changed-component heap-to-freelist++ #:source-context-where (lambda (v c) (valid-state-block c)))))

#| What may be more intuitive (the SEEC way) would be to write a higher-level model providing more structures to valid states, allowing us to synthesize states which are one step away from being exploited |#

