#lang seec
;; Abstract -> Heap -> Freelist
;; May be renamed demo, as compilation is just chaining abstract-to-heap and heap-to-freelist 
;; TODO : will need to bridge together w/o using hl (or using hl all the way)
(require racket/format)
(require seec/private/util)
(require seec/private/monad)

(require (file "lib.rkt"))
(require (file "heap-lang-hl.rkt"))
(require (file "heap-abstract-lang-hl.rkt"))
(require (file "freelist-lang.rkt"))
(require (file "heap-to-freelist-compiler.rkt"))
(require (file "abstract-to-heap-hl-compiler.rkt"))


; Compile to heap-hl
(define (manual-full-test0)
  (begin
    (define ab0 (abstract-model value 1))
    (define ab1 (abstract-model value 1))
    (define ab2 (abstract-model value 1))
    (define ab3 (abstract-model value 1))
    (define ab* (abstract-model (cons ,ab0 (cons ,ab1 (cons ,ab2 (cons ,ab3 nil))))))
    (define ablock (abstract-model block 3))
    (define ah* (abstract-model (cons ,ablock nil)))
    (define as* (abstract-model (,ab* ,ah*)))
    (let*-values
        ([(p* nondet*) (capture-nondeterminism #:nondet #t (generate-permutation-fl 2 1))])
      (define s* (make-state-struct (test-abs-into-heap-fl p* as*)))
      (define ai* (abstract-model action 3))
      (define as+* (abs-interpret-action ai* as*))
      (define i* (compile-abs-action ai* p*))
      (define s+* (interpret-action i* s*))
      (define sol (verify (assert ((bounded-equiv-state 3) as+* s+*))))
      (if (unsat? sol)
          (displayln "unsat")
          (begin
            (displayln "sat")
            (define as (concretize as* sol))
            (define ai (concretize ai* sol))
            (define i (concretize i* sol))
            (define s (concretize s* sol))
            (define s+ (interpret-action i s))
            (define as+ (abs-interpret-action i as))
            (displayln "Over state")
            (display-abs-state as)
            (displayln "compiled as state")
            (display-state s)
            (display "Action ")
            (displayln ai)
            (displayln i)
            (displayln "Results in abstract.state :")
            (display-abs-state as+)
            (displayln "and heap.state :")
            (display-state s+)
            (displayln "which are equivalent?")
            (displayln ((bounded-equiv-state 3) as+ s+)))))))



; Compile all the way to freelist
(define (manual-full-test1)
  (begin
    (define ab0 (abstract-model value 1))
    (define ab1 (abstract-model value 1))
    (define ab2 (abstract-model value 1))
    (define ab3 (abstract-model value 1))
    (define ab* (abstract-model (cons ,ab0 (cons ,ab1 (cons ,ab2 (cons ,ab3 nil))))))
    (define ablock (abstract-model block 3))
    (define ah* (abstract-model (cons ,ablock nil)))
    (define as* (abstract-model (,ab* ,ah*)))
        (let*-values ; Note: I don't need the p later since we only care about the actions over heap.state, and use abstract to restrict the space of states
        ([(p* nondet*) (capture-nondeterminism #:nondet #t (generate-permutation-fl 2 1))])
          (define s* (make-state-struct (test-abs-into-heap-fl p* as*)))
          (define fl* (compile-heap-to-freelist s*))
          (define ai* (abstract-model interaction 3))
          ;(define as+* (abs-interpret-interaction ai* as*))
          (define i* (heap-model interaction 3)) ; (compile-abs-action ai* p*))
          (define s+* (interpret-interaction i* s*))
          (define fi* (compile-interaction i*))
          (define fl+* (freelist-interaction fi* fl*))      
          (define sol (verify (assert (equal? (compile-heap-to-freelist s+*) fl+*))))
          (if (unsat? sol)
              (displayln "unsat")
              (begin
                (displayln "sat")
                (define as (concretize as* sol))
                (define i (concretize i* sol))
                (define fi (concretize fi* sol))
                (define s (concretize s* sol))
                (define s+ (interpret-interaction i s))
                (define fl (concretize fl* sol))
                (define fl+ (freelist-interaction fi fl))
                (displayln "Over state")
                (display-abs-state as)
                (displayln "compiled as state")
                (display-state s)
                (displayln "with freelist")
                (displayln fl)
                (display "Action ")
                (displayln i)
                (displayln "Results in heap.state :")
                (display-state s+)
                (displayln "and free list :")
                (displayln fl+))))))

(define (semi-manual-test1)
  (define as* (make-symbolic-abstract-state))
  (define-values (perm* nondet*) (capture-nondeterminism #:nondet #t (generate-permutation-fl 2 1)))
  (define s* (test-abs-into-heap-fl perm* (car as*)))
  (define fl* (compile-heap-to-freelist (make-state-struct s*))) ; #compile
  (define i* (heap-model interaction 3)) ; #context
  (define p* (heap-lang-link-state i* s*))
  (define s+* ((uncurry interpret-interaction) p*))
  (define fi* (freelist interaction 3))
  (assert (equal? fi* (compile-interaction i*)))
  (define fl+* ((uncurry freelist-interaction) (cons fi* fl*)))
  (define sol (verify (assert (equal? (compile-heap-to-freelist s+*) fl+*))))
  (if (unsat? sol)
    (displayln "unsat")
    (displayln "sat")))

#|
         [source           (compiler-source comp)]  heap-lang-state
         [target           (compiler-target comp)] freelist-lang
         [e2               ((compiler-compile comp) e1)] (lambda s (compile-heap-to-freelist (make-state-struct s)))) e1
         [p1               ((language-link source) c1 e1)] 
         [p2               ((language-link target) c2 e2)]
         [context-relation (compiler-context-relation comp)] (lambda (i fi) (equal? (compile-interaction i) fi)) c1 c2
         [ccomp            (if context-relation
                               (context-relation c1 c2)
                               #t)])
|#

; manual-test1 using the query
(define (aftest)
  (let* ([as* (make-symbolic-abstract-state)])
    (let*-values ([(p* nondet*) (capture-nondeterminism #:nondet #t (generate-permutation-fl 2 1))])
      (define s* (test-abs-into-heap-fl p* (car as*)))
      (display-heap-to-freelist
       (find-changed-behavior heap-to-freelist s*)))))


(define (aftest-wh)
      (display-heap-to-freelist
       (with-heap-schema (lambda (s*) (find-changed-behavior heap-to-freelist s*)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (display-abstract-to-freelist witnesses)
  (if witnesses     
      (let* ([lwl-abstract (unpack-language-witness (first witnesses))]
             [lwl-freelist (unpack-language-witness (second witnesses))])
        (displayln "State: ")
        (display-abs-state (first lwl-abstract))
        (displayln "... can have freelist:")
        (displayln (first lwl-freelist))
        (display "... and steps, under interaction ")
        (display (second lwl-abstract))
        (displayln ", to state: ")
        (display-abs-state (fourth lwl-abstract))
        (displayln "... with emergent behavior: ")
        (displayln (fourth lwl-freelist)))
      (displayln "No changed behavior found")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Full compiler
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(compose-compiler fixedperm-full-compiler
                  #:upper small-fixed-permutation-to-heap
                  #:lower heap-to-freelist)


(compose-compiler full-compiler
                  #:upper abstract-to-heap
                  #:lower heap-to-freelist)



(define (fpftest0)
  (display-abstract-to-freelist
       (find-changed-behavior fixedperm-full-compiler asmallstate)))

(define (fpftest1)
  (display-abstract-to-freelist
       (find-changed-component fixedperm-full-compiler)))

(define (fulltest0)
  (display-abstract-to-freelist
       (find-changed-behavior full-compiler asmallstate)))

(define (fulltest1)
  (display-abstract-to-freelist
       (find-changed-component full-compiler)))
