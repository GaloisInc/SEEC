#lang seec

(require seec/private/bonsai2)

(current-bitwidth 4)

(define-language set-api
  (value       ::= integer boolean)
  (list        ::= empty (value list))
  (method      ::= (insert integer) (remove integer) (member? integer) select)
  (interaction ::= empty (method interaction))
  (context     ::= empty ((insert integer) context) ((remove integer) context)))

(define (head s)
  (match s
    [(set-api empty)
     (assert #f)]
    [(set-api (v:value list))
     v]))

(define (tail s)
  (match s
    [(set-api empty)
     (assert #f)]
    [(set-api (value rest:list))
     rest]))

(define (abstract-insert s v)
  (set-api (,v ,(abstract-remove s v))))

(define (abstract-remove s v)
  (match s
    [(set-api empty) (set-api empty)]
    [(set-api (x:value r:list))
     (let ([new-tail (abstract-remove r v)])
       (if (equal? x v)
           new-tail
           (set-api (,x ,new-tail))))]))

(define (abstract-member? s v)
  (match s
    [(set-api empty) (set-api #f)]
    [(set-api (x:value r:list))
     (if (equal? x v)
         (set-api #t)
         (abstract-member? r v))]))

(define (abstract-select s)
  (match s
    [(set-api empty) (set-api #f)]
    [(set-api list)  (abstract-select-nondet s)]))

(define (abstract-select-nondet s)
  (match s
    [(set-api (x:value empty)) x]
    [(set-api (x:value r:list))
     (if (nondet!) x (abstract-select-nondet r))]))

(define (abstract-interpret interaction state)
  (match interaction
    [(set-api empty) (set-api empty)]
    [(set-api ((insert v:value) r:interaction))
     (abstract-interpret r (abstract-insert state v))]
    [(set-api ((remove v:value) r:interaction))
     (abstract-interpret r (abstract-remove state v))]
    [(set-api ((member? v:value) r:interaction))
     (set-api (,(abstract-member? state v) ,(abstract-interpret r state)))]
    [(set-api (select r:interaction))
     (set-api (,(abstract-select state) ,(abstract-interpret r state)))]))

(define (abstract-interpret-in-context context interaction state)
  (match context
    [(set-api empty) (abstract-interpret interaction state)]
    [(set-api ((insert v:value) r:interaction))
     (abstract-interpret-in-context r interaction (abstract-insert state v))]
    [(set-api ((remove v:value) r:interaction))
     (abstract-interpret-in-context r interaction (abstract-remove state v))]))

(define (concrete-insert s v)
  (set-api (,v ,s)))

(define (concrete-remove s v)
  (match s
    [(set-api empty) (set-api empty)]
    [(set-api (x:value r:list))
     (let ([new-tail (concrete-remove r v)])
       (if (equal? x v)
           new-tail
           (set-api (,x ,new-tail))))]))

(define (buggy-concrete-remove s v)
  (match s
    [(set-api empty) (set-api empty)]
    [(set-api (x:value r:list))
     (if (equal? x v)
         r
         (set-api (,x ,(buggy-concrete-remove r v))))]))

(define (concrete-member? s v)
  (match s
    [(set-api empty) (set-api #f)]
    [(set-api (x:value r:list))
     (if (equal? x v)
         (set-api #t)
         (concrete-member? r v))]))

(define (concrete-select s)
  (match s
    [(set-api empty) (set-api #f)]
    [(set-api (x:value list)) x]))

(define (concrete-interpret interaction state)
  (match interaction
    [(set-api empty) (set-api empty)]
    [(set-api ((insert v:value) r:interaction))
     (concrete-interpret r (concrete-insert state v))]
    [(set-api ((remove v:value) r:interaction))
     (concrete-interpret r (concrete-remove state v))]
    [(set-api ((member? v:value) r:interaction))
     (set-api (,(concrete-member? state v) ,(concrete-interpret r state)))]
    [(set-api (select r:interaction))
     (set-api (,(concrete-select state) ,(concrete-interpret r state)))]))

(define (concrete-interpret-in-context context interaction state)
  (match context
    [(set-api empty) (concrete-interpret interaction state)]
    [(set-api ((insert v:value) r:interaction))
     (concrete-interpret-in-context r interaction (concrete-insert state v))]
    [(set-api ((remove v:value) r:interaction))
     (concrete-interpret-in-context r interaction (concrete-remove state v))]))

(define (buggy-concrete-interpret interaction state)
  (match interaction
    [(set-api empty) (set-api empty)]
    [(set-api ((insert v:value) r:interaction))
     (buggy-concrete-interpret r (concrete-insert state v))]
    [(set-api ((remove v:value) r:interaction))
     (buggy-concrete-interpret r (buggy-concrete-remove state v))]
    [(set-api ((member? v:value) r:interaction))
     (set-api (,(concrete-member? state v) ,(buggy-concrete-interpret r state)))]
    [(set-api (select r:interaction))
     (set-api (,(concrete-select state) ,(buggy-concrete-interpret r state)))]))

(define (buggy-concrete-interpret-in-context context interaction state)
  (match context
    [(set-api empty) (buggy-concrete-interpret interaction state)]
    [(set-api ((insert v:value) r:interaction))
     (buggy-concrete-interpret-in-context r interaction (concrete-insert state v))]
    [(set-api ((remove v:value) r:interaction))
     (buggy-concrete-interpret-in-context r interaction (buggy-concrete-remove state v))]))

(define (valid-set? xs)
  (match xs
    [(set-api empty) #t]
    [(set-api (x:integer r:list))
     (match (concrete-member? r x)
       [(set-api #f) (valid-set? r)]
       [(set-api #t) #f])]
    [_ #f]))

(define (select-free? trace)
  (match trace
    [(set-api empty) #t]
    [(set-api (select r:interaction)) #f]
    [(set-api ((insert integer) r:interaction))
     (select-free? r)]
    [(set-api ((remove integer) r:interaction))
     (select-free? r)]
    [(set-api ((member? integer) r:interaction))
     (select-free? r)]))

(define (output-free? trace)
  (match trace
    [(set-api empty) #t]
    [(set-api ((insert integer) r:interaction))
     (output-free? r)]
    [(set-api ((remove integer) r:interaction))
     (output-free? r)]
    [_ #f]))

(define (compose t1 t2)
  (match t1
    [(set-api empty) t2]
    [(set-api (m:method r:interaction))
     (set-api (,m ,(compose r t2)))]))

#;
(define (trace-context-experiment buggy)
  (define test-interpret-in-context
    (if buggy
        buggy-concrete-interpret-in-context
        concrete-interpret-in-context))
  (displayln "Building trees...")
  (define trace (time (set-api interaction 5)))
  (define concrete-context (time (set-api context 5)))
  (define abstract-context (time (set-api context 5)))
  ;(define concrete-context (time (set-api interaction 5)))
  ;(time (assert (output-free? concrete-context)))
  ;(define abstract-context (time (set-api interaction 5)))
  ;(time (assert (output-free? abstract-context)))
  (displayln "Abstract interpretation...")
  (define abstract
    (time (abstract-interpret-in-context abstract-context trace (set-api empty))))
  (displayln "Concrete interpretation...")
  (define concrete
    (time (test-interpret-in-context concrete-context trace (set-api empty))))
  (displayln "Generating equality assertion...")
  (define equality-assertions (with-asserts-only (time (assert (equal? abstract concrete)))))
  (displayln "Solving for trace with different behavior...")
  (define sol
    (time (verify #:assume (assert (equal? concrete-context abstract-context))
                  #:guarantee (assert (apply && equality-assertions)))))
  (if (unsat? sol)
      (displayln "Synthesis failed")
      (begin
        (displayln "Found initial set with divergent traces...")
        (define trace-instance (concretize trace sol))
        (define concrete-context-instance (concretize concrete-context sol))
        (displayln trace-instance)
        (displayln concrete-context-instance)
        (printf "Abstract interpretation: ~a~n"
                (instantiate
                    (abstract-interpret-in-context
                     concrete-context-instance
                     trace-instance
                     (set-api empty))))
        (printf "Concrete interpretation: ~a~n"
                (instantiate
                    (test-interpret-in-context
                     concrete-context-instance
                     trace-instance
                     (set-api empty))))))
  #;(displayln "Solving for trace with different behavior under all contexts...")
  #;
  (define universal-sol
    (time (synthesize #:forall abstract-context
                      #:guarantee (assert (! (apply && equality-assertions))))))
  #;
  (if (unsat? universal-sol)
      (displayln "Synthesis failed")
      (begin
        (displayln "Found initial set with divergent traces...")
        (define trace-instance (concretize trace universal-sol))
        (define concrete-context-instance (concretize concrete-context universal-sol))
        (displayln trace-instance)
        (displayln concrete-context-instance)
        (printf "Abstract interpretation: ~a~n"
                (instantiate
                    (abstract-interpret-in-context
                     concrete-context-instance
                     trace-instance
                     (set-api empty))))
        (printf "Concrete interpretation: ~a~n"
                (instantiate
                    (test-interpret-in-context
                     concrete-context-instance
                     trace-instance
                     (set-api empty)))))))

(define (set-context-experiment buggy)
  (define test-interpret
    (if buggy
        buggy-concrete-interpret
        concrete-interpret))
  (displayln "Building symbolic interaction traces of size 6... ")
  (define trace (time (set-api interaction 6)))
  (displayln "Building symbolic initial set of size 2 for concrete execution...")
  (define concrete-set
    (time (let ([s (set-api list 2)])
            (assert (valid-set? s))
            s)))
  (displayln "Building symbolic initial set of size 2 for concrete execution...")
  (define abstract-set
    (time (let ([s (set-api list 2)])
            (assert (valid-set? s))
            s)))
  (newline)
  (displayln "Symbolically executing with the abstract implementation...")
  (define-values (abstract nondet)
    (capture-nondeterminism (time (abstract-interpret trace abstract-set))))
  (displayln "Symbolically executing with the concrete implementation...")
  (define concrete
    (time (test-interpret trace concrete-set)))
  (newline)
  (displayln "Generating equality assertion...")
  (define equality-assertions (with-asserts-only (time (assert (equal? abstract concrete)))))
  (newline)
  (displayln "Solving for trace with different behavior...")
  (define sol
    (time (verify #:assume (assert (equal? concrete-set abstract-set))
                  #:guarantee (assert (apply && equality-assertions)))))
  (if (unsat? sol)
      (displayln "Synthesis failed")
      (begin
        (displayln "Found initial set with divergent traces...")
        (define trace-instance (concretize trace sol))
        (define concrete-set-instance (concretize concrete-set sol))
        (displayln trace-instance)
        (displayln concrete-set-instance)
        (printf "Abstract interpretation: ~a~n"
                (instantiate
                    (abstract-interpret
                     trace-instance
                     concrete-set-instance)))
        (printf "Concrete interpretation: ~a~n"
                (instantiate
                    (test-interpret
                     trace-instance
                     concrete-set-instance)))))
  (newline)
  (displayln "Solving for trace with different behavior under all contexts...")
  (define universal-sol
    (time (synthesize #:forall (cons abstract-set nondet)
                      #:guarantee (assert (! (apply && equality-assertions))))))
  (if (unsat? universal-sol)
      (displayln "Synthesis failed")
      (begin
        (displayln "Found initial set with divergent traces...")
        (define trace-instance (concretize trace universal-sol))
        (define concrete-set-instance (concretize concrete-set universal-sol))
        (displayln trace-instance)
        (displayln concrete-set-instance)
        (printf "Abstract interpretation: ~a~n"
                (instantiate
                    (abstract-interpret
                     trace-instance
                     concrete-set-instance)))
        (printf "Concrete interpretation: ~a~n"
                (instantiate
                    (test-interpret
                     trace-instance
                     concrete-set-instance)))))
  (newline))

(displayln "Experiment with incorrect concrete interpretation...")
(set-context-experiment #t)
(displayln "Experiment with correct concrete interpretation...")
(set-context-experiment #f)
