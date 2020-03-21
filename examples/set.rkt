#lang seec

(require seec/private/bonsai2)

(define-language set-api
  (value       ::= integer boolean)
  (list        ::= empty (value list))
  (method      ::= (insert integer) (remove integer) (member? integer) select)
  (interaction ::= empty (method interaction)))

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
     (if (havoc!) x (abstract-select-nondet r))]))

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

(define (valid-set? xs)
  (match xs
    [(set-api empty) #t]
    [(set-api (x:integer r:list))
     (match (concrete-member? r x)
       [(set-api #f) (valid-set? r)]
       [(set-api #t) #f])]
    [_ #f]))

(displayln "Building trees...")
(define trace (time (set-api interaction 5)))
(define initial-set (time (set-api list 5)))
(time (assert (valid-set? initial-set)))
(displayln "Abstract interpretation...")
(define abstract (time (abstract-interpret trace initial-set)))
(displayln "Concrete interpretation...")
(define concrete (time (concrete-interpret trace initial-set)))
(displayln "Solving...")
(define sol
  #;(time (verify (assert (equal? abstract concrete))))
  (time (optimize #:minimize (list (bonsai-leaves trace))
                  #:guarantee (assert (! (equal? abstract concrete))))))
(displayln "Found initial set with divergent traces...")
(define trace-instance (concretize trace sol))
(define set-instance (concretize initial-set sol))
(displayln trace-instance)
(displayln set-instance)
(printf "Abstract interpretation: ~a~n"
        (instantiate (abstract-interpret trace-instance set-instance)))
(printf "Concrete interpretation: ~a~n"
        (instantiate (concrete-interpret trace-instance set-instance)))
