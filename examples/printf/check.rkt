#lang seec
(require (file "syntax.rkt"))
(require (only-in seec/private/bonsai2
                  bonsai-pretty
                  ))

(define (test-lookup-offset)
  (displayln "Testing lookup-offset...")
  (define-symbolic* offset integer?)
  (define args (printf-lang arglist 5))
  (assert (< offset (bonsai-ll-length args)))
  (define sol
    (verify (val? (lookup-offset offset args))))
  (if (unsat? sol)
      (displayln "Verified.")
      (begin
        (displayln "Counterexample found.")
        (displayln "Offset...")
        (concretize offset sol)
        (displayln "Arglist...")
        (concretize args sol)
        ))
)


(define (test-mem-update)
  (displayln "Testing mem-update")
  (define m (printf-lang mem 5))
  (define l (printf-lang ident 1))
  (define v (printf-lang val 1))
  (assert (mem? m))
  (define sol (verify (mem? (mem-update m l v))))
  (if (unsat? sol)
      (displayln "Verified")
      (displayln "Counterexample found.")))


(define (test-interp-fmt-safe)
  (displayln "Testing interp-fmt-safe")
  (displayln "NOTE: times out when increasing size of f beyond 2")
  (define f (printf-lang fmt 2))
  (define args (printf-lang arglist 4))
  (define conf (printf-lang config 4))
  (assert (fmt-consistent-with-arglist? f args))
  (define sol (verify (match (interp-fmt-safe f args conf)
                        [(printf-lang (trace conf+:config)) (conf? conf+)]
                        )))
  (if (unsat? sol)
      (displayln "Verified")
      (begin
        (displayln "Counterexample found.")
        (displayln "fmt...")
        (define f-instance (concretize f sol))
        (displayln f-instance)
        (displayln "args...")
        (define args-instance (concretize args sol))
        (displayln args-instance)
        (displayln "conf...")
        (define conf-instance (concretize conf sol))
        (displayln conf-instance)
        (define res-instance (interp-fmt-safe f-instance args-instance conf-instance))
        (displayln res-instance)
        )))


(define (test-interp-fmt-unsafe)
  (displayln "Testing interp-fmt-unsafe")
  (displayln "NOTE: times out when increasing size of arglist beyond 2")
  (define f (printf-lang fmt 2))
  (define args (printf-lang arglist 4))
  (define conf (printf-lang config 5))
  #;(assert (fmt-consistent-with-arglist? f args))
  (define guarantee
    (match (interp-fmt-unsafe f args conf)
      [(printf-lang (trace conf+:config)) (conf? conf+)]
      [_ #f]))
  (define sol (verify
               #:guarantee guarantee
               ))
  (if (unsat? sol)
      (displayln "Verified")
      (begin
        (displayln "Counterexample found.")
        (displayln "fmt...")
        (define f-instance (concretize f sol))
        (displayln f-instance)
        (displayln "args...")
        (define args-instance (concretize args sol))
        (displayln args-instance)
        (displayln "conf...")
        (define conf-instance (concretize conf sol))
        (displayln conf-instance)
        (define res-instance (interp-fmt-unsafe f-instance args-instance conf-instance))
        (displayln res-instance)
        (conf? (behavior->config res-instance))
        )))

(define (find-exploit)
  (define f (printf-lang fmt 5))
  ;(assert (equal? f (printf-lang (cons (% (0 $) NONE d) nil))))
  (define args (printf-lang arglist 2))
  ;(assert (equal? args (printf-lang nil)))
  (define conf (printf-lang config 5))
  (displayln "Searching for a format string that evaluates in the target but not in the source")
  (displayln "NOTE: times out when increasing size of arglist beyond 2")
  (define conf+ (behavior->config (interp-fmt-unsafe f args conf)))
  (define sol (synthesize
               #:forall '()
               #:guarantee (assert (and (not (fmt-consistent-with-arglist? f args))
                                        (conf? conf+)))))
  #;(define sol (verify #:assume (assert (conf? conf+))
                      #:guarantee (assert (fmt-consistent-with-arglist? f args))
                      ))
  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded.")
        (displayln "fmt...")
        (define f-instance (concretize f sol))
        (displayln f-instance)
        (displayln "args...")
        (define args-instance (concretize args sol))
        (displayln args-instance)
        (displayln "conf...")
        (define conf-instance (concretize conf sol))
        (displayln conf-instance)
        (define res-instance (interp-fmt-unsafe f-instance args-instance conf-instance))
        (displayln res-instance)
        (displayln (fmt-consistent-with-arglist? f-instance args-instance))
        )))


(define (is-constant-add f c args conf)
  (let* ([conf+ (behavior->config (interp-fmt-safe f args conf))]
         [acc   (conf->acc conf)]
         [acc+  (conf->acc conf+)]
        )
    (equal? acc+ (+ c acc))
    ))
(define (is-constant-add-positive f c args conf)
  (let* ([conf+ (behavior->config (interp-fmt-safe f args conf))]
         [acc   (conf->acc conf)]
         [acc+  (conf->acc conf+)]
        )
    (equal? acc+ (+ (max c 0) acc))
    ))


; a refinement of is-constant-add where the result is the max of (acc+c) and (acc+length(c))
(define (is-constant-add-max f c args conf)
  #;(printf "(is-constant-add-max ~a ~a ~a ~a)~n" f c args conf)
  (let* ([b+ (interp-fmt-safe f args conf)]
         [conf+ (behavior->config b+)]
         [acc   (conf->acc conf)]
         [acc+  (conf->acc conf+)]
         [c-length (string-length (number->string c))]
        )
    (equal? acc+ (+ acc (max c c-length)))
    #;(equal? (conf->acc conf+) (+ c (conf->acc conf)))
    ))



(define (demo-add-constant)
  (define f (printf-lang (cons "x" nil)))
  (displayln f)
  #;(define f (printf-lang (cons (% (0 $) d) nil)))
  (displayln (fmt? f))
  (define args (printf-lang (cons 100 nil)))
  (displayln args)
  (displayln (arglist? args))
  (define conf (printf-lang (-5 mnil)))
  (displayln conf)
  (displayln (conf? conf))
  (define exec (interp-fmt-safe f args conf))
  (displayln "==")
  #;(match exec
    [(list s+ conf+) (equal? (+ 1 (conf->acc conf)) (conf->acc conf+))])
  (is-constant-add f 1 args conf)
  )


#;(define (synthesize-string)
  (define s (new-symbolic-string 2))
  (define sol (verify (assert (not (equal? s (string "x"))))))
  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded")
        #;(define s-instance (concretize s sol))
        #;(printf "s: ~a~n" s-instance)
        ))
  )
#;(synthesize-string)



(define (find-add-constant)
  (define f (printf-lang fmt 3))
  ;(assert (equal? f (printf-lang (cons "x" nil))))
  (define acc0 (printf-lang integer 1))
  (define conf (printf-lang (,acc0 mnil)))
            
  (define args (printf-lang nil))


  (displayln "")
  (displayln "Searching for a format string that adds 1 to the accumulator")
  (define sol (synthesize
               #:forall acc0
               #:assume (assert (fmt-consistent-with-arglist? f args))
               #:guarantee (assert (is-constant-add-positive f 1 args conf))))
  (displayln "")
  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded.")
        (displayln "f...")
        (define f-instance (concretize f sol))
        (displayln (bonsai-pretty f-instance))
        (define acc0-instance (bonsai-integer 20) #;(concretize acc0 sol))
        (displayln "acc0...")
        (displayln acc0-instance)
        (define conf-instance (printf-lang (,acc0-instance mnil)))
        (displayln "conf before...")
        (displayln conf-instance)

        (displayln "conf after...")
        (displayln (behavior->config (interp-fmt-safe f-instance args conf-instance)))
        ))
  )

(define (max-int)
  ; subtract exponent by 1 because of signed integers
  (- (expt 2 (- (current-bitwidth) 1)) 1)
  )
(define (min-int)
  (* -1 (max-int)))

(define (test-quantifier)
  (current-bitwidth 5)
  (define-symbolic x integer?)
  (define sol (synthesize
               #:forall x
               #:guarantee (<= (min-int) x (max-int))))
  sol
  )


(define (find-add-argument-max)

  (current-bitwidth 16)
  (define f-concrete (printf-lang (cons (% (0 $) (* 0) d) nil)))
  (define f (printf-lang fmt 5))
  #;(define f f-concrete)
  #;(assert (equal? f f-concrete))

  (define-symbolic* acc0-val integer?)
  #;(define acc0-val 0)
  (define acc0 (printf-lang ,(bonsai-integer acc0-val)))
  (define conf (printf-lang (,acc0 mnil)))


  ;; NOTE: synthesis succeeds if x is defined to be the concrete value 16, but
  ;; not if we assert x = 16 and add a forall quantifier over x. Maybe add the
  ;; assertions to the query instead of the context?

  (define-symbolic x-val integer?)
  (printf "min-int: ~a ~n max-int: ~a~n" (min-int) (max-int))
  (define x (printf-lang ,(bonsai-integer x-val)))
  (define args (printf-lang (cons ,x nil)))

  #;(define result (interp-fmt-safe f args conf))
  #;(printf "Defined result: ~a~n" result)
  #;(printf "(is-constant-add f x args conf): ~a~n"
          (is-constant-add-max f x-val args conf))


  (displayln "Searching for a format string that adds the value of x to the accumulator")
  ; doesn't work when I quantify over x-val...
  (define sol (time (synthesize
                     #:forall (list acc0-val x-val)
                     #:guarantee (assert (is-constant-add-max f x-val args conf))
               )))
  ; use this query to find a counter-example
  #;(define sol (time (optimize
               #:minimize (list x-val)
               #:guarantee (assert (not (is-constant-add-max f x-val args conf)))
               )))


  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded.")
        (define f-instance (concretize f sol))
        (printf "f: ~a~n" f-instance)
        (define acc0-instance #;(bonsai-integer 0) (concretize acc0 sol))
        (printf "acc0 instance: ~a~n" acc0-instance)
        (define conf-instance (printf-lang (,acc0-instance mnil)))
        (define x-instance #;(bonsai-integer -1) (concretize x sol))
        (printf "x instance: ~a~n" x-instance)
        (define args-instance (printf-lang (cons ,x-instance nil)))

        (define result (interp-fmt-safe f-instance args-instance conf-instance))
        (define t (behavior->trace result))
        (define conf+ (behavior->config result))
        (printf "result: (~a ~a)~n" t conf+)

        (printf "(is-constant-add-max ~a ~a ~a ~a): ~a~n"
                f-instance
                x-instance
                args-instance
                conf-instance
                (is-constant-add-max f-instance (bonsai->number x-instance) args-instance conf-instance))
        ))
  )

(define (find-add-argument)

  (current-bitwidth 5)
  (define f-concrete (printf-lang (cons (% (0 $) (* 1) s) nil)))
  (define f (printf-lang fmt 5))
  #;(define f f-concrete)
  #;(assert (equal? f f-concrete))

  (define-symbolic* acc0-val integer?)
  #;(define acc0-val 0)
  #;(define acc0 (bonsai-integer acc0-val))
  (define conf (printf-lang config 2))
  (define acc0 (match conf 
                 [(printf-lang (acc:integer mem)) acc]))
  #;(define acc0 (printf-lang integer 1))
  (assert (equal? acc0-val (match acc0
                             [(printf-lang x:integer) (bonsai->number x)])))
  #;(assert (equal? acc0-val (bonsai->number acc0)))
  #;(define acc0-val (match acc0
                     [(printf-lang x:integer) (bonsai->number x)]))
  #;(printf "acc0: ~a [~a]~n" acc0 (symbolics acc0))
  #;(define conf (printf-lang (,acc0 mnil)))


  ; this will terminate because it is structurally decreasing on the length of
  ; args, which is finite
  (define (args-contains-x args x)
    (match args
      [(printf-lang nil) #f]
      [(printf-lang (cons y:any args+:arglist))
       (or (and (bonsai-integer? y)
                (equal? x (bonsai->number y)))
           (args-contains-x args+ x))]
      ))

  ; x is the amount to add to the accumulator
  (define-symbolic x-val integer?)
  #;(define x (printf-lang ,(bonsai-integer x-val)))
  #;(define x (printf-lang integer 1))
  #;(assert (equal? x-val (bonsai->number x)))
  #;(define args-concrete (ll-cons x (ll-singleton (printf-lang "") )))
  #;(define args args-concrete)

  (define args (printf-lang arglist 3))
  (define args+ (printf-lang arglist 2))
  (assert (equal? args (ll-cons (bonsai-integer x-val) args+)))
  #;(match args
            [(printf-lang (cons v:val arglist))
             (assert (equal? (bonsai-integer x-val) v))]
            [(printf-lang nil) (assert #f)]
            )

  #;(assert (equal? args args-concrete))
  #;(assert (match args
            [(printf-lang (cons y:integer (cons s:string nil)))
             (and (equal? x-val (bonsai->number y)))]
            ))


  (define result (interp-fmt-safe f args conf))
  #;(printf "Defined result: ~a~n" result)
  #;(printf "(is-constant-add-positive f x args conf): ~a~n"
          (is-constant-add-positive f x-val args conf))


  (displayln "Searching for a format string that adds the value of x to the accumulator")
  (define sol (time (synthesize
                     #:forall (list acc0-val x-val) #;(append (symbolics acc0) (symbolics x))
                     #:guarantee (assert (is-constant-add-positive f x-val args conf))
               )))
  ; use this query to find a counter-example
  #;(define sol (time (optimize
               #:minimize (list x-val)
               #:guarantee (assert (not (is-constant-add-positive f x-val args conf)))
               )))


  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded.")
        #;(define results (complete-solution sol (append (symbolics f)
                                                       (symbolics args)
                                                       (symbolics conf))))
        (define sol+ (expand-solution sol (list x-val acc0-val)))
        #;(define sol+ (complete-solution (complete-solution sol (symbolics x-val)) (symbolics acc0)))
        (printf "sol+: ~a~n" (sat? sol+))
                                              
        (define acc0-instance #;(bonsai-integer 0)
          (concretize+ acc0 sol+)
          #;(rosette/evaluate acc0 sol+))
        (printf "acc0 instance: ~a~n" acc0-instance)

        (define f-instance (concretize+ f sol+) #;(rosette/evaluate f sol+))
        (printf "f: ~a~n" f-instance)
        
        (define conf-instance (printf-lang (,acc0-instance mnil)))
        (define args-instance (concretize+ args sol+) #;(rosette/evaluate args sol+))
        (define x-instance (match args-instance
                  [(printf-lang (cons x:integer arglist)) (bonsai->number x)]))

        (printf "x instance: ~a~n" x-instance)
        #;(define args+-instance (concretize args+ sol))
        #;(define args-instance (printf-lang (cons ,x-instance ,args+-instance)))
        #;(define args-instance (concretize args sol))
        (printf "args instance: ~a~n" args-instance)

        (define result (interp-fmt-safe f-instance args-instance conf-instance))
        (define t (behavior->trace result))
        (define conf+ (behavior->config result))
        (printf "result: (~a ~a)~n" t conf+)

        (printf "(is-constant-add-positive ~a ~a ~a ~a): ~a~n"
                f-instance
                x-instance
                args-instance
                conf-instance
                (is-constant-add-positive f-instance x-instance args-instance conf-instance))
        ))


  )



;; (test-lookup-offset)
;; (displayln "")
;; (test-mem-update)
;; (displayln "")
;; (test-interp-fmt-safe)
;; (displayln "")
;; (test-interp-fmt-unsafe)
;; (displayln "")
;; (find-exploit)
;; (displayln "")
;; (find-add-constant)
;; (displayln "")
;; (find-add-argument-max)
(find-add-argument)
