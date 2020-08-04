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
    (time (verify (val? (lookup-offset offset args)))))
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
  (define sol (time (verify (mem? (mem-update m l v)))))
  (if (unsat? sol)
      (displayln "Verified")
      (displayln "Counterexample found.")))


(define (test-interp-fmt-safe)
  (displayln "Testing interp-fmt-safe")
  (define f (printf-lang fmt 2))
  (define args (printf-lang arglist 4))
  (define conf (printf-lang config 4))
  (assert (fmt-consistent-with-arglist? f args))
  (define sol (time (verify (match (interp-fmt-safe f args conf)
                              [(printf-lang (trace conf+:config)) (conf? conf+)]
                              ))))
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
  (define f (printf-lang fmt 2))
  (define args (printf-lang arglist 4))
  (define conf (printf-lang config 5))
  #;(assert (fmt-consistent-with-arglist? f args))
  (define guarantee
    (match (interp-fmt-unsafe f args conf)
      [(printf-lang (trace conf+:config)) (conf? conf+)]
      [_ #f]))
  (define sol (time (verify
               #:guarantee guarantee
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
        (define res-instance (interp-fmt-unsafe f-instance args-instance conf-instance))
        (displayln res-instance)
        (conf? (behavior->config res-instance))
        )))

(define (find-exploit)
  (current-bitwidth 3)

  (define f (printf-lang fmt 5))
  ;(assert (equal? f (printf-lang (cons (% (0 $) NONE d) nil))))
  (define args (printf-lang arglist 2))
  ;(assert (equal? args (printf-lang nil)))
  (define conf (printf-lang config 5))
  (displayln "Searching for a format string that evaluates in the target but not in the source")
  
  (define safe-result (interp-fmt-safe f args conf))
  (define unsafe-result (interp-fmt-unsafe f args conf))
  #;(define conf+ (behavior->config (interp-fmt-unsafe f args conf)))
  (define sol (time (synthesize
               #:forall '()
               #:guarantee (assert (and #;(not (fmt-consistent-with-arglist? f args))
                                        #;(equal? safe-result (printf-lang ERR))
                                        #;(conf? conf+)
                                        (not (equal? safe-result unsafe-result))
                                        )))))
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
(define (is-increment? f args conf)
  (let* ([conf+ (behavior->config (interp-fmt-safe f args conf))]
         [acc   (conf->acc conf)]
         [acc+  (conf->acc conf+)]
        )
    (equal? acc+ (+ 1 acc))
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
  (current-bitwidth 3)
  (define f (printf-lang fmt 5))
  (define acc0 (printf-lang integer 1))
  (define conf (printf-lang (,acc0 mnil)))
  #;(define conf (printf-lang config 5))
  (define args (printf-lang arglist 2))
  #;(define args (printf-lang nil))


  (displayln "")
  (displayln "Searching for a format string that adds 1 to the accumulator")
  (define sol (time (synthesize
               #:forall acc0
               #:guarantee (assert (is-increment? f args conf)))))
  (displayln "")
  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded.")
        (displayln "f...")
        (define f-instance (concretize f sol))
        (displayln f-instance)
        (define acc0-instance (bonsai-integer 20) #;(concretize acc0 sol))
        (displayln "acc0...")
        (displayln acc0-instance)
        (define conf-instance (printf-lang (,acc0-instance mnil)))
        (displayln "conf before...")
        (displayln conf-instance)
        (define args-instance (concretize args sol))
        (displayln "args...")
        (displayln args-instance)



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
  (current-bitwidth 3)
  (define-symbolic x integer?)
  (define sol (time (synthesize
               #:forall x
               #:guarantee (<= (min-int) x (max-int)))))
  sol
  )


(define (find-add-argument-max)

  (current-bitwidth 3)
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


(define (verify-add-argument f)

  (define-symbolic* acc0-val integer?)
  (define conf (printf-lang config 2))
  (define acc0 (match conf
                 [(printf-lang (acc:integer mem)) acc]))

  (define (conf-constraint acc0-val conf)
    (match conf
      [(printf-lang (acc:integer mem)) (equal? (bonsai-integer acc0-val) acc)]))
  
  (define-symbolic* x-val integer?)
  (define args (printf-lang arglist 3))
  (define args+ (printf-lang arglist 2))
  (define (args-constraint x-val args args+)
    (equal? args (ll-cons (bonsai-integer x-val) args+))
    #;(match args
      [(printf-lang (cons x:val arglist))
       (equal? x (bonsai-integer x-val))])
    )

  (define (synthesis-goal) (is-constant-add-positive f x-val args conf))
  (assert (conf-constraint acc0-val conf))
  (assert (args-constraint x-val args args+))
  (define res (interp-fmt-safe f args conf))

  (define sol (time (synthesize
                     #:forall (list acc0-val x-val)
                     #:guarantee (assert (synthesis-goal))
               )))

  sol
  )

(define (debug-add-argument f)

  (define-symbolic* acc0-val integer?)
  (define conf (printf-lang (,(bonsai-integer acc0-val) mnil)))
  (define acc0 (match conf
                 [(printf-lang (acc:integer mem)) acc]))

  (define (conf-constraint acc0-val conf)
    (match conf
      [(printf-lang (acc:integer mem)) (equal? (bonsai-integer acc0-val) acc)]))

  (define-symbolic* x-val integer?)
  (define args+ (ll-singleton (printf-lang "")))
  (define args (ll-cons (bonsai-integer x-val) args+))

  (define (args-constraint x-val args args+)
    (equal? args (ll-cons (bonsai-integer x-val) args+)))


  (define sol (time (optimize
               #:minimize (list x-val)
               #:guarantee (assert (not (is-constant-add-positive f x-val args conf)))
               )))

  (if (unsat? sol)
      (displayln "No counterexample found")
      (begin 
        (define f-result (concretize f sol))
        (printf "f: ")
        (displayln f-result)

        (define sol+ (expand-solution sol (list x-val acc0-val)))
        (define x-concrete (concretize+ x-val sol+))
        (printf "x-val: ~a~n" x-concrete)
        (define acc0-concrete (concretize+ acc0-val sol+))
        (printf "acc-val: ~a~n" acc0-concrete)
        (define conf-concrete (concretize+ conf sol+))
        (printf "conf: ~a~n" conf-concrete)
        #;(conf-constraint acc0-concrete conf-concrete)
        (define args-concrete (concretize+ args sol+))
        (printf "args-concrete: ~a~n" args-concrete)
        (define args+-concrete (concretize+ args+ sol+))
        (printf "args+-concrete: ~a~n" args+-concrete)
        #;(args-constraint x-concrete args-concrete args+-concrete)
        #;(is-constant-add-positive f-result
                       0
                       (ll-cons (bonsai-integer 0) (ll-singleton (printf-lang "")))
                       (printf-lang (6 mnil))
                       )
  ))


  )

(define (find-add-argument)
  (current-bitwidth 3)
  (define f-concrete (printf-lang (cons (% (1 $) (* 0) s) nil)))
  (define f-bad (printf-lang (cons (% (1 $) 13 d) nil)))
  (define f-symbolic (printf-lang fmt 5))

  (displayln "Searching for a format string that adds the value of x to the accumulator")
  (define sol (verify-add-argument f-symbolic))
  (if (unsat? sol)
      (printf "Failed to synthesize~n")
      (begin
        (define f-synthesized (concretize f-symbolic sol))
        (define f-sol (verify-add-argument f-synthesized))
        (if (unsat? sol)
            (printf "Synthesized bogus result: ~a~n" f-synthesized)
            (printf "Synthesis succeeded: ~a~n" f-synthesized)
            )
        ))
  )

#;(define (find-add-argument)

  (current-bitwidth 3)
  (define f-concrete (printf-lang (cons (% (1 $) (* 0) s) nil)))
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

  ; NOTE: the function `interp-fmt-safe` must be called before the call to
  ; synthesize or else will get bogus answer... WHY????
  #;(assert (fmt-consistent-with-arglist? f args))
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


(test-lookup-offset)
(displayln "")
(clear-asserts!)
(displayln "")
(test-mem-update)
(displayln "")
(clear-asserts!)
(displayln "")
(test-interp-fmt-safe)
(displayln "")
(displayln "")
(clear-asserts!)
(test-interp-fmt-unsafe)
(displayln "")
(find-exploit)
(displayln "")
(clear-asserts!)
(displayln "")
(find-add-constant)
(displayln "")
(clear-asserts!)
(displayln "")
(find-add-argument-max)
(displayln "")
(clear-asserts!)
(displayln "")
(find-add-argument)

