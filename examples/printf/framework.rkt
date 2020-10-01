#lang seec
#;(require (file "syntax.rkt"))
(require (prefix-in safe:
                    (file "printf-spec.rkt")))
(require (file "printf-impl.rkt")) ; unsafe does not have a prefix for now
(require racket/contract)
(require seec/private/framework)

(require rosette/lib/value-browser) ; debugging

(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error
                  parameterize))


(set-bitwidth 16 8)



; It usually makes sense to define functions in the printf grammar that take
; three arguments: a format string, an argument list, and a configuration. This
; function converts such a function into one that accepts a [printf-lang]
; program, consisting of the same parts in a different order.
#;(define/contract (printf-uncurry f)
  (-> (-> fmt? arglist? config? any)
      (-> (cons/c context? fmt?) any))
  (λ (p)
    (match p
      [(cons (printf-lang (args:arglist cfg:config)) fmt)
       (f fmt args cfg)])))



(define/contract (bv-add-integer b x)
  (-> bv? integer? bv?)
  #;(printf "(bv-add-integer ~a ~a)~n" b x)
  (bvadd b (bonsai-bv-value (integer->bonsai-bv x)))
  )

(define/contract (add-constant-spec c p res)
  (-> integer? printf-program? behavior? boolean?)
  #;(printf "(add-constant-spec ~a ~a ~a)~n" c p res)
  (let* ([acc (conf->acc (program->config p))]
         [acc+ (conf->acc (behavior->config res))]
         )
    (equal? acc+ (bv-add-integer acc c))
    ))
(define/contract (safe:add-constant-spec c p res)
  (-> integer? safe:printf-program? safe:behavior? boolean?)
  #;(printf "(add-constant-spec ~a ~a ~a)~n" c p res)
  (let* ([acc (safe:conf->acc (safe:program->config p))]
         [acc+ (safe:conf->acc (safe:behavior->config res))]
         )
    (equal? acc+ (+ acc c))
    ))


(define (symbolic? e)
  (not (equal? (symbolics e) (list ))))


(define (find-increment-gadget)
  (define g (find-gadget safe:printf-spec
                         ((curry safe:add-constant-spec) 1)
                         #;(λ (input-program result-behavior)
                           (let* ([acc-before (conf->acc (program->config input-program))]
                                  [acc-after  (conf->acc (behavior->config result-behavior))])
                             (= acc-after (+ 1 acc-before))))
;                         #:count 3
                         ))
  (display-gadget g displayln)
  )
#;(find-increment-gadget)



(define (find-add-constant-gadget c)

  (define g (find-gadget safe:printf-spec
                         ((curry safe:add-constant-spec) c)
                         #:expr-bound 5
                         #:context-bound 3
                         ; NOTE: will not find gadget without this context-constraint. WHY????
                         #:context-constraint (λ (ctx) (match (safe:context->arglist ctx)
                                                         [(safe:printf-lang (cons s:string arglist))
                                                          ; need to compare the
                                                          ; string via equal?
                                                          ; because pattern
                                                          ; matching against
                                                          ; string literals does
                                                          ; not work currently
                                                          (equal? s (safe:printf-lang ""))]
                                                         [_ #f]))
                         ))
  (display-gadget g displayln)
  )
#;(find-add-constant-gadget 100)

(define (find-add-argument-gadget)

  (printf "Attempting to synthesize an add-argument gadget~n~n")

  (define/contract f-concrete fmt?
    (printf-lang (cons (% ((1 $) ((* 0) s))) nil)))
  (define/contract f-bad fmt?
    (printf-lang (cons (% ((0 $) (1 d)))
                 (cons (% ((0 $) ((* 0) d))) nil))))
  (define/contract f-bad-2 fmt?
    (printf-lang (cons (% ((1 $) (16383 d)))
                 (cons (% ((0 $) (NONE d))) nil))))

  (define/contract (args-concrete y-val) (-> integer? arglist?)
    (printf-lang (cons ,(integer->bonsai-bv y-val) (cons "" nil))))
  (define/contract (args-bad y-val) (-> integer? arglist?)
    (printf-lang (cons ,(integer->bonsai-bv y-val)
                 (cons ,(integer->bonsai-bv y-val) nil))))
  (define/contract (args-bad-2 y-val) (-> integer? arglist?)
    (printf-lang (cons ,(integer->bonsai-bv y-val)
                 (cons (* ,(integer->bonsai-bv 0))
                 nil))))

  (define/contract (context-concrete y-val)
    (-> integer? context?)
    (printf-lang (,(args-concrete y-val)
                  ((bv 0) nil))))


  (define/contract (arglist-constraint ctx idx y-val)
    (-> context? integer? integer? boolean?)
    #;(begin
      (define m (conf->mem (context->config ctx)))
      (define y-bv (integer->bonsai-bv y-val))
      (define (constraint args)
        (match args
          [(printf-lang nil) #f]
          [(printf-lang (cons e:expr args+:arglist))
           (or (equal? (eval-expr e m) y-bv)
               (constraint args+)
               )]
          ))
      (define res (constraint (context->arglist ctx)))
      res
      )
    (equal? (lookup-offset idx ctx)
            (integer->bonsai-bv y-val))
    )

  #;(parameterize ([debug? #t])
    (interp-fmt f-concrete
                       (args-concrete 3)
                       (printf-lang ((bv 0) nil))))

  (define-symbolic x-val integer?)
  (define-symbolic acc-val integer?)

  (define args-symbolic (printf-lang arglist 4))
  (define context-symbolic
    (printf-lang (,args-symbolic
                  (,(integer->bonsai-bv acc-val)
                   nil))))

  ; One of the biggest problems is that we will sometimes synthesize a bogus
  ; answer, like e.g. %0$d... ??? maybe it still has to do with bitvectors??
  (display-gadget
   (find-gadget printf-impl
                       ((curry add-constant-spec) x-val)
;                       #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
;                                                                    (program->context p)))
                       ; This valid constraint is not *necessarily* good for printf-impl
                       #:expr-bound 6
;                       #:expr-constraint (λ (e) (equal? e f-concrete))
                       #:context-bound 4 ; must be at least 4
                       #:context (context-concrete x-val) ;context-symbolic
                       #:context-constraint (λ (ctx)
                                              (and (arglist-constraint ctx 0 x-val)
                                                   ; NOTE: no symbolic variables
                                                   ; (like a symbolic index)
                                                   ; should appear in these
                                                   ; constraints. ALSO: we don't
                                                   ; want to quantify over the
                                                   ; entire context, since we
                                                   ; want to figure out what x
                                                   ; and s should be!
                                                   (equal? ctx (context-concrete x-val))
                                                   ))
                       #:fresh-witness #f
                       #:debug #f
                       #:forall (list x-val acc-val)
                       )
   displayln)
  (displayln "Done")
  )
#;(find-add-argument-gadget)
; NOTE: still doesn't work for context-symbolic...


(define (find-load-gadget)

  (define/contract f-concrete fmt?
    (printf-lang (cons (% ((0 $) ((* 1) s))) nil)))
  (define args+ (printf-lang arglist 2))
  (define/contract (args-concrete l) (-> ident? arglist?)
    (printf-lang (cons "" (cons (* (LOC ,l)) ,args+))))
  (define m+ (printf-lang mem 2))
  (define/contract (mem-concrete l y-val)
    (-> ident? integer? mem?)
    (printf-lang (cons (,l ,(integer->bonsai-bv y-val)) ,m+)))

    
  (define/contract (context-concrete l y-val acc-val)
    (-> ident? integer? integer? context?)
    (printf-lang (,(args-concrete l)
                  (,(integer->bonsai-bv acc-val)
                   ,(mem-concrete l y-val)
                   ))))

  #;(parameterize ([debug? #t])
    (define res (interp-fmt-unsafe f-concrete (args-concrete 128) (printf-lang ((bv 0) nil))))
    (define spec (add-constant-spec 128 (make-program f-concrete (args-concrete 128)
                                                 (printf-lang ((bv 0) nil)))
                                    res))
    (printf "spec: ~a~n" spec)
    )

  (define-symbolic x-val integer?)
  (define-symbolic acc-val integer?)
  (define-symbolic l-val integer?)
  (define/contract l ident? (bonsai-integer l-val))

  #;(define l-val (printf-lang ident 1))
  (display-gadget
   (find-gadget printf-impl
                       ((curry add-constant-spec) x-val)
                       #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
                                                                    (program->context p)))
                       #:expr-bound 6
;                       #:expr f-concrete
;                       #:expr-constraint (λ (f) (equal? f f-concrete))
                       #:context-bound 6
                       ; NOTE: I found it easier to provide this "concrete"
                       ;   context with symbolic variables in it, than to
                       ;   provide a completely symbolic context and constrain
                       ;   it. Not only did the completely symbolic version take
                       ;   multiple minutes as opposed to less than 1 minute,
                       ;   but it provided a bogus answer. Debugging this would
                       ;   be useful, but in the meantime providing sketches is
                       ;   a reasonable compromise.
                       #:context (context-concrete l x-val acc-val)
                       #:fresh-witness #f
#|
                       #:context-constraint (λ (ctx) 
                                              (and (match (context->arglist ctx)
                                                     ; NOTE: ideally we could
                                                     ; just say that l occurs in
                                                     ; the arglist, not exactly
                                                     ; the shape of the arglist
                                                     [(printf-lang (cons s:string
                                                                   (cons (* (LOC l+:ident))
                                                                   arglist)))
                                                      (equal? l+ l)
                                                      ]
                                                     [_ #f])
                                                   (equal? (integer->bonsai-bv acc-val)
                                                    (bonsai-bv (conf->acc (context->config ctx))))
                                                   (match (conf->mem (context->config ctx))
                                                     [(printf-lang (cons (l+:ident v+:bvint) mem))
                                                      (and (equal? l+ l)
                                                           (equal? v+ (integer->bonsai-bv x-val)))]
                                                     [_ #f])
                                                   )
                                               )
|#                      
                       #:forall (list l-val x-val acc-val)
                       )
   displayln)
  )
#;(find-load-gadget)


(define (find-add-mem-gadget)

  (define/contract f-concrete fmt?
    (printf-lang (cons (% ((3 $) ((* 0) s))) ; first  add value1 to the accumulator
                 (cons (% ((3 $) ((* 1) s))) ; second add value2 to the accumulator
                 (cons (% ((2 $) (NONE n)))  ; then write the result to the target location
                       nil)))))
  (define/contract (args-structure l1 l2 l3 args+)
    (-> ident? ident? ident? arglist? arglist?)
    (printf-lang (cons (* (LOC ,l1))
                 (cons (* (LOC ,l2))
                 (cons (LOC ,l3)
                 ,args+)))))
  (define/contract (mem-structure l1 x1 l2 x2 m+)
    (-> ident? integer? ident? integer? mem? mem?)
    (printf-lang (cons (,l1 ,(integer->bonsai-bv x1))
                 (cons (,l2 ,(integer->bonsai-bv x2))
                 ,m+))))

  (define (add-mem-spec l1 l2 l3 p b)
      ; 1. look up the bitvector value of l1 in the memory of p
      ; 2. look up the bitvector value of l2 in the memory of p
      ; 3. look up the bitvector value of l3 in the memory of b
      ; 4. check if l3 = l1+l2
    (let* ([cfg (context->config (program->context p))]
           [m   (conf->mem cfg)]
           [m+  (conf->mem (behavior->config b))]
           [x1  (lookup-loc l1 m)]
           [x2  (lookup-loc l2 m)]
           [x3  (lookup-loc l3 m+)]
           )
      (and (bonsai-bv? x1) (bonsai-bv? x2) (bonsai-bv? x3)
           (equal? (bonsai-bv-value x3)
                   (bvadd (bonsai-bv-value x1)
                          (bonsai-bv-value x2))))))

  
  #;(parameterize ([debug? #t])
    (define l1-concrete (bonsai-integer 1))
    (define l2-concrete (bonsai-integer 2))
    (define l3-concrete (bonsai-integer 3))
    (define conf (printf-lang ((bv 0) ,(mem-structure l1-concrete 1 l2-concrete 2 (printf-lang nil)))))
    ; the result should be (bv 3)
    (define res (interp-fmt f-concrete
                                   (args-structure l1-concrete l2-concrete l3-concrete
                                                   (printf-lang (cons "" nil)))
                                   conf))
    (define spec (add-mem-spec l1-concrete l2-concrete l3-concrete
                               (make-program f-concrete
                                             (args-structure l1-concrete l2-concrete l3-concrete
                                                   (printf-lang (cons "" nil)))
                                             conf)
                               res))
    (printf "spec: ~a~n" spec)
    )

  (define-symbolic l1-val integer?)
  (define-symbolic l2-val integer?)
  (define-symbolic l3-val integer?)
  (define l1 (bonsai-integer l1-val)) ; Note: when I made l1, l2, and l3 purely
                                      ; symbolic and quantified over them, I got
                                      ; bogus answers
  (define l2 (bonsai-integer l2-val))
  (define l3 (bonsai-integer l3-val))
  (define-symbolic x1-val integer?)
  (define-symbolic x2-val integer?)
  #;(define-symbolic z-val integer?)

  (define args-symbolic
    (printf-lang (cons (* (LOC ,l1))
                 (cons (* (LOC ,l2))
                 (cons (LOC ,l3)
                 ,(printf-lang arglist 2))))))
  (define mem-symbolic
    (printf-lang (cons (,l1 ,(integer->bonsai-bv x1-val))
                 (cons (,l2 ,(integer->bonsai-bv x2-val))
                 ,(printf-lang mem 1)))))

  (define context-structure
    (printf-lang (,args-symbolic ; arglist
                  ((bv 0) ; we will start with bv 0 here
                   ,mem-symbolic))))


  (display-gadget
   (find-gadget printf-impl
                       (λ (p b) (add-mem-spec l1 l2 l3 p b))
                       #:expr-bound 7
;                       #:expr-constraint (λ (e) (equal? e f-concrete))
;                       #:context-bound 8
                       #:context context-structure
                       ; NOTE: SEEC is not very good at synthesizing maps based
                       ; on specifications of their contexts... e.g. on what lookup-loc does
                       #:fresh-witness #f
                       #:forall (list l1-val l2-val l3-val x1-val x2-val)
                       )
   displayln)
  )
(time (find-add-mem-gadget))
