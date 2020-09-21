#lang seec
(require (file "syntax.rkt"))
(require racket/contract)
(require seec/private/framework)

(require rosette/lib/value-browser) ; debugging

(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error
                  parameterize))


(set-bitwidth 16 8)


; a context is a pair of an arglist and a config
(define (spec-interpret ctx f)
  (match ctx
    [(printf-lang (args:arglist cfg:config))
     (interp-fmt-safe f args cfg)]))

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

(define-language printf-spec
  #:grammar printf-lang
  #:expression fmt #:size 3
  #:context context #:size 5
  #:link cons
  #:evaluate (λ (p) (interp-fmt-safe (program->fmt p) (program->arglist p) (program->config p)))
  )
(define-language printf-impl
  #:grammar printf-lang
  #:expression fmt #:size 3
  #:context context #:size 5
  #:link cons
  #:evaluate (λ (p) (interp-fmt-unsafe (program->fmt p) (program->arglist p) (program->config p)))
  )


(define (valid-printf-spec-program? f args cfg)
  (fmt-consistent-with-arglist? f args))

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


(define (symbolic? e)
  (not (equal? (symbolics e) (list ))))




(define (find-increment-gadget)
  (define g (find-gadget printf-spec
                         ((curry add-constant-spec) 1)
                         ))
  (display-gadget g displayln)
  )
(find-increment-gadget)



(define (find-add-constant-gadget c)

  (define g (find-gadget printf-spec
                         ((curry add-constant-spec) c)
                         #:expr-bound 5
                         #:context-bound 3
                         ; NOTE: will not find gadget without this context-constraint. WHY????
                         #:context-constraint (λ (ctx) (match (context->arglist ctx)
                                                         [(printf-lang (cons s:string arglist))
                                                          ; need to compare the
                                                          ; string via equal?
                                                          ; because pattern
                                                          ; matching against
                                                          ; string literals does
                                                          ; not work currently
                                                          (equal? s (printf-lang ""))]
                                                         [_ #f]))
                         ))
  (display-gadget g displayln)
  )
(find-add-constant-gadget 100)

(define (find-add-argument-gadget)

  (define/contract f-concrete fmt?
    (printf-lang (cons (% (0 $) (* 1) s) nil)))
  (define/contract (args-concrete y-val) (-> integer? arglist?)
    (printf-lang (cons "" (cons ,(integer->bonsai-bv y-val) nil))))
  (define/contract (context-concrete y-val)
    (-> integer? context?)
    (printf-lang (,(args-concrete y-val)
                  ((bv 0) mnil))))

  #;(parameterize ([debug? #t])
    (define res (interp-fmt-unsafe f-concrete (args-concrete 128) (printf-lang ((bv 0) mnil))))
    (define spec (add-constant-spec 128 (make-program f-concrete (args-concrete 128)
                                                 (printf-lang ((bv 0) mnil)))
                                    res))
    (printf "spec: ~a~n" spec)
    )

  (define-symbolic x-val integer?)
  (define-symbolic acc-val integer?)
  (display-gadget
   (find-gadget printf-impl
                       ((curry add-constant-spec) x-val)
                       #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
                                                                    (program->context p)))
                       #:expr-bound 5
                       #:context-bound 4 ; must be at least 4
                       #:context-constraint (λ (ctx) 
                                              (and (match (context->arglist ctx)
                                                     ; NOTE: don't want to
                                                     ; quantify over the entire
                                                     ; context, since we want to
                                                     ; figure out what x and s should be!
                                                     [(printf-lang (cons s:string
                                                                   (cons x:bvint arglist)))
                                                      (equal? x (integer->bonsai-bv x-val))
                                                      ]
                                                     [_ #f])
                                                   (equal? (integer->bonsai-bv acc-val)
                                                    (bonsai-bv (conf->acc (context->config ctx))))
                                                   )
                                               )
                       #:forall (list x-val acc-val)
                       )
   displayln)
  )
(find-add-argument-gadget)


(define (find-load-gadget)

  (define/contract f-concrete fmt?
    (printf-lang (cons (% (0 $) (* 1) s) nil)))
  (define args+ (printf-lang arglist 2))
  (define/contract (args-concrete l) (-> ident? arglist?)
    (printf-lang (cons "" (cons (* (LOC ,l)) ,args+))))
  (define m+ (printf-lang mem 2))
  (define/contract (mem-concrete l y-val)
    (-> ident? integer? mem?)
    (printf-lang (mcons ,l ,(integer->bonsai-bv y-val) ,m+)))

    
  (define/contract (context-concrete l y-val acc-val)
    (-> ident? integer? integer? context?)
    (printf-lang (,(args-concrete l)
                  (,(integer->bonsai-bv acc-val)
                   ,(mem-concrete l y-val)
                   ))))

  #;(parameterize ([debug? #t])
    (define res (interp-fmt-unsafe f-concrete (args-concrete 128) (printf-lang ((bv 0) mnil))))
    (define spec (add-constant-spec 128 (make-program f-concrete (args-concrete 128)
                                                 (printf-lang ((bv 0) mnil)))
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
                       #:expr-bound 5
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
                                                     [(printf-lang (mcons l+:ident v+:bvint mem))
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


