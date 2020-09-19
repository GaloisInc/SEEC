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

(define find-gadget-custom
  (λ (lang ; SEEC langauge
      #:valid              [valid-program (λ (p) #t)]
      spec ; program -> behavior -> boolean
      #:expr-bound         [bound-e #f]
      #:context-bound      [bound-c #f]
      #:context            [ctx (make-symbolic-var (language-context lang) bound-c)]
      #:context-constraint [ctx-constraint (λ (x) #t)] ; (-> context? boolean?)
      #:expr               [e (make-symbolic-var (language-expression lang) bound-e)]
      #:expr-constraint    [e-constraint (λ (x) #t)] ; (-> expr? boolean?)

      #:fresh-witness      [fresh #t] ; set to false if we should NOT generate a
                                      ; fresh witness context, e.g. if you are
                                      ; providing an argument for the context
      #:debug              [debug #f] ; if debug is set, then we will attempt to
                                      ; synthesize an expression that violates the specification
      #:forall             [vars (if debug
                                     (list ) ; no quantifiers for debugging
                                     ctx)]   ; any term containing symbolic variables to be quantified over
      #:forall-extra       [vars-extra (list )]
      )
    (let*
        ([p ((language-link lang) ctx e)]
         [b ((language-evaluate lang) p)]
         ; creating second context to return as example if the first is symbolic
         [ctx-witness (if fresh
                          (make-symbolic-var (language-context lang) bound-c)
                          ctx
                          )]
         [p-witness ((language-link lang) ctx-witness e)]
         [b-witness ((language-evaluate lang) p-witness)]
         [sol (synthesize #:forall (cons vars vars-extra)
                          #:assume (assert (and (valid-program p)
                                                (valid-program p-witness)
                                                ; we need to constrain both the
                                                ; ctx and the ctx-witness
                                                (ctx-constraint ctx)
                                                (ctx-constraint ctx-witness) 
                                                (e-constraint e)))
                          #:guarantee (assert (if debug
                                                  (not (spec p b))
                                                  (spec p b))))]
         )
      (if (unsat? sol)
          #f
          (let* ([symbolic-witness (solution (list (language-witness e ctx-witness p-witness b-witness))
                                             sol)]
                 [witness (concretize-witness symbolic-witness)]
                 [core (language-witness-expression (first witness))]
                 )
            witness))
      )))
      


(define (find-increment-gadget)
  (define g (find-gadget-custom printf-spec
                         ((curry add-constant-spec) 1)
                         ))
  (display-gadget g displayln)
  )
#;(find-increment-gadget)



(define (find-add-constant-gadget c)

  (define g (find-gadget-custom printf-spec
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
#;(find-add-constant-gadget 100)

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
   (find-gadget-custom printf-impl
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
#;(find-add-argument-gadget)


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
   (find-gadget-custom printf-impl
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
(find-load-gadget)


; If the gadget fails to synthesize, what could be wrong?

; 1. The specification is unsatisfiable.
;
; Solution: Identify a gadget/context pair that satisfies the specification. Use
;   unit tests (possibly using parameterize debug?) to check that the
;   specification is satisfied for a concrete example. If that succeeds, use
;   #:expr and #:context arguments to check that the find-gadget query succeeds
;   on that concrete argument. Use the argument (#:fresh-witness #f).

; 2. The specification is satisfied for a particular unit test, but fails when
;   quantifying over symbolic variables.
;
; Solution: Use #:forall or #:forall-extra to limit or extend the variables
;   being quantified over. For example, set (#:forall (list )) to stop universal
;   quantification over contexts. If synthesis succeeds when removing one or
;   more quantifiers, use the (#:debug #t) argument to search for
;   counterexamples---instantiations of the variables that cause the
;   specification to fail.

; 2. The expression or context bound is too small
; 
; Solution: Assume you know a gadget/context pair that satisfies Solution 1.
;   Remove the #:expr (resp #:context) argument and replace with
;   (#:expr-constraint (λ (e) (equal? e concrete-e))). If this fails, increase
;   the #:expr-bound argument until it succeeds.

; 3. The witnessed behavior is ERROR and/or the witnessed context is incompatible.
;
; Solution: If this happens when given a concrete context argument, add the
;   argument (#:fresh-witness #f), which will stop the query from generating a
;   new argument and instead reuse the one provided. Otherwise, add a #:valid
;   constraint or #:context-contraint to limit the search to contexts that
;   provide meaningful results.
