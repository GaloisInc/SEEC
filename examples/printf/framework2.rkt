#lang seec
(require (file "syntax.rkt"))
(require racket/contract)
(require seec/private/framework)

(require rosette/lib/value-browser) ; debugging

(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

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

(define (valid-printf-spec-program? f args cfg)
  (fmt-consistent-with-arglist? f args))

(define/contract (bv-add-integer b x)
  (-> bv? integer? bv?)
  #;(printf "(bv-add-integer ~a ~a)~n" b x)
  (bvadd b (bonsai-bv-value (integer->bonsai-bv x)))
  )




(define/contract (add-constant-spec c p res)
  (-> integer? printf-program? behavior? boolean?)
  ;(printf "(add-constant-spec ~a ~a ~a)~n" c p res)
  (let* ([acc (conf->acc (program->config p))]
         [acc+ (conf->acc (behavior->config res))]
         )
    (equal? acc+ (bv-add-integer acc c))
    ))



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
      #:forall             [vars ctx] ; any term containing symbolic variables to be quantified over
      )
    (let*
        ([p ((language-link lang) ctx e)]
         [b ((language-evaluate lang) p)]
         ; creating second context to return as example
         [ctx-witness (make-symbolic-var (language-context lang) bound-c)]
         [p-witness ((language-link lang) ctx-witness e)]
         [b-witness ((language-evaluate lang) p-witness)]
         [sol (synthesize #:forall vars
                          #:assume (assert (and (valid-program p)
                                                ; we need to constraint both the
                                                ; ctx and the ctx-witness
                                                (ctx-constraint ctx)
                                                (ctx-constraint ctx-witness) 
                                                (e-constraint e)))
                          #:guarantee (assert (spec p b)))]
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




(define (find-load-gadget)

  ; load a location given by the identifier [l] into the accumulator
  (define/contract (load-spec l p res)
    (-> ident? printf-program? behavior? boolean?)
    (let* ([m (conf->mem (program->config p))]
           [v (lookup-loc l m)]
           [acc+ (conf->acc (behavior->config res))]
           )
      (equal? (bonsai-bv acc+) v)
      ))

  (define l (printf-lang ident 1))

  ; assert that l occurs in the domain of [ctx]'s memory
  (define (domain-constraint ctx)
    (let* ([m (conf->mem (context->config ctx))])
      (bonsai-bv? (lookup-loc l m))))
  ; assert that [*l] occurs in the argument list of [ctx]
  (define (arglist-constraint ctx)
    (match (context->arglist ctx)
      [(printf-lang (cons (* (LOC l+:ident)) arglist))
       (equal? l+ l)]
      [_ #f]
      ))

  (define concrete-fmt  (ll-singleton (printf-lang (% (0 $) (* 0) d))))
  (define concrete-args (list->bonsai-ll (list (printf-lang (* (LOC ,l)))
                                        (printf-lang ""))))
  (define/contract concrete-m
      mem?
      (printf-lang (mcons ,l (bv 3) mnil))
      )
  (define/contract concrete-ctx context? (printf-lang (,concrete-args ((bv 0) ,concrete-m))))

  (display-gadget (find-gadget-custom
                   printf-spec
                   ((curry load-spec) l)
                   #:expr-bound 5
                   #:context-bound 5
;                   #:context-constraint (λ (ctx) (and (domain-constraint ctx)
;                                                      (arglist-constraint)))
                   #:context concrete-ctx
                   #:expr concrete-fmt
                   ))
  )
(find-load-gadget)
