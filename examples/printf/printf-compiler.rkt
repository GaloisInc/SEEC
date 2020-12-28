#lang seec
#;(require racket/base)
(require racket/contract)
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error
                  make-parameter
                  ))
(require rosette/lib/value-browser)

(require (only-in racket/base
                  [make-string unsafe:make-string]
                  ))
(require (only-in seec/private/string
                  char->string))
(require (prefix-in safe:
                    (file "printf-spec.rkt")))
(require (prefix-in unsafe:
                    (file "printf-impl.rkt")))

(provide compile-val
         compile-expr
         compile-arglist
         compile-mem
         compile-config
         compile-context
         compile-program
         compile-behavior
         )

(define/contract (compile-val v)
  (-> safe:val? unsafe:val?)
  (match v
    [(safe:printf-lang n:integer) (unsafe:printf-lang ,(integer->bv n))]
    [_ v]
    ))

(define/contract (compile-expr e)
  (-> safe:expr? unsafe:expr?)
  (match e
    [(safe:printf-lang v:val) (compile-val v)]
    [(safe:printf-lang (* e+:expr))
     (unsafe:printf-lang (* ,(compile-expr e+)))]
    ))

(define/contract (compile-arglist l)
  (-> safe:arglist? unsafe:arglist?)
  (match l
    [(safe:printf-lang nil) l]
    [(safe:printf-lang (cons e:expr l+:arglist))
     (seec-cons (compile-expr e) (compile-arglist l+))]
    ))

(define/contract (compile-mem m)
  (-> safe:mem? unsafe:mem?)
  (match m
    [(safe:printf-lang nil) (unsafe:printf-lang nil)]
    [(safe:printf-lang (cons (x:ident v:val) m+:mem))
     (unsafe:printf-lang (cons (,x ,(compile-val v)) ,(compile-mem m+)))]
    ))

(define/contract (compile-config conf)
  (-> safe:config? unsafe:config?)
  (unsafe:make-config (safe:conf->acc conf)
                      (compile-mem (safe:conf->mem conf))))

(define/contract (compile-context ctx)
  (-> safe:context? unsafe:context?)
  (unsafe:make-context (compile-arglist (safe:context->arglist ctx))
                       (compile-config (safe:context->config ctx))
                       ))

(define/contract (compile-program p)
  (-> safe:printf-program? unsafe:printf-program?)
  (unsafe:make-program (safe:program->fmt p)
                       (compile-arglist (safe:program->arglist p))
                       (compile-config  (safe:program->config p))
                       ))

(define/contract (compile-behavior b)
  (-> safe:behavior? unsafe:behavior?)
  (unsafe:printf-lang (,(safe:behavior->trace b)
                       ,(compile-config (safe:behavior->config b))
                       )))
(define/contract (compile-maybe-behavior b)
  (-> (or/c safe:err? safe:behavior?) (or/c unsafe:err? unsafe:behavior?))
  (cond
    [(safe:err? b) (unsafe:printf-lang ERR)]
    [else          (compile-behavior b)]
    ))



(define-compiler printf-compiler
  #:source safe:printf-spec
  #:target unsafe:printf-impl
  #:behavior-relation (lambda (b1 b2) (equal? (compile-maybe-behavior b1) b2))
  #:context-relation (λ (ctx1 ctx2) (equal? (compile-context ctx1) ctx2))
  #:compile (lambda (f) f))


(define (find-weird-component-example)
  (set-bitwidth 16 8)
  (define/contract fmt-example
    safe:fmt?
    (safe:fmt-string (cons (% ((0 $) (NONE d)))
                           nil)))
  (define-symbolic l-val integer?)
  (define target-args (seec-singleton (unsafe:printf-lang (LOC ,l-val))))
  (define target-conf  (unsafe:printf-lang ((bv 0) nil)))
  (define/contract target-ctx
    unsafe:context?
    (unsafe:printf-lang (,target-args ,target-conf)))
#|

  (define target-behavior (unsafe:interp-fmt fmt-example target-args target-conf))
                                             
  (define src-args (safe:printf-lang arglist 3))
  (define src-config (safe:printf-lang config 3))
  (define/contract src-context safe:context?
    (safe:printf-lang (,src-args ,src-config)))
  (define src-behavior (safe:interp-fmt fmt-example src-args src-config))

  (define sol (synthesize #:forall (list l-val)
                          #:guarantee (assert (equal? (compile-behavior src-behavior)
                                                      target-behavior))
                          ))
  (if (unsat? sol)
      (displayln "No counterexample found")
      (begin
        (displayln "Counterexample found")
        (define src-args+ (concretize src-args sol))
        (define src-config+ (concretize src-config sol))
        (printf "args: ~a~n" src-args+)
        (printf "config: ~a~n" src-config+)
        ))

|#
    
  (define comp (find-weird-behavior printf-compiler
                                    #:source-expr fmt-example
;                                    #:source-context-bound 6
;                                    #:source-context (safe:printf-lang (,target-args (0 nil)))
                                    #:target-context target-ctx
;                                    #:forall-extra (list l-val)
                                    #:debug #f
                                    #:fresh-witness #f
                                    ))
  (display-weird-behavior comp displayln)
  (displayln "hi")
  )
#;(find-weird-component-example)

(define (find-changed-component-example)
  (display-changed-component
   (find-changed-component printf-compiler
                           #:source-expr-bound 3
                           #:source-context-bound 3
                           )
   displayln)
  )
#;(find-changed-component-example)
