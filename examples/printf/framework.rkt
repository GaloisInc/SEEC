#lang seec
(require (file "syntax.rkt"))
(require seec/private/framework)

(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(current-bitwidth 5)

(define (spec-interpret p)
  (match p
    [(cons (printf-lang (args:arglist conf:config)) f)
     (interp-fmt-safe f args conf)]
    [_ (raise-argument-error 'spec-interpret
                              "(cons (printf-lang (arglist config)) (printf-lang fmt))"
                              p)]
    ))

(define (impl-interpret p)
  (match p
    [(cons (printf-lang (args:arglist conf:config)) f)
     (interp-fmt-unsafe f args conf)]
    [_ (raise-argument-error 'impl-interpret
                              "(cons (printf-lang (arglist config)) (printf-lang fmt))"
                              p)]
    ))

; There is probably a better way of doing this
; I just want to limit the size of config and of the vlist separately
(define (max-context-size config-size args-size)
  (lambda (ctx)
    (match ctx
       [(printf-lang (args:arglist conf:config))
        (let ([c* (printf-lang config config-size)]
              [a* (printf-lang arglist args-size)])
          (and (equal? conf c*) (equal? args a*)))])))

; only link when the arglist is consistant with the format-string
; I think a cleaner way of doing this would be
; context-relation: s.exp -> t.exp -> s.ctx -> t.ctx
(define (link-context-fmt ctx f)
  (match ctx
    [(printf-lang (args:arglist conf:config))
     (if (fmt-consistent-with-arglist? f args)
         (cons ctx f)
         (assert #f))]))


(define (valid-context valid-args valid-config)
  (lambda (ctx)
    (match ctx
      [(printf-lang (args:arglist conf:config))
       (and (valid-args args) (valid-config conf))])))



(define (link-context-empty-args acc f)
  (let* ([args (printf-lang nil)]
         [conf (printf-lang (,acc mnil))]
         [ctx (printf-lang (,args ,conf))])
        (cons ctx f)))
    
;; Note: moved the nil-arglist version of printf-spec to its own language since
;; it has no weird machines
(define-language printf-spec-simpl
  #:grammar printf-lang
  #:expression fmt #:size 3
  #:context integer #:size 1
  #:link link-context-empty-args
  #:evaluate spec-interpret
  )
(define-language printf-spec
  #:grammar printf-lang
  #:expression fmt #:size 4
  #:context context #:size 5 #:where (max-context-size 5 2)
  #:link cons
  #:evaluate spec-interpret
  )


(define-language printf-impl
  #:grammar printf-lang
  #:expression fmt #:size 5
  #:context context #:size 5 #:where (max-context-size 5 2)
  #:link cons ;link-context-fmt
  #:evaluate impl-interpret)


;; ctx1 in printf-spec is an integer consisting just of the accumulator.
;; ctx2 in printf-impl is a printf-lang context.
;; they are related when the accumulator values are the same and the argument list and memory in ctx2 is nil.
;; we do allow ctx2 to have a non-trivial arglist. If not, there would be no weird machines.
(define (spec-to-impl-context-relation ctx1 ctx2)
  (match ctx2
    [(printf-lang (arglist (acc:integer mnil)))
     (equal? (bonsai->number acc) (bonsai->number ctx1))]
    [_ #f]))

(define-compiler spec-to-impl
  #:source printf-spec
  #:target printf-impl
  #:behavior-relation equal?
  #:context-relation equal? #;spec-to-impl-context-relation
  #:compile (λ (x) x)
  )

;; find-weird-component
#;(begin
  (displayln "Trying to find a format string with weird behavior")
  (define witness (time (find-weird-component spec-to-impl)))
  (display-weird-component witness displayln)
  )



;find-exploit-gadget
(define (valid-conf prog)
  (match prog
    [(cons ctx f)     
     (match ctx
       [(printf-lang (args:arglist conf:config))
        (match (interp-fmt-unsafe f args conf)
          [(list str conf+) (conf? conf+)])])]))
     

(define (fmt-consistent-with-arglist?-uncurry prog)
    (match prog
      [(cons ctx f)
       (match ctx
         [(printf-lang (args:arglist conf:config))
          (fmt-consistent-with-arglist? f args)])]))



(define (is-constant-add f c args conf)
  (let ([conf+ (behavior->config (interp-fmt-safe f args conf))])
    (equal? (conf->acc conf+) (+ c (conf->acc conf)))))

; TODO: fix: this function doesn't currently actually use beh and instead re-calls intepr-fmt-safe
(define (is-constant-add-spec prog beh)
    (match prog
    [(cons ctx f)
     (match ctx
       [(printf-lang (args:arglist conf:config))
        (is-constant-add f 1 args conf)])]))

#;(begin
  (displayln "Trying to find a format string that increments the accumulator by 1")
  (display-gadget (find-gadget printf-spec fmt-consistent-with-arglist?-uncurry is-constant-add-spec) displayln))

(define (is-constant-add-positive f c args conf)
  (let* ([conf+ (behavior->config (interp-fmt-safe f args conf))]
         [acc   (conf->acc conf)]
         [acc+  (conf->acc conf+)]
        )
    (equal? acc+ (+ (max c 0) acc))
    ))

(define (is-constant-add-positive-spec prog beh)
  (match (cons beh prog)
    [(cons (printf-lang (t:trace conf+:config))
                 ; assume that the arglist has the form (cons x args+),
                 ; where x is the value being added to the accumulator
           (cons (printf-lang ((cons x:integer args+:arglist) conf:config))
                 f))
     (let ([acc+ (conf->acc conf+)]
           [acc  (conf->acc conf)]
           )
         
     (equal? acc+ (+ (max (bonsai->number x) 0) acc)))
     ]
    ))
     


#;(define (is-constant-add-link x-val ctx f)
  (define args (match ctx
                 [(printf-lang (args:arglist config)) args]
                 ))
  (define args+ (printf-lang arglist 3))
  (assert (equal? args (ll-cons (bonsai-integer x-val) args+)))
  (cons ctx f)
  )



(define (context-is-x config-size arg-size x-val)
  (λ (ctx)
    (match ctx
      [(printf-lang (args:arglist conf:config))
       (let ([c* (printf-lang config config-size)]
             [a+ (printf-lang arglist (- arg-size 1))]
             )
         (and (equal? conf c*)
              (equal? args (ll-cons (bonsai-integer x-val) a+))
              ))])))
      
(begin 
  (define-symbolic x-val integer?)
  (define-language printf-is-constant-add
    #:grammar printf-lang
    #:expression fmt #:size 4
    #:context context #:size 5 #:where (context-is-x 5 2 x-val)
    #:link cons
    #:evaluate spec-interpret
    )

  (displayln "Trying to find a format string that adds the value of a positive
number x to the accumulator")
  
  (define sol (find-gadget printf-is-constant-add
                               fmt-consistent-with-arglist?-uncurry
                               (is-constant-add-positive-spec x-val)))
  (display-gadget sol displayln)
  )
