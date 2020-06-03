#lang seec
(require (file "syntax.rkt"))

(define (spec-interpret p)
  (match p
    [(cons ctx f)     
     (match ctx
       [(printf-lang (args:arglist conf:config))
        (interp-fmt-safe f args conf)])]))

(define (impl-interpret p)
  (match p
    [(cons ctx f)     
     (match ctx
       [(printf-lang (args:arglist conf:config))
        (interp-fmt-unsafe f args conf)])]))


; There is probably a better way of doing this
; I just want to limit the size of config and of the vlist separately
(define (max-context-size config-size args-size)
  (lambda (ctx)
    (match ctx
       [(printf-lang (args:arglist conf:config))
        (let ([c* (printf-lang config config-size)]
              [a* (printf-lang arglist args-size)])
          (and (equal? conf c*) (equal? args a*)))])))

#;(define (max-context-size config-size args-size)
  (lambda (ctx)
    ((match ctx
       [(printf-lang (args:arglist conf:config))
        (let ([c* (printf-lang config config-size)]
              [a* (printf-lang arglist args-size)])
          (and (equal? conf c*) (equal? args a*)))]))))

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
    

(define-language printf-spec
  #:grammar printf-lang
  #:expression fmt #:size 3
  #:context integer #:size 1
  #:link link-context-empty-args
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
;; they are related when the accumulator values are the same and the argument
;; list and memory in ctx2 is nil
(define (spec-to-impl-context-relation ctx1 ctx2)
  (match ctx2
    [(printf-lang (nil (acc:integer mnil)))
     (equal? (bonsai->number acc) ctx1)]
    [_ #f]))

(define-compiler spec-to-impl
  #:source printf-spec
  #:target printf-impl
  #:behavior-relation equal?
  #:context-relation spec-to-impl-context-relation
  #:compile (λ (x) x)
  )

(begin
  (displayln "Trying to find a format string with weird behavior")
  (define witness (time (find-weird-component spec-to-impl)))
  (display-weird-component witness displayln)
  )

;; find-changed-behavior
#;(begin
  (displayln "Trying to find a trace with different behavior under compilation")
  (define f (printf-lang fmt 3))
  (define witness (find-changed-behavior spec-to-impl f))
  (display-changed-behavior witness)
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

(define (is-constant-add-spec prog beh)
    (match prog
    [(cons ctx f)
     (match ctx
       [(printf-lang (args:arglist conf:config))
        (is-constant-add f 1 args conf)])]))

(begin
  (displayln "Trying to find-add-constant using the framework")
  (display-gadget (find-gadget printf-spec fmt-consistent-with-arglist?-uncurry  is-constant-add-spec) displayln))
