#lang seec
(require (file "syntax.rkt"))

(define (spec-interpret p)
  (match p
    [(cons ctx f)     
     (match ctx
       [(printf-lang (conf:config args:arglist))
        (interp-fmt-safe f args conf)])]))

(define (impl-interpret p)
  (match p
    [(cons ctx f)     
     (match ctx
       [(printf-lang (conf:config args:arglist))
        (interp-fmt-unsafe f args conf)])]))


; There is probably a better way of doing this
; I just want to limit the size of config and of the vlist separately
(define (max-context-size config-size args-size)
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



(define-language printf-spec
  #:grammar printf-lang
  #:expression fmt #:size 2
  ; any way to make the where clause assume consistency with the format?
  #:context context #:size 6; #:where (max-context-size 5 2)
  #:link cons ;link-context-fmt
  #:evaluate spec-interpret
  )

(define-language printf-impl
  #:grammar printf-lang
  #:expression fmt #:size 5
  #:context context #:size 5 #:where (max-context-size 5 2)
  #:link cons ;link-context-fmt
  #:evaluate impl-interpret)


(define-compiler spec-to-impl
  #:source printf-spec
  #:target printf-impl
  #:behavior-relation equal?
  #:context-relation equal?
  #:compile (λ (x) x)
  )

#;(define (find-add-constant-gadget)
  (displayln "Trying to find a format string that adds a constant number to the accumulator")
)
#;(begin
  (displayln "Trying to find a trace with different behavior under compilation")
  (define trace (printf-lang interaction 6))
  (define witness (find-changed-behavior abstract-to-concrete trace))
  (display-witness witness))



;find-exploit-gadget
(define (valid-conf prog)
  (match prog
    [(cons ctx f)     
     (match ctx
       [(printf-lang (conf:config args:arglist))
        (match (interp-fmt-unsafe f args conf)
          [(list str conf+) (conf? conf+)])])]))
     

(define (fmt-consistent-with-arglist?-uncurry prog beh)
  (match prog
    [(cons ctx f)
     (match ctx
       [(printf-lang (conf:config args:arglist))
        (fmt-consistent-with-arglist? f args)])]))


(displayln "Trying to find the same exploit using the framework")
(find-gadget printf-spec valid-conf  fmt-consistent-with-arglist?-uncurry)
;(display-gadget (find-gadget printf-spec valid-conf fmt-consistent-with-arglist?-uncurry))
