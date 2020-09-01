#lang seec
(require (file "syntax.rkt"))
(require racket/contract)
(require seec/private/framework)

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
(define/contract (printf-uncurry f)
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
  #:evaluate (printf-uncurry interp-fmt-safe)
  )

(define (valid-printf-spec-program? f args cfg)
  (fmt-consistent-with-arglist? f args))


(define/contract (increment-spec p res)
  (-> (cons/c context? fmt?) behavior? boolean?)
  ((printf-uncurry (λ (f args cfg)
                     (let* ([acc (conf->acc cfg)]
                            [acc+ (conf->acc (behavior->config res))]
                            )
                       (equal? acc+ (bvadd1 acc)))))
                  p))
(define (find-increment-gadget)
  (set-bitwidth 16 8)
  ; no matter what accumulator we start with, add 1 to the accumulator

  (define g (find-gadget printf-spec
                         (printf-uncurry valid-printf-spec-program?)
                         increment-spec
                         ))
  (display-gadget g displayln)
  )
(find-increment-gadget)
(define (printf-program? p)
  (and (pair? p)
       (context? (car p))
       (fmt? (cdr p))
       ))

#;(define (find-increment-gadget-manual)
  (set-bitwidth 16 8)

  (define c1 (make-symbolic-var (language-context printf-spec) 5))
  (define v1 (make-symbolic-var (language-expression printf-spec) 3))
  #;(assert (equal? v1 (printf-lang (cons " " nil))))
  (define p1 ((language-link printf-spec) c1 v1))
  (define b1 ((language-evaluate printf-spec) p1))
  
  #;(printf "spec: ~a~n" (increment-spec p1 b1))

  (define sol (synthesize
               #:forall c1
               #:assume (assert ((printf-uncurry valid-printf-spec-program?) p1))
               #:guarantee (assert (increment-spec p1 b1))
               ))
  (if (unsat? sol)
      (displayln "Synthesis failed")
      (printf "Synthesis succeeded: ~a~n" (concretize v1 sol))
      )
  )
#;(find-increment-gadget-manual)
