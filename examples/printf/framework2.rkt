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

(define (printf-program? p)
  (and (pair? p)
       (context? (car p))
       (fmt? (cdr p))
       ))
(define/contract (program->fmt p)
  (-> printf-program? fmt?)
  (cdr p))
(define/contract (program->config p)
  (-> printf-program? config?)
  (context->config (car p)))
(define/contract (bv-add-integer b x)
  (-> bv? integer? bv?)
  #;(printf "(bv-add-integer ~a ~a)~n" b x)
  (bvadd b (bonsai-bv-value (integer->bonsai-bv x)))
  )




(define/contract (add-constant-spec c p res)
  (-> integer? printf-program? behavior? boolean?)
  (printf "(add-constant-spec ~a ~a ~a)~n" c p res)
  (let* ([acc (conf->acc (program->config p))]
         [acc+ (conf->acc (behavior->config res))]
         )
    (equal? acc+ (bv-add-integer acc c))
    ))



(define find-gadget-custom
  (λ (lang ; SEEC langauge
      #:valid [valid-program (λ (p) #t)]
      spec ; program -> behavior -> boolean
      #:expr-bound    [bound-e #f]
      #:context-bound [bound-c #f]
      #:context [ctx (make-symbolic-var (language-context lang) bound-c)]
      #:context-constraint [ctx-constraint (λ (x) #t)] ; (-> context? boolean?)
      #:expr    [e   (make-symbolic-var (language-expression lang) bound-e)]
      #:expr-constraint [e-constraint (λ (x) #t)] ; (-> expr? boolean?)
      #:forall  [vars ctx] ; any term containing symbolic variables to be quantified over
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
                                                (ctx-constraint ctx)
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
  #;(set-bitwidth 4 3)
  (define g (find-gadget-custom printf-spec
                         ((curry add-constant-spec) c)
;                         #:expr-bound 3
;                         #:expr (printf-lang (cons (% (0 $) 5 s) nil))
                         #:expr-constraint (λ (fmt) (equal? fmt
                                                            (printf-lang (cons (% (0 $) 5 s) nil))))
;                         #:context (printf-lang ((cons "" nil)
;                                                 ((bv 0)
;                                                  mnil)))
                         #:context-constraint (λ (ctx)
                            (equal? (context->arglist ctx) (printf-lang (cons "" nil))))
                         #:forall '()
                         ))
  (display-gadget g displayln)
  )
(find-add-constant-gadget 5)
