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
         compile-fmt
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
     (ll-cons (compile-expr e) (compile-arglist l+))]
    ))

(define/contract (compile-mem m)
  (-> safe:mem? unsafe:mem?)
  (match m
    [(safe:printf-lang mnil) (unsafe:printf-lang nil)]
    [(safe:printf-lang (mcons x:ident v:val m+:mem))
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

(define/contract (compile-fmt f)
  (-> safe:fmt? unsafe:fmt?)
  (match f
    [(safe:printf-lang nil) f]
    [(safe:printf-lang (cons s:string f+:fmt))
     (unsafe:printf-lang (cons ,s ,(compile-fmt f+)))]
    [(safe:printf-lang (cons (% p:parameter w:width ftype:fmt-type)
                             f+:fmt))
     (unsafe:printf-lang (cons (% (,p (,w ,ftype))) ,f+))]
    ))

(define/contract (compile-program p)
  (-> safe:printf-program? unsafe:printf-program?)
  (unsafe:make-program (compile-fmt (safe:program->fmt p))
                       (compile-arglist (safe:program->arglist p))
                       (compile-config  (safe:program->config p))
                       ))

(define/contract (compile-behavior b)
  (-> safe:behavior? unsafe:behavior?)
  (unsafe:printf-lang (,(safe:behavior->trace b)
                       ,(compile-config (safe:behavior->config b))
                       )))

