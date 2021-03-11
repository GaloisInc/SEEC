#lang seec
(require seec/private/util)
(require "tinyC.rkt"
         "tinyC-test.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt")
(require rosette/lib/value-browser) ; debugging

(define (synthesize-arg-tinyC)
  (let ([g (find-ctx-gadget tinyC-lang
                            (λ (p tr) (equal? tr (seec-singleton 3)))
                            #:expr (list->seec simple-call-example)
                            #:context-bound 4
                            )])
    (display-gadget g displayln))
  ; Should find (seec-singleton 3)
  )
#;(synthesize-arg-tinyC)

(define (synthesize-args-factorial)
  (parameterize ([debug? #t]
                 [max-fuel 100])
    (define-symbolic* val0 integer?)
    (let* ([symbolic-args (list->seec (list val0))]
           [g (find-ctx-gadget tinyC-lang
                              (λ (p tr) (equal? tr (seec-singleton 6)))
                              #:expr (list->seec factorial)
;                              #:context-bound 2
                              #:context symbolic-args
;                              #:context (seec-singleton 3)
                              )])
      (display-gadget g displayln)))
  ; Should find (seec-singleton 3)
  )
#;(synthesize-args-factorial) ; Currently does not finish symbolic execution, at
                              ; least for a long time. TODO: optimize execution
                              ; when running up against fuel



(define (synthesize-arg-tinyA)
  ; Try this computation with an arglist of a fixed length
  #;(define symbolic-args (tinyA trace 3))
  (define-symbolic* val1 integer?)
  (define-symbolic* val2 integer?)
  (define-symbolic* val3 integer?)
  ; With argument list of length >1, does not terminate

  (define symbolic-args (list->seec (list val1)))
  #;(define symbolic-args (tinyA trace 3))
  #;(define symbolic-args (list->seec (list val2 val3)))

  (parameterize ([debug? #t]
                 [max-fuel 10] ; with a low enough fuel, can still synthesize
                              ; args even with wrong # of arguments
                 )
    (let ([g (find-ctx-gadget tinyA-lang
                          (λ (p tr) (equal? tr (seec-singleton 3)))
                          #:expr ((compiler-compile tinyC-compiler) (list->seec simple-call-example))
                          #:context (tinyA (,symbolic-args nil))
                          #:context-bound 3
                          )])
      (display-gadget g displayln)))
  )
; Expected: (seec-singleton 3)
#;(synthesize-arg-tinyA)

  
(define (synthesize-weird-behavior-call)
  (parameterize ([debug? #t]
                 [max-fuel 10])
    (let ([g (find-weird-computation tinyC-compiler
                                     (list->seec simple-call-example)
                                     #:target-context-bound 2
                                     )])
      (display-weird-behavior g displayln))))
; Expected: No weird behavior found
#;(synthesize-weird-behavior-call)

(define (synthesize-weird-behavior-factorial)
  (parameterize ([debug? #t]
                 [max-fuel 4]) ; Should increase bound to allow feasibility
    (let ([g (find-weird-computation tinyC-compiler
                                     (list->seec factorial)
                                     #:target-context-bound 3
                                     )])
      (display-weird-behavior g displayln))))
#;(synthesize-weird-behavior-factorial)
; Expected: no weird behavior found



(define (synthesize-input-password)
  (parameterize ([debug? #t])
    (define-symbolic* x integer?)
    (define input (list->seec (list x)))
    (let* ([g (find-ctx-gadget tinyA-lang
                               ; Synthesize an input that gains authorization
                               (λ (p tr) (equal? tr (seec-singleton 1)))
                               #:expr ((compiler-compile tinyC-compiler) (list->seec password-checker))
                               #:context (tinyA (nil (cons ,input nil)))
                               )])
      (display-gadget g displayln))))
#;(synthesize-input-password)
; Should synthesize 42 -- the fixed password value

(define (synthesize-input-password-2)
  (define-symbolic* x integer?)
  (define-symbolic* y integer?)
  (define input (list->seec (list x y)))
  ; Note that when using an input, symbolic execution does not terminate
  #;(define input (cond
                  [(havoc!) (seec-singleton x)]
                  [else     (list->seec (list x y))]))
  (parameterize ([debug? #t])
    (let ([g (find-ctx-gadget tinyA-lang
                               ; Synthesize an input that gains authorization
                               (λ (p tr) (equal? tr (seec-singleton 1)))
                               #:expr ((compiler-compile tinyC-compiler) (list->seec password-checker))
                               #:context (tinyA (nil (cons ,input nil)))
                               )])
      (display-gadget g displayln))))
#;(synthesize-input-password-2)
; Should find x=y

(define (synthesize-input-password-3)
  (define-symbolic* x integer?)
  (define-symbolic* y integer?)
  (define-symbolic* z integer?)
  (define input (list->seec (list x y z)))
  (parameterize ([debug? #t])
    (let ([g (find-ctx-gadget tinyA-lang
                               ; Synthesize an input that gains authorization
                               (λ (p tr) (equal? tr (seec-singleton 1)))
                               #:expr ((compiler-compile tinyC-compiler) (list->seec password-checker))
                               #:context (tinyA (nil (cons ,input nil)))
                               )])
      (display-gadget g displayln))))
#;(synthesize-input-password-3)
; Should find EITHER x=y OR z=0

(define (synthesize-input-arg-password)
  (define-symbolic* pswd integer?)
  (define-symbolic* x integer?)
  (define-symbolic* y integer?)
  (define args  (seec-singleton pswd))
  (define input (list->seec (list x y)))
  (parameterize ([debug? #t])
    (let ([g (find-ctx-gadget tinyA-lang
                               ; Synthesize an input that gains authorization
                               (λ (p tr) (equal? tr (seec-singleton 1)))
                               #:expr ((compiler-compile tinyC-compiler)
                                       (list->seec password-checker-with-arg))
                               #:context (tinyA (,args (cons ,input nil)))
                               #:forall pswd
                               )])
      (display-gadget g displayln))))
#;(synthesize-input-arg-password)
; Should find (any,1)


(define (synthesize-weird-behavior-password)
  (define-symbolic* x integer?)
  (define-symbolic* y integer?)
  (define input (list->seec (list x y)))

  (parameterize ([debug? #f]
                 [max-fuel 10])
    (let ([g (find-weird-behavior tinyC-compiler
                                     #:source-expr (list->seec password-checker)
                                     ; I think we need to provide both the
                                     ; source and target contexts so symbolic
                                     ; execution will terminate
                                     #:source-context (tinyC (nil (cons ,input nil)))
                                     #:target-context (tinyA (nil (cons ,input nil)))
                                     #:forall (list)
                                     #:fresh-witness #f
                                     )])
      (display-weird-behavior g displayln))))
(synthesize-weird-behavior-password)
;
; Expected:
;
; Expression (("main" (("candidate" int) (("password" int) (("auth" int)))) ((ASSIGN "auth" 0) ((ASSIGN "password" 42) ((INPUT (& "candidate")) ((IF (= "candidate" "password") (ASSIGN "auth" 1) SKIP) ((CALL "guarded-fun" ("auth")))))))) (("guarded-fun" (("auth" int)) ((OUTPUT "auth")))))
;  has emergent behavior (1)
;  witnessed by target-level context (((0 (0))))
