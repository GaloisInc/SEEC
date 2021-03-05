#lang seec
(require seec/private/util)
(require "tinyC.rkt"
         "tinyC-test.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt")
(require rosette/lib/value-browser) ; debugging

#;(define prog (list->seec simple-call-example))
#;(define inputs (tinyC trace 3))
#;(define inputs (seec-singleton 3))
#;(parameterize ([debug? #t])
  (tinyC:display-state (tinyC:run+ prog inputs)))

#;(let ([g (find-gadget tinyC-lang
                      (λ (p tr) (equal? tr (seec-singleton 3)))
                      #:expr (list->seec simple-call-example)
                      #:context-bound 4
                      #:fresh-witness #f
                      #:forall (list )
                      )])
  (display-gadget g displayln))
; Should find (seec-singleton 3)

#;(let ([g (find-ctx-gadget tinyC-lang
                          (λ (p tr) (equal? tr (seec-singleton 3)))
                          #:expr (list->seec simple-call-example)
                          #:context-bound 4
                          #:count 2
                          )])
  (display-gadget g displayln))


; Try this computation with an arglist of a fixed length
#;(define symbolic-args (tinyA trace 3))
(define-symbolic* val1 integer?)
(define-symbolic* val2 integer?)
(define-symbolic* val3 integer?)
; With argument list of length >1, does not terminate


#;(let-values ([(g mem) (tinyC->tinyA-program (list->seec simple-call-example)
                                            100)])
  (render-value/window mem)) ; At this stage: totally concrete
#;(parameterize ([debug? #t])
  (define compiled-prog ((language-link tinyA-lang)
                         symbolic-args
                         ((compiler-compile tinyC-compiler) (list->seec simple-call-example))
                         ))
  (render-value/window (tinyA:state-memory compiled-prog))
  (displayln "done"))
                       
#;(define symbolic-args (list->seec (list val1)))
#;(define symbolic-args (tinyA trace 3))
(define symbolic-args (list->seec (list val2 val3)))

(parameterize ([debug? #t])
  (let ([g (find-ctx-gadget tinyA-lang
                          (λ (p tr) (equal? tr (seec-singleton 3)))
                          #:expr ((compiler-compile tinyC-compiler) (list->seec simple-call-example))
                          #:context symbolic-args
                          #:context-bound 3
                          )])
    (display-gadget g displayln)))
