#lang seec
(require (file "alist-lang.rkt"))
(require (file "linked-list-lang.rkt"))
(require (file "linked-alist-compiler.rkt"))
(require (only-in racket/base
                  make-parameter
                  parameterize))
(provide ex1
         ex2
         ex3)
(require seec/private/framework)

; Do we introduced any new behaviors by compiling store and interactions to linked-list?
; ERR: with bound=4, rec-bound=10, took 14 sec
;      with bound=6, took 43 sec
(define (ex1)
  (find-changed-component alist-to-ll-compiler
                          #:source-expression-size 6))
#;(begin
  (displayln "Are all behaviors preserved through alist->ll compilation?")
  (time (display-changed-component (ex1) displayln))
  )

; Can we introduce any new behaviors by changed the free pointer of the compiled linked-list
;
; With rec-bound=5, 6.5 min
(define (ex2)
  (parameterize ([rec-bound 5])
    (find-changed-component alist-to-attacked-ll-compiler
                            #:source-expression-size 4)))
#;(time (begin
  (displayln "Can we induced a changed behavior by modifying the free-list pointer?")
  (define q2 (ex2))
  (display-language-witness-alist (first q2))
  (display-language-witness-ll (second q2))))

#;(begin
  #;(define sol (find-weird-computation-backend
   alist-to-attacked-ll-compiler
;   #:source-expr _ ; symbolic
;   #:source-context _ ; symbollic
;   #:target-context _ ; symbolic
   #:fresh-witness #f
   #:forall (list )
   #:capture-nondeterminism #f
   ))
  (display-weird-behavior sol displayln)
  )


; Can we find interesting new behaviors?
;
; Note: with source-expression-size=4, rec-bound=10, 80 min
;       with source-expression-size=4, rec-bound=5, 10 min
(define (ex3)
  (parameterize ([rec-bound 5])
  (find-changed-component alist-to-attacked-ll-compiler
                          #:source-expression-size 4
                          #:target-context-where (lambda (v1 c2) (not (alist-in v1 (complete-interaction-ll-lookup (aci->ci c2)))))
                          #:target-behavior-where (lambda (v1 c1 c2 b2) (alist-in v1 b2))))
  )
#;(begin
    (displayln "Can we find an attack that 1) doesn't require private information 2) reveals private information?")
    (define q3 (ex3))
    (display-language-witness-alist (first q3))
    (display-language-witness-ll (second q3)))
