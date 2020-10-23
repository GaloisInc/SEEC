#lang seec
(require (file "alist-lang.rkt"))
(require (file "linked-list-lang.rkt"))
(require (file "linked-alist-compiler.rkt"))
(provide ex1
         ex2
         ex3)
(require seec/private/framework)

; Do we introduced any new behaviors by compiling store and interactions to linked-list?
; ERR: ran for close to 15 minutes...
(define (ex1)
  (find-changed-component alist-to-ll-compiler))
#;(begin
  (displayln "Are all behaviors preserved through alist->ll compilation?")
  (display-changed-component (ex1) displayln))

; Can we introduce any new behaviors by changed the free pointer of the compiled linked-list
(define (ex2)
  (find-changed-component alist-to-attacked-ll-compiler))
#;(begin
  (displayln "Can we induced a changed behavior by modifying the free-list pointer?")
  (define q2 (ex2))
  (display-language-witness-alist (first q2))
  (display-language-witness-ll (second q2)))

#;(begin
  #;(define sol (find-weird-behavior
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
(define (ex3)
  (find-changed-component alist-to-attacked-ll-compiler
                                       #:target-context-where (lambda (v1 c2) (not (alist-in v1 (complete-interaction-ll-lookup (aci->ci c2)))))
                                       #:target-behavior-where (lambda (v1 c1 c2 b2) (alist-in v1 b2))))
#;(begin
    (displayln "Can we find an attack that 1) doesn't require private information 2) reveals private information?")
    (define q3 (ex3))
    (display-language-witness-alist (first q3))
    (display-language-witness-ll (second q3)))

