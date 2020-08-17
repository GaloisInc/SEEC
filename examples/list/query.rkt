#lang seec
(require (file "alist-lang.rkt"))
(require (file "linked-list-lang.rkt"))
(require (file "linked-alist-compiler.rkt"))

(define (ex1)
  (begin 
    (displayln "Are all behaviors preserved through alist->ll compilation?")
    (define q1 (find-changed-component alist-to-ll-compiler))
    (display-changed-component q1 displayln)))

(define (ex2)
  (begin
    (displayln "Can we induced a changed behavior by modifying the free-list pointer?")
    (define q2 (find-changed-component alist-to-attacked-ll-compiler))
    (display-language-witness-alist (first q2))
    (display-language-witness-ll (second q2))))

(define (ex3)
  (begin
    (displayln "Can we find an attack that 1) doesn't require private information 2) reveals private information?")
    (define q3 (find-changed-component alist-to-attacked-ll-compiler
                                              #:target-context-where (lambda (v1 c2) (not (alist-in v1 (complete-interaction-ll-lookup (aci->ci c2)))))
                                              #:target-behavior-where (lambda (v1 c1 c2 b2) (alist-in v1 b2))))
    (display-language-witness-alist (first q3))
    (display-language-witness-ll (second q3))))

; Do we introduced any new behaviors by compiling store and interactions to linked-list?
(ex1)
; Can we introduce any new behaviors by changed the free pointer of the compiled linked-list?
(ex2)
; Can we find interesting new behaviors? 
(ex3)
