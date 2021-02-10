#lang seec
(require (file "set.rkt"))
(provide (all-defined-out))

(define (ex1) (find-changed-component abstract-to-concrete #:count 3))
#;(begin
  (displayln "Trying to find a trace with different behavior under compilation")
  (let* ([witnesses (time (ex1))])
    (for-each (lambda (w) (begin
                            (displayln "Found witness: ")
                            (display-changed-behavior w displayln))) witnesses)))


(define (ex2) (find-weird-component abstract-to-buggyconcrete
                                    #:source-context-bound 2
                                    #:target-context-bound 2))
#;(begin
  (displayln "Trying to find a trace with weird behavior under buggy compilation")
  (display-weird-component (ex2) displayln)
  )
; Result:
; Expression ((insert 4) ((insert 4) ((remove 4) (select))))
; has emergent behavior (4)
; witnessed by target-level context *null*

(define (ex3) (find-weird-component abstract-to-concrete
                                    #:source-context-bound 2
                                    #:target-context-bound 2))
#;(begin
    (displayln "Trying to find a trace with weird behavior under correct compilation")
    (display-weird-component (ex3) displayln))
; Result:
; No weird behavior found


; a program prog (for concrete-two) is a pair of an expression (in this case, a
; context), paired with a context (in this case, a set).
; res is a pair of a trace and a set
(define (add1-concrete? prog res)
  (match (cons prog res)
    [(cons (cons _ init-set) (cons _ res-set))
     (equal? (seec-length res-set)
             (+ 1 (seec-length init-set)))
     ]
    [_ #f]
    ))

(define (ex4) (find-gadget concrete-with-state add1-concrete?))
#;(begin
  (displayln "Trying to find a +1 gadget")
  (display-gadget (ex4) displayln))
