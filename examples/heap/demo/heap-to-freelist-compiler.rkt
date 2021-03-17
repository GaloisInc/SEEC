#lang seec
(set-bitwidth 4)

(require racket/format)
(require seec/private/util)
(require seec/private/monad)

;(require racket/contract)
(provide (all-defined-out))
(require (file "heap-lang.rkt"))
(require (file "freelist-lang.rkt"))

(define/debug #:suffix (compile-into-freelist fuel h p )
    (if (< fuel 1)
        #f
        (match p
          [(heap-model null)
           (freelist nil)]
          [(heap-model n:natural)       
           (let* ([new-p (nth h n)]
                  [rest (compile-into-freelist (- fuel 1) h new-p)])
             (if (and new-p
                      rest)
                 (freelist (cons ,n ,rest))
                 #f))])))

(define (compile-heap-to-freelist s)
  (match s
    [(heap-model (any h:heap p:pointer))
                 (compile-into-freelist 3 h p)]))



(define (compile-action a)
  (match a
    [(heap-model (free h:heap-loc))
     (freelist (free ,h))]
    [(heap-model (alloc any))
     (freelist alloc)]
    [(heap-model a:action)
     *fail*]))


(define (compile-interaction i)
  (match i
    [(heap-model nil)
     (freelist nil)]
    [(heap-model (cons a:action i+:interaction))
     (let ([af (compile-action a)])
       (if (failure? af)
           (compile-interaction i+)
           (freelist (cons ,af ,(compile-interaction i+)))
           ))]))



(define-compiler heap-to-freelist
  #:source heap-lang
  #:target freelist-lang
  #:behavior-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:context-relation (lambda (s f) (equal? (compile-heap-to-freelist s) f))
  #:compile compile-interaction)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (display-heap-to-freelist witnesses)
  (if witnesses     
      (let* ([lwl-heap (unpack-language-witness (first witnesses))]
             [lwl-freelist (unpack-language-witness (second witnesses))])
        (displayln "State: ")
        (display-state (second lwl-heap))
        (displayln "... has freelist:")
        (displayln (second lwl-freelist))
        (display "... and steps, under interaction ")
        (display (first lwl-heap))
        (displayln ", to state: ")
        (display-state (fourth lwl-heap))
        (displayln "... with freelist: ")
        (print (compile-heap-to-freelist (fourth lwl-heap)))
        (displayln "")
        (displayln "... with emergent behavior: ")
        (print (fourth lwl-freelist))
        (displayln ""))
      (displayln "No example found")))
