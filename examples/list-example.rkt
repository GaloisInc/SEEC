#lang seec
#;(require seec/private/language)
(require rosette/lib/value-browser)

(define-grammar lang
  (boollist ::= list<boolean>)
  #;(list-of-list ::= list<list<boolean>>)
  (boollist2 ::= bnil (bcons boolean boollist2))
  )

(define list-ex-2 (lang (cons #t (cons #f nil))))
(define list-ex-1 (lang (cons #t nil)))
(define list-ex-0 (lang nil))

#;(match list-ex-2
  [(lang nil) #t]
  [(lang (cons boolean boollist)) #t]
  )


(define (alltrue l)
  (match l
    [(lang nil) #t]
    [(lang (cons b:boolean m:list<boolean>)) (and b (alltrue m))]
    ))
#;(alltrue list-ex-2)


(define (bool-list-length l)
  (match l
    [(lang nil) 0]
    [(lang (cons boolean l+:list<boolean>)) (+ 1 (bool-list-length l+))]
    ))


(define (head l)
  (match l
    [(lang nil) #f]
    [(lang (cons x:any list<boolean>)) x]))
(head list-ex-1)


(define (length l)
  (match l
    [(lang nil) 0]
    [(lang (cons any l+:list<any>)) (+ 1 (length l+))]
    ))
(length list-ex-2)

#;(bool-list-length list-ex-2)
(define list-symbolic (lang boollist 3))
#;(define list-ex-2-2 (lang (bcons #t (bcons #f nil))))
#;list-ex-2-2
(define list2-symbolic (lang boollist2 5))
#;list2-symbolic

#;(seec-length list-ex-2)
#;list-ex-1
#;list-ex-2
#;(define list-ex-3 (seec-append list-ex-1 list-ex-2))
#;(length list-ex-3)

#;(printf "bool-list-length: ~a~n" (bool-list-length list-symbolic))
#;(printf "seec-length: ~a~n" (seec-length list-symbolic))
#;(render-value/window list-symbolic)

#;(verify (assert (<= 0 (bool-list-length (seec-append list-symbolic list-symbolic)) 4)))

(define (tail l)
  (match l
    [(lang (cons any l+:list<boolean>)) l+]
    ))

(begin
 (define sol (synthesize
              #:forall '()
              #:guarantee (assert (equal? (seec-length list-symbolic)
                                          (+ 1 (seec-length (seec-tail list-symbolic)))))
              ))
 (if (unsat? sol)
     (displayln "Failed to synthesize")
     (begin
       (displayln "Synthesis succeeded")
       (define list-concrete (concretize list-symbolic sol))
       (displayln list-concrete)
       ))
 )
