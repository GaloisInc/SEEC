#lang seec
(require seec/private/language)

(define-language lang
  (boollist ::= list<boolean>)
  #;(list-of-list ::= list<list<boolean>>)
  (boollist2 ::= bnil (bcons boolean boollist2))
  )

(define list-ex-2 (lang (cons #t (cons #f nil))))
(define list-ex-1 (lang (cons #t nil)))
(define list-ex-0 (lang nil))

(match list-ex-2
  [(lang nil) #t]
  [(lang (cons boolean boollist)) #t]
  )


(define (alltrue l)
  (match l
    [(lang nil) #t]
    [(lang (cons b:boolean m:list<boolean>)) (and (bonsai-boolean-value b) (alltrue m))]
    ))
(alltrue list-ex-2)


(define (bool-list-length l)
  (match l
    [(lang nil) 0]
    [(lang (cons boolean l+:list<boolean>)) (+ 1 (bool-list-length l+))]
    ))

(bool-list-length list-ex-2)
(define list-symbolic (lang boollist 5))
(define list-ex-2-2 (lang (bcons #t (bcons #f nil))))
list-ex-2-2
(define list2-symbolic (lang boollist2 5))
list2-symbolic
