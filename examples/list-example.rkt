#lang seec

(define-language lang
  (boollist ::= list<boolean>)
  #;(list-of-list ::= list<list<boolean>>)
  )

#;(define list-ex (lang (cons #t (cons #f nil))))
(define list-ex (lang nil))

(define (alltrue l)
  (match l
    [(lang nil) #t]
    [(lang boollist) #t]
    [(lang (cons b:boolean boollist)) (and b #;(alltrue m))]
    [(lang other:boollist) other]
    [(lang other:boolean) other]
    ))
(alltrue list-ex)

#;(define (bool-list-length l)
  (match l
    [(lang nil) 0]
    [(lang (cons b:boolean m:bool-list)) (+ 1 (bool-list-length m))]
    ))

#;(bool-list-length list-ex)
