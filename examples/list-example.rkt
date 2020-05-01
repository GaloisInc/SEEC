#lang seec
(require seec/private/language)

(define-language lang
  (boollist ::= list<boolean>)
  #;(list-of-list ::= list<list<boolean>>)
  )

(define list-ex-2 (lang (cons #t (cons #f nil))))
(define list-ex-1 (lang (cons #f nil)))
(define list-ex-0 (lang nil))

(match list-ex-2
  [(lang nil) #t]
  [(lang (cons boolean boollist)) #t]
  )



(define (alltrue l)
  (match l
    [(lang nil) #t]
    [(lang (cons b:boolean m:list<boolean>)) b #;(and b (alltrue m))]
    ))
(alltrue list-ex-1)


(define (bool-list-length l)
  (match l
    [(lang nil) 0]
    [(lang (cons b:boolean l+:list<boolean>)) (+ 1 (bool-list-length l+))]
    ))

(bool-list-length list-ex-0)
