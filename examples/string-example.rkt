#lang seec

(require seec/private/string)
(require (only-in racket/base integer->char))

(define-language constants
  (const ::= (BOOL boolean) num (STR string) (CHAR char))
  (num ::= (NAT natural))
)


(define b (constants (BOOL #f)))
(define five (constants (NAT 5)))


(define hi-desired (constants (STR "hi")))
(define c-desired (constants (CHAR #\x)))
(displayln hi-desired)
(displayln c-desired)
(match hi-desired
  [(constants (STR s:string)) (print-string (bonsai-string-value s))]
  )
(match c-desired
  [(constants (CHAR c:char)) (displayln c)]
  )



#|
(define (any-lang x)
  (match x
    [(constants any) #t]
    ))
(any-lang b)
|#
