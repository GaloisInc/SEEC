#lang seec

(require seec/private/string)
(require (only-in racket/base integer->char))

(define-language constants
  (const ::= (BOOL boolean) num (STR string) (CHAR char))
  (num ::= (NAT natural))
)


(define b (constants (BOOL #f)))
(define five (constants (NAT 5)))


; Previously, I was able to define
(define hi-desired (constants (STR "hi")))
(define c-desired (constants (CHAR #\x)))
; Now, if I try to use these structures, I get an error
;(displayln hi-desired)
;(displayln c-desired)
#;(match hi-desired
  [(constants (STR s:string)) (print-string s)]
  )
#;(match c-desired
  [(constants (CHAR c:char)) (print-char c)]
  )

; Instead, I can construct them by wrapping the `string` and `char` functions,
; which does some magic in `string.rkt`.
(define hi-current (constants (STR ,(string "hi"))))
(define c-current (constants (CHAR ,(char #\x))))
(displayln hi-current)
(displayln c-current)

; However, pattern matching doesn't work
#;(match hi-current
  [(constants (STR s:string)) (print-string s)]
  )
#;(match c-current
  [(constants (CHAR c:char)) (print-char c)]
  )













#|
(define (any-lang x)
  (match x
    [(constants any) #t]
    ))
(any-lang b)
|#
