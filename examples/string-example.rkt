#lang seec

(require seec/private/string)
(require (only-in racket/base integer->char))

(define-language constants
  (const ::= (BOOL boolean) num (STR string) (CHAR char))
  (num ::= (NAT natural))
)


(define b (constants (BOOL #f)))
(define five (constants (NAT 5)))
(define hi (constants (STR "hi")))
;(print-char (char #\x))
;(bonsai-char #\x)
(define c (constants (CHAR #\x)))
;hi
;c

#;(match (bonsai-char #\x)
  [(bonsai-string x) #t]
  [(bonsai-integer x) #f]
  [(bonsai-char x) #f]
  )

(match b
  #;[(constants x:num) x]
  [(constants (BOOL b:boolean)) b]
  #;[(constants (STR s:string)) s]
  #;[(constants (CHAR c:char)) c]
  )
