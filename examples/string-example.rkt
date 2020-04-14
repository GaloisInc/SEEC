#lang seec

(require seec/private/string)
(require (only-in racket/base integer->char))

(define-language constants
  (const ::= (BOOL boolean) (NAT natural) (STR string) (CHAR char))
)


(define five (constants (NAT 5)))
(define hi (constants (STR "hi")))
(print-char (char #\x))
(bonsai-char #\x)
(define c (constants (CHAR #\x)))
hi
c

(match (bonsai-char #\x)
  [(bonsai-string x) #t]
  [(bonsai-integer x) #f]
  [(bonsai-char x) #f]
  )
(match c
  [(constants (BOOL b:boolean)) b]
  [(constants (NAT n:natural)) n]
  [(constants (STR s:string)) s]
  [(constants (CHAR c:char)) c]
  )
