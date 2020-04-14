#lang seec

(define-language constants
  (const ::= (BOOL boolean) (NAT natural) (STR string))
)

(define five (constants (NAT 5)))
(define hi (constants (STR "hi")))

(match (bonsai-string "Hello")
  [(bonsai-string x) #t]
  [(bonsai-integer x) #f]
  )
(match five
  [(constants (BOOL b:boolean)) b]
  [(constants (NAT n:natural)) n]
  [(constants (STR s:string)) s]
  )
