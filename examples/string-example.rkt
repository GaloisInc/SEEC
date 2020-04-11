#lang seec
(require seec/private/string)

(require seec/private/match)
(require (for-syntax syntax/parse))


(define-language constants
  (const ::= (BOOL boolean) (NAT natural) (STR string))
)

(constants (NAT ,(bonsai-integer 5)))
#;(constants (STR ,(bonsai-string (string "hi"))))

(constants (STR ,(bonsai-string* "hi")))

(define-match-expander is-a-string
  (lambda (stx)
    (syntax-parse stx
      [(_ x) #'(? bonsai-string? (bonsai-string x))])))

(match (bonsai-string (string "Hello"))
  [(is-a-string x) #t])

#;(match (constants (NAT 4) #;(STR ,(bonsai-string* "Hello")))
  [(constants (BOOL b:boolean)) b]
  [(constants (NAT n:natural)) n]
  [(constants (STR s:string)) s]
  )
