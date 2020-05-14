#lang seec

(require seec/private/string)
(require (only-in racket/base integer->char))

(define-language constants
  (const ::= (BOOL boolean) num (STR string) (CHAR char))
  (num ::= (NAT natural))
)


#|
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
|#


#|
(define (any-lang x)
  (match x
    [(constants any) #t]
    ))
(any-lang b)
|#


(define (synthesize-specific-string)
  (define s (new-symbolic-string 1))
  s
  (string "x")
  (define sol (verify (assert (not (equal? s (string "x"))))))
  sol
)

; TODO: fix pattern matching for matching against a concrete string?
#;(match (constants (STR "hi"))
  [(constants (STR "hi")) #t]
  [_ #f]
  )

(define (synthesize-string-in-lang)
  (displayln (constants (CHAR #\x)))

  (define symbolic-exp (constants const 5))
  #;(displayln symbolic-exp)
  #;(define sol (verify (assert (not (equal? symbolic-exp (constants (CHAR #\x)))))))
  (define (is-char)
    (match symbolic-exp
      #;[(constants (STR s:string)) #t]
      [(constants (CHAR c:char)) #t]
      #;[(constants (BOOL b:boolean)) #t]
      [_ #f]))
  (define (is-bool)
    (match symbolic-exp
      [(constants (BOOL b:boolean)) #t]
      [_ #f]))

  (assert (is-char))
  (define sol (verify (assert #f)))
  sol
  )
(synthesize-string-in-lang)

