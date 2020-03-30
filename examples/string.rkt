#lang seec

(require (only-in racket/base
                  [string->list racket/string->list]
                  [char->integer racket/char->integer]
                  [integer->char racket/integer->char]
                  [list->string racket/list->string]
                  ))
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(require (only-in racket/contract listof))
(provide char?
         string?
         symbolic-string?
         print-char
         print-string
         mk-char
         mk-string
         mk-symbolic-char
         mk-symbolic-string
         string-length
         number->string
         string-append
         )

;; A character is just a number between 0 and 256
(define (char? c) (<= 0 c 256))
;; A string is just a list of characters
(define (string? s) (listof char?))

(define (symbolic-string? s)
  (ormap term? s))

(define (string-append s1 s2) (append s1 s2))

(define (print-char c)
  (if (term? c) ; if c is a symbolic term, then don't do anything special
      c
      (racket/integer->char c)
      ))
(define (print-string s)
  (if (symbolic-string? s)
      s
      (racket/list->string (map print-char s))))

; You can construct a symbolic character using
; (define-symbolic c char?)
; or construct a concrete character from a racket char using 
; (define c (mk-char c0))
(define (mk-char c)
  (racket/char->integer c))
(define (mk-string s)
  (map mk-char (racket/string->list s)))
(define (char->string c)
  (list c))

(define (mk-symbolic-char)
  (define-symbolic c integer?)
  (assert (<= 0 c 256))
  c)
; create a symbolic string of length len
(define (mk-symbolic-string len)
  (if (<= len 0)
      '()
      (cons (mk-symbolic-char) (mk-symbolic-string (- len 1)))
      ))

#|
(mk-char #\x)
(print-char (mk-char #\x))
(mk-string "Hello, world!")
(symbolic-string? (mk-string "Hello, world!"))
(print-string (mk-string "Hello, world!"))
(mk-symbolic-char)
(print-char (mk-symbolic-char))
(mk-symbolic-string 5)
(symbolic-string? (mk-symbolic-string 5))
(print-string (mk-symbolic-string 5))
|#

  
;; functions on strings ;;
(define (string-length s) (length s))

; convert a number into a string encoding the number
#|(define (number->string n)
  (if (term? n)
      ; if n is symbolic...
      ?
      ; else...
      (racket/number->string n)
|#

;; given a number n between 0 and 9 inclusive,
;; output the character corresponding to n
;; (since 0 starts at 48, increase from there)
(define (digit->char n)
  (if (<= 0 n 9)
      (+ n 48)
      (raise-argument-error 'digit->char
                            "digit between 0 and 9"
                            n)))

(define (number->string n)
  (cond
    [(negative? n) (string-append (mk-string "-") (number->string (* -1 n)))]
    [(<= 0 n 9) (char->string (digit->char n))]
    [else 
     ;; n = 10*q + r
     (let* ([q (quotient n 10)]
            [r (remainder n 10)]
            )
       (string-append (number->string q) (char->string (digit->char r)))
       )]))
