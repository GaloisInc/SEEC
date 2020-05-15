#lang rosette/safe

(require (only-in racket/base
                  [string->list racket/string->list]
                  [char->integer racket/char->integer]
                  [integer->char racket/integer->char]
                  [list->string racket/list->string]
                  [string? racket/string?]
                  [string-append racket/string-append]
                  ))
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(provide char?
         string?
         symbolic-string?
         print-char
         print-string
         char
         string
         new-symbolic-char
         new-symbolic-char*
         new-symbolic-string
         new-symbolic-string*
         string-length
         number->string
         string-append
         string
         )

;; A (printable, ASCII) character is just a number between 32 and 126
(define (char? c) (and (integer? c) (<= 32 c 126)))

;; A string is just a list of characters
(define (string? s) (and (list? s)
                         (andmap char? s)))

(define (symbolic-string? s)
  (ormap term? s))

(define string-append append)

(define (char->racket c)
  (if (term? c) ; if c is a symbolic term, then don't do anything special
      c
      (racket/integer->char c)
      ))
(define (print-char c) (char->racket c))
(define (print-string s)
  (if (symbolic-string? s)
      s
      (racket/string-append "\"" (racket/list->string (map char->racket s)) "\"")))

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


(define (char c) (mk-char c))
;  (cond 
;    [(char? c) c]
;    [(not (term? c)) (mk-char c)]
;    ))

; construct either a concrete OR symbolic string
; if the input is already a rosette string, do nothing
; if the input is a concrete string, apply mk-string
(define (string s)
  (cond
    [(string? s) s]
    [(not (term? s)) (mk-string s)]
    ))

(define (new-symbolic-char)
  (begin
    (define-symbolic c integer?)
    (assert (char? c))
    c))
(define (new-symbolic-char*)
  (begin
    (define-symbolic* c integer?)
    (assert (char? c))
    c))
; create a symbolic string of length len
; len must not be symbolic or termination could occur
(define (new-symbolic-string len)
  (letrec ([make-string (lambda (n)
                          (if (<= n 0)
                              '()
                              (cons (new-symbolic-char*) (make-string (- n 1)))))]
           )
    (make-string len)))
(define (new-symbolic-string* len)
  (letrec ([c (new-symbolic-char*)]
           [make-string (lambda (n)
                          (if (<= n 0)
                              '()
                              (cons c (make-string (- n 1)))))]
           )
    (make-string len)))



  
;; functions on strings ;;
(define (string-length s) (length s))

#;(define (string-equal? s1 s2)
  (and (equal? (string-length s1) (string-length s2))
       (andmap equal? s1 s2)))


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

