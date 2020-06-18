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
(require (only-in racket/base
                  [log unsafe/log]))
(require rosette/lib/value-browser)


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
         number->string+
         number->string
         digit->char
         string-append
         string
         max-str-len

         #;(rename-out [bv-max-width string/bv-max-width])
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

;; given a number n between 0 and 9 inclusive,
;; output the character corresponding to n
;; (since 0 starts at 48, increase from there)
(define (digit->char n)
  (assert (<= 0 n 9))
  (+ n 48)
  )

(define (number->string+ x fuel)
  (cond
    [(< fuel 0)  (raise-argument-error 'number->string+ "ran out of fuel" fuel)]
    [(negative? x)
     (let* ([minus-x (* -1 x)]
           [pos-minus-x (if (negative? minus-x) (expt 2 (current-bitwidth)) minus-x)]) ; replace minus-x by concrete max-int+1 if x was min-int
           (string-append (string "-") (number->string+ pos-minus-x (- fuel 1))))]
    [(<= 0 x 9)    (char->string (digit->char x))]
    [(>= x 10)     (let* ([q (quotient x 10)]
                          [r (remainder x 10)]
                          [q-str (number->string+ q (- fuel 1))]
                          [r-str (char->string (digit->char r))]
                          )
                     (string-append q-str r-str))]
    ))

(define (max-str-len)
  (let ([max-int+1 (expt 2 (current-bitwidth))])
    ; unsafe/log is only safe when both arguments are concrete
    (ceiling (unsafe/log max-int+1 10))))

(define (number->string n)
  (number->string+ n 10);(max-str-len))
  )

#;(current-bitwidth 32)

#;(print-string (number->string 1000000000))

; testing number->string
#|
(define-symbolic* x integer?)
(define s (number->string x))
#;(print-string s)
#;(render-value/window s)
#;(define len (string-length s))
#;(render-value/window len)
#;(assert (equal? x 10000000000000000)) ; note: this will just truncate the result
(assert (equal? (string-length s) 11)) ; can go up to 11
(define sol (synthesize #:forall '()
                        #:guarantee (assert #t)
                        ))
sol
(define x-val (evaluate x (complete-solution sol (symbolics x))))
(print-string (number->string x-val))
(string-length (number->string x-val))
|#
