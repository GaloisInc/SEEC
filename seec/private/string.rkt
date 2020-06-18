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
                  raise-user-error
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
         number->string
         digit->char
         string-append
         string
         max-str-len
         min-int
         max-int

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


(define (max-int)
  (cond
    [(equal? (current-bitwidth) #f)
     (raise-user-error "no current bitwidth set when calling max-int")]
    [else
     ; subtract exponent by 1 because of signed integers
     (- (expt 2 (current-bitwidth)) 1)
     ]
  ))
(define (min-int)
  (cond
    [(equal? (current-bitwidth) #f)
     (raise-user-error "no current bitwidth set when calling min-int")]
    [else
     (* -1 (+ (max-int) 1))
     ]
  ))

(define (nat->string+ x fuel)
  (define res (cond
    [(< fuel 0)    (raise-argument-error 'nat->string+ "ran out of fuel" fuel)]
    [(negative? x) (raise-argument-error 'nat->string+ "natural?" x)]

    [(<= 0 x 9)    (char->string (digit->char x))]
    [(>= x 10)     (let* ([q (quotient x 10)]
                          [r (remainder x 10)]
                          [q-str (nat->string+ q (- fuel 1))]
                          [r-str (char->string (digit->char r))]
                          )
                     (string-append q-str r-str))]
    ))
  res)

(define (max-str-len)
  (let* ([max-int+1 (expt 2 (current-bitwidth))]
         ; unsafe/log is only safe when both arguments are concrete
         [pos-str-len (ceiling (unsafe/log max-int+1 10))]
         )
    pos-str-len))

(define (number->string n)
  (cond

    [(negative? n)
     (let* ([minus-x (* -1 n)]
            ; replace minus-x by concrete max-int+1 if x was min-int
            [pos-minus-x (if (negative? minus-x) (expt 2 (current-bitwidth)) minus-x)])

           (string-append (string "-") (nat->string+ pos-minus-x (max-str-len))))]


    [else (nat->string+ n (max-str-len))]
  ))



(define (test-number->string)
  (current-bitwidth 64)
  (printf "min-int: ~a~n" (min-int))
  (printf "max-int: ~a~n" (max-int))
  (define-symbolic x integer?)
  (assert (equal? x (min-int)))
  (define-symbolic x-len integer?)
  (define s (number->string x))
  (printf "string: ~a~n" s)
  #;(render-value/window s)
  (define s-len (string-length s))
  (printf "string-length: ~a~n" s-len)
  #;(render-value/window s-len)

  (define sol (synthesize
               #:forall '()
               #:guarantee (assert (equal? s-len x-len))
               ))
  (if (unsat? sol)
      (displayln "Synthesis failed")
      (begin
        (displayln "Synthesis succeeded")
        (define complete-sol (complete-solution sol (symbolics x)))
        (define x-instance (evaluate x complete-sol))
        (define s-instance (evaluate s complete-sol))
        (define x-len-instance (evaluate x-len complete-sol))
        (printf "x: ~a~n" x-instance)
        (printf "s: ~a~n" s-instance)
        (printf "string-length: ~a~n" (evaluate (string-length s) complete-sol))
        (printf "x-len: ~a~n" x-len-instance)
        (printf "did synthesis succeed? ~a~n" (equal? (string-length s-instance) x-len-instance))
        ))
)
#;(test-number->string)
