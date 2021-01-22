#lang rosette/safe

(require (only-in racket/base
                  [string->list racket/string->list]
                  [char->integer racket/char->integer]
                  [integer->char racket/integer->char]
                  [list->string racket/list->string]
                  [string? racket/string?]
                  [char? racket/char?]
                  [string-append racket/string-append]
                  ))
(require (only-in racket/base
                  raise-user-error
                  raise-argument-error
                  raise-arguments-error))
(require (only-in racket/base
                  [log unsafe/log]))
(require "match.rkt")
(require (for-syntax syntax/parse))
(require rosette/lib/value-browser)
(require racket/contract)

(provide char?
         char
         digit->char
         new-symbolic-char*

         string?
         string
         symbolic-string?
         new-symbolic-string*
         string-length
         number->string
         char->string
         string-append
         string->char-list
         char-list->string
         char->ascii

         max-str-len
         min-int
         max-int
         )


(define (string-write b port mode)
  (case mode
    [(#f) (string-display b (λ (v) (display v port)))]
    [(#t) (string-print b (λ (v) (display v port)) (lambda (v) (write v port)))]
    [else (string-print b (λ (v) (display v port)) (lambda (v) (print v port)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Definitions of characters and strings ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct seec-char (digit)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc string-write)])

;; A (printable, ASCII) character is just a number between 32 and 126
(define (char? c)
  (and (seec-char? c)
       (integer? (seec-char-digit c))
       (<= 32 (seec-char-digit c) 126)
       ))
(define/contract (char->ascii c)
  (-> char? integer?)
  (seec-char-digit c))

(struct seec-string (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc string-write)])

;; A string is just a list of characters
(define (string? s)
  (and (seec-string? s)
       (list? (seec-string-value s))
       (andmap char? (seec-string-value s))
       ))

(define (symbolic-string? s)
  (not (empty? (symbolics s))))


(define string-append (λ strs
  (seec-string (apply append (map seec-string-value strs)))))
#;(define (string-append s1 s2)
  (seec-string (append (seec-string-value s) ..)))

(define/contract (char->racket c)
  (-> char? any/c)
  (let ([c+ (seec-char-digit c)])
    (if (term? c+) ; if c is a symbolic term, then don't do anything special
        c+
        (racket/integer->char c+)
        )))


;;;;;;;;;;;;;;;;;;;;;
;; Pretty printing ;;
;;;;;;;;;;;;;;;;;;;;;

(define (print-char c)
  (char->racket c))
(define (print-string s)
  (if (symbolic-string? s)
      (map print-char (seec-string-value s))
      (racket/string-append "\""
                            (racket/list->string (map char->racket (seec-string-value s)))
                            "\"")))


(define (string-display str out)
  (cond
    [(string? str) (out (print-string str))]
    [(char? str) (out (print-char str))]
    ))
(define (string-print str out recur)
  (cond
    [(string? str) (out (print-string str))]
    [(char? str) (out (print-char str))]
    ))


;;;;;;;;;;;;;;;;;;
;; Constructors ;;
;;;;;;;;;;;;;;;;;;

; You can construct a symbolic character using
; (define-symbolic c char?)
; or construct a concrete character from a racket char using 
; (define c (mk-char c0))
(define/contract (char c)
  (-> racket/char? char?)
  (seec-char (racket/char->integer c)))

(define (char->string c)
  (-> char? string?)
  (seec-string (list c)))

; construct either a concrete OR symbolic string
; if the input is already a rosette string, do nothing
; if the input is a concrete string, apply mk-string
(define/contract (string s)
  (-> (or/c string? racket/string?) string?)
  (cond
    [(string? s) s]
    [(racket/string? s) (seec-string (map char (racket/string->list s)))]
    ))


(define (new-symbolic-char*)
  (begin
    (define-symbolic* c integer?)
    (assert (char? (seec-char c)))
    (seec-char c)))


; create a symbolic string of length len
; len must not be symbolic or termination could occur
#;(define (new-symbolic-string* len)
  (letrec ([c (new-symbolic-char*)]
           [make-string (lambda (n)
                          (if (<= n 0)
                              '()
                              (cons c (make-string (- n 1)))))]
           )
    (seec-string (make-string len))))
(define (new-symbolic-string* len)
  (define (make-string n)
    (if (<= n 0)
        '()
        (cons (new-symbolic-char*) (make-string (- n 1)))))
  (seec-string (make-string len)))

;; functions on strings ;;
(define/contract (string-length s)
  (-> string? integer?)
  (length (seec-string-value s)))

;; given a number n between 0 and 9 inclusive,
;; output the character corresponding to n
;; (since 0 starts at 48, increase from there)
(define/contract (digit->char n)
  (-> integer? char?)
  (assert (<= 0 n 9))
  (seec-char (+ n 48))
  )

(define/contract (string->char-list s)
  (-> string? list?)
  (seec-string-value s))
(define (char-list->string l)
  #;(-> (listof char?) string?)
  (seec-string l))

;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Convert nat to string ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(define/contract (nat->string+ x fuel)
  (-> integer? integer? string?)
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
  (cond
    [(equal? (current-bitwidth) #f)
     (raise-user-error "no current bitwidth set when calling max-str-length")]
    [else
     (let* ([max-int+1 (expt 2 (current-bitwidth))]
            ; unsafe/log is only safe when both arguments are concrete
            [pos-str-len (ceiling (unsafe/log max-int+1 10))]
            )
       pos-str-len)]
    ))

(define (number->string n)
  (cond

    [(and (term? n) (equal? (current-bitwidth) #f))
     (raise-user-error "no current bitwidth set when calling number->string on symbolic argument")]
    [(negative? n)
     (let* ([minus-x (* -1 n)]
            ; replace minus-x by concrete max-int+1 if x was min-int
            [pos-minus-x (if (negative? minus-x) (expt 2 (current-bitwidth)) minus-x)])

           (string-append (string "-") (nat->string+ pos-minus-x (max-str-len))))]


    [else (nat->string+ n (max-str-len))]
  ))

;;;;;;;;;;;
;; Tests ;;
;;;;;;;;;;;

(module* test rosette/safe
  (require rackunit)
  (require (submod ".."))


  (current-bitwidth 64)
  (define x (char #\x))
  (displayln x)
  (printf "x: ~a~n" x)
  (define x-str (char->string x))
  (printf "x-str: ~a~n" x-str)
  (define hello (string "hello"))
  (printf "hello: ~a~n" hello)

  (define c-symbolic (new-symbolic-char*))
  (printf "symbolic: ~a~n" c-symbolic)
  (define s-symbolic (new-symbolic-string* 3))
  (printf "symbolic: ~a~n" s-symbolic)





  (test-case "char?"
    (check-equal? #t (char? x) "x")
    (check-equal? #f (char? x-str) "string")
    )
  (test-case "string?"
    (check-equal? #t (string? x-str) "x (string)")
    (check-equal? #t (string? hello) "hello")
    (check-equal? #f (string? x)     "char")
    )

  (test-case "string functions"

    (check-equal? 5 (string-length hello)      "string length")
    (check-equal? 3 (string-length s-symbolic) "string length (symbolic)")

    (check-equal? (string "hellox") (string-append hello x-str) "string-append")

    (check-equal? (string "20") (number->string 20) "number->string")
    )


)
  (define (test-number->string)
    (current-bitwidth 64)
    (define-symbolic x integer?)
    (assert (equal? x (min-int)))
    (define-symbolic x-len integer?)
    (define s (number->string x))
    (define s-len (string-length s))

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
