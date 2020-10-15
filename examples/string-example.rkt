#lang seec

(require seec/private/string)
(require (only-in racket/base integer->char))
(require seec/private/bonsai2)

(require rosette/lib/value-browser) ; debugging

(define-grammar constants
  (const ::= (BOOL boolean) num (STR string) (CHAR char))
  (num ::= (NAT natural))
)

(constants-const? (constants (BOOL #t)))


(define b (constants (BOOL #f)))
(define five (constants (NAT 5)))


(define hi-desired (constants (STR "hi")))
(define c-desired (constants (CHAR #\x)))
#;(displayln hi-desired)
#;(displayln c-desired)
#;(match hi-desired
  [(constants (STR s:string)) (print-string (bonsai-string-value s))]
  )
#;(match c-desired
  [(constants (CHAR c:char)) (displayln c)]
  )


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
  #;(displayln (constants (CHAR #\x)))

  #|
  (define t (make-tree! 2 2))
  
  (displayln t)
  (define is-str
    (match t
      [(constants string) #t]
      [_ #f]))
#;  (assert is-string)
  (displayln is-str)
  |#

  (define symbolic-exp (constants const 6))
  #;(define sol (verify (assert (not (equal? symbolic-exp (constants (CHAR #\x)))))))
  (define (is-char)
    (match symbolic-exp
      #;[(constants (CHAR c:char)) #t]
      [(constants (CHAR c:char)) (equal? (bonsai-char-value c) (char #\y))]
      [_ #f]))
  (define (is-string)
    (match symbolic-exp
      #;[(constants (STR s:string)) #t]
      [(constants (STR s:string)) (equal? (bonsai-string-value s) (string "hello"))]
      [_ #f]))
  (define (is-bool)
    (match symbolic-exp
      [(constants (BOOL b:boolean)) #t]
      [_ #f]))

  (displayln (is-bool))
  (displayln (is-char))
  (displayln (is-string))

  (displayln "")
  #;(define (get-string)
    (match symbolic-exp
      [(constants (STR s:string)) s]))
  #;(displayln (get-string))
  #;(displayln (equal? (get-string) (string "")))

  #;(assert (equal? symbolic-exp (constants (STR "x"))))
  (assert (is-string))
  (define sol (verify (assert #f)))
  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded:")
        (define instance (concretize symbolic-exp sol))
        (displayln instance)
        ))
  )
#;(synthesize-string-in-lang)





(define (more-tests)
  #;(define t (bonsai-list (cons (new-char!) (cons (new-char!) (cons (bonsai-null) '())))))
  #;(define t (make-string-tree! 2 2))
  #;(define t (new-string! 5))
  (define t (constants string 5))
  (define x (match t
              [(constants s:string) (equal? (bonsai-string-value s) (string "hi"))]
              #;[(constants s:string) (equal? (string-length (bonsai-string-value s)) 3)]
              [_ #f]))
  (displayln x)
  #;(displayln (string-length (bonsai-string-value t)))
  #;(displayln (print-string (bonsai-string-value t)))
  #;(displayln t)
  #;(displayln (= (string-length (bonsai-string-value t)) 3))
  #;(displayln (equal? (bonsai-string-value t) (string "")))
  #;(displayln (string? (bonsai-string-value t)))

  #;(define x (constants string 4))
  #;(match t
    [(constants s:string) (equal? (bonsai-string-value s) (string "x"))]
    [_ #f]
    )
  (displayln #t)
  )
#;(more-tests)

(define (pattern-matching-tests)
  (define t (constants string 1))
  (define t-constant (constants ""))
  (define (do-match s)
    (match s
      [(constants "") #t]
      [_ #f]))
  (define (do-equal s)
    (equal? s (constants "")))

  #;(render-value/window t-equal)
  #;(displayln (do-equal t))

  (define b (constants boolean 1))
  (match b
    [(constants #t) #t]
    [_ #f])
  )
#;(pattern-matching-tests)
