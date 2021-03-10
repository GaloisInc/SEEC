#lang rosette/safe

(require racket/stxparam)
(require (only-in racket/contract
                  [define/contract racket:define/contract]
                  [listof          racket:listof]
                  ))
(require (except-in racket/contract
                    define/contract
                    listof))
(require (only-in racket/base
                  make-parameter
                  parameterize
                  [raise-user-error      racket:raise-user-error]
                  [raise-argument-error  racket:raise-argument-error]
                  [raise-arguments-error racket:raise-arguments-error]
                  ))
(require (for-syntax (only-in racket/base
                              make-parameter
                              )))

(provide debug
         debug-display
         debug?
         parameterize
         define/debug

         define/contract
         define/contract/debug
         use-contracts-globally
         (all-from-out racket/contract) ; Since we didn't import define/contract, no overlap
         listof
         )

;;;;;;;;;
; Debug ;
;;;;;;;;;

(define debug? (make-parameter #f))
(define (debug stmt)
  (if (debug?)
      (stmt)
      (void)))
(define-syntax (debug-display stx)
  (syntax-case stx ()
    [(_ str args ...)
     #'(debug (thunk (displayln (format str args ...))))
     ]))

;;;;;;;;;;;;;
; Contracts ;
;;;;;;;;;;;;;

(begin-for-syntax
  (define use-contracts-internal? (make-parameter #t))
)

(define-syntax (define/contract stx)
  (syntax-case stx ()

    [(_ name contract-expr body ...)
     (cond
       [(use-contracts-internal?)
        #'(racket:define/contract name contract-expr body ...)]
       [else
        #'(define name body ...)]
     )]

    ; Optionally turn on debugging (see below)
    [(_ name contract-expr body ...)
     (cond
       [(use-contracts-internal?)
        #'(racket:define/contract name contract-expr body ...)]
       [else
        #'(define name body ...)]
     )]
    ))

(define-syntax (use-contracts-globally stx)
  (syntax-case stx ()
    [(_ #t) (use-contracts-internal? #t)
            #'(void)]
    [(_ #f) (use-contracts-internal? #f)
            #'(void)
            ]
    ))

(define (listof tp?)
  (λ (x) (for/all ([x x])
           ((racket:listof tp?) x))))

;;;;;;;;;;;;;;;;;;;;;
; Tunable debugging ;
;;;;;;;;;;;;;;;;;;;;;


(begin-for-syntax
  (define (syntax->string stx)
    (symbol->string (syntax->datum stx)))
  )


; (define/debug (f xs ...) body)
; will insert a call to debug-display showing the
; function name and arguments it is called with.
; Optionally, you can turn the suffix on, which will
; also print the result
(define-syntax (define/debug stx)
  (syntax-case stx ()

    ; No contracts. Must come after #:contract because otherwise parsing would be incorrect
    [(_ (name args ...) body ...)
     (let* ([name-as-string (syntax->string #'name)])
       #`(define (name args ...)
           (debug-display "~a" (list #,name-as-string args ...))
           body
           ...
           )
       )]

    ; Optionally turn on suffix, but only one body expression is allowed
    [(_ #:suffix (name args ...) body-expr)
     (let* ([name-as-string (syntax->string #'name)])
       #`(define (name args ...)
           (debug-display "~a" (list #,name-as-string args ...))
           (define tmp body-expr)
           (debug-display "result of ~a: ~a" #,name-as-string tmp)
           tmp
           )
       )]


    ))

; Both contracts and debugging
(define-syntax (define/contract/debug stx)
  (syntax-case stx ()
    [(_ (name args ...) contract-expr body ...)
     (let* ([name-as-string (syntax->string #'name)])
       #`(define/contract (name args ...)
           contract-expr
           (debug-display "~a" (list #,name-as-string args ...))
           body
           ...
           )
       )]
    [(_ #:suffix (name args ...) contract-expr body-expr)
     (let* ([name-as-string (syntax->string #'name)])
       #`(define/contract (name args ...)
           contract-expr
           (debug-display "~a" (list #,name-as-string args ...))
           (define tmp body-expr)
           (debug-display "result of ~a: ~a" #,name-as-string tmp)
           tmp
           )
       )]
    ))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(module+ test
  (use-contracts-globally #f)
  (define/contract (foo x) (-> any/c boolean?) 5)
  (foo 3) ; Should return 5
  
  (use-contracts-globally #t)
  (foo 3) ; Should return 5
  (define/contract (bar x) (-> any/c boolean?) 5)
  #;(bar 3) ; Should throw an exception


  (define/debug (foobar x y) 10)
  (parameterize ([debug? #t])
    (foobar 3 5))

  (define/debug #:suffix (foobar+ x y) 10)
  (parameterize ([debug? #t])
    (foobar+ 3 5))

  (define/contract/debug #:suffix (foobar+contract x y)
    (-> any/c any/c integer?)
    10)
  (parameterize ([debug? #t])
    (foobar+contract 3 5))
  )
