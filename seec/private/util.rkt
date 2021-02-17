#lang rosette/safe

(require racket/stxparam)
(require (only-in racket/contract
                  [define/contract racket:define/contract]
                  ))
(require (except-in racket/contract
                    define/contract))
(require (only-in racket/base
                  make-parameter
                  [raise-user-error      racket:raise-user-error]
                  [raise-argument-error  racket:raise-argument-error]
                  [raise-arguments-error racket:raise-arguments-error]
                  ))
(require (for-syntax (only-in racket/base
                              make-parameter
                              )))

(provide debug
         debug?
         define/contract
         use-contracts-globally
         (all-from-out racket/contract) ; Since we didn't import define/contract, no overlap
         )

(define debug? (make-parameter #f))
(define (debug stmt)
  (if (debug?)
      (stmt)
      (void)))

(begin-for-syntax
  (define use-contracts-internal? (make-parameter #t))
)

(define-syntax (define/contract stx)
  (syntax-case stx ()
    [(_ (name args ...) contract-expr body ...)
     (cond
       [(use-contracts-internal?)
        #'(racket:define/contract (name args ...) contract-expr body ...)]
       [else
        #'(define (name args ...) body ...)]
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

(module+ test
  (use-contracts-globally #f)
  (define/contract (foo x) (-> any/c boolean?) 5)
  (foo 3) ; Should return 5
  
  (use-contracts-globally #t)
  (foo 3) ; Should return 5
  (define/contract (bar x) (-> any/c boolean?) 5)
  (bar 3) ; Should throw an exception
  )
