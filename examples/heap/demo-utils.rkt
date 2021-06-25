#lang racket/base

(provide recorded)

(require (for-syntax racket/base))
(require (only-in racket file->string))

(define-syntax (recorded stx)
  (syntax-case stx ()
    [(_ id)
     #`(begin
         (sleep 2)
         (display
          (file->string
           (string-append
            "./output/upper-demo-err-"
            #,(symbol->string (syntax->datum #'id))
            ".txt"))))]))
