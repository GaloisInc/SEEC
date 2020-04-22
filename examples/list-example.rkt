#lang seec

(define-language lang
  (bool-list ::= (list boolean))
  (list-of-list ::= (list (list boolean))
)
(define list-ex (lang (cons #t (cons #f nil))))
(define (bool-list-length l)
  (match l
    [(lang nil) 0]
    [(lang (cons boolean l+:(list boolean))) (+ 1 (bool-list-length l+))]
    ))
