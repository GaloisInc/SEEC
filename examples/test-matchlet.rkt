#lang seec

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))

(define-language lang
  (exp  ::= (Val integer) (Plus exp exp))

  )



; returns a pair containing (1) the value of exp e (2) a list of all integers encountered in e
(define (eval-at-zero e)
  (match e
    [(lang (Val n:integer))
     (let ([nn (bonsai->number n)])
       (cons nn (list nn)))]
    [(lang (Plus e1:exp e2:exp))
     #;(match (eval-at-zero e1)
       [(cons v1 l1)
        (match (eval-at-zero e2)
          [(cons v2 l2)
           (let* ([l12 (append l1 l2)]
                  [v12 (+ v1 v2)])
             (cons v12 l12))])])
     (match-let* ([(cons v1 l1) (eval-at-zero e1)]
                  [(cons v2 l2) (eval-at-zero e2)])
           (let* ([l12 (append l1 l2)]
                  [v12 (+ v1 v2)])
             (cons v12 l12)))
     ]))

(define test-exp1
  (lang (Plus (Val 4) (Val 0))))

(define test-exp2
  (lang (Plus (Plus (Val 4) (Val 0)) (Plus (Val 2) (Val 1)))))

(displayln "Test match-let*");
(displayln (eval-at-zero test-exp1))
