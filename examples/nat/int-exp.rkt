#lang seec

(define-grammar int-exp
  (val   ::= input integer)
  (exp   ::= (+ exp exp) val
             (neg? exp exp exp)))

(define (int-subst n exp)
  (match exp
    [(int-exp input) n]
    [(int-exp v:integer) (int-exp ,v)]
    [(int-exp (+ l:exp r:exp))
     (int-exp (+ ,(int-subst n l)
                 ,(int-subst n r)))]
    [(int-exp (neg? c:exp t:exp f:exp))
     (int-exp (neg? ,(int-subst n c)
                    ,(int-subst n t)
                    ,(int-subst n f)))]))

(define (int-eval exp)
  (match exp
    [(int-exp n:integer) (int-exp ,n)]
    [(int-exp (+ l:exp r:exp))
     (int-exp ,(seec-add (int-eval l)
                         (int-eval r)))]
    [(int-exp (neg? c:exp t:exp f:exp))
     (if (< (seec->int (int-eval c)) 0)
         (int-eval t)
         (int-eval f))]))

(provide (all-defined-out))
