#lang seec


; TODO: these should be in a lib
(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))

(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

(define id
  (lambda (a)
    a))

(define snoc
  (lambda (a b) (cons b a)))


#||||||||||||||||||||||||||||#
#| Defining grammar for     |#
#| toy languages:           |#
#| expN, with natural number|#
#| expZ, with integers      |#
#||||||||||||||||||||||||||||#


(define-grammar lang
  (expn  ::= (Var name) (Valn natural) (Sn expn) (binop expn expn))
  (expz  ::= (Var name) (Valz integer) (Sz expz) (Pz expz) (binop expz expz))
  (binop ::= + *)
  (name  ::= natural)
  (envn  ::= empty (Envn expn envn))
  (envz  ::= empty (Envz expz envz)))


(define (interp-binop op n1 n2)
  (match op
  [(lang +)
   (+ n1 n2)]
  [(lang *)
   (* n1 n2)]))







#||||||||||||||||||||||||||||#
#| Language expN            |#
#||||||||||||||||||||||||||||#


; Returns the nth projection of env
(define (lookup-envn n env)
  (match env
    [(lang (Envn e1:expn env1:envn))
     (if (equal? n 0)
         (lang ,e1)
         (lookup-envn (- n 1) env1))]))

; Returns |env|
(define (size-envn env)
  (match env
    [(lang empty)
     0]
    [(lang (Envn e1:expn env1:envn))
     (+ (size-envn env1) 1)]))

; Returns the highest occurence of "Var" in the expn
(define (scope-expn e)
  (match e
    [(lang (Var n:name))
     (+ (bonsai->number n) 1)]
    [(lang (Sn e1:expn))
     (scope-expn e1)]
    [(lang (op:binop e1:expn e2:expn))
     (max (scope-expn e1) (scope-expn e2))]
    [_
     0]))

; Returns the number of occurences of "Var" in the expn
(define (numhole-expn e)
  (match e
    [(lang (Var n:name))
     1]
    [(lang (Sn e1:expn))
     (numhole-expn e1)]
    [(lang (op:binop e1:expn e2:expn))
     (+ (numhole-expn e1) (numhole-expn e2))]
    [_
     0]))




; e is properly scoped by env (assuming closed env)
(define (well-scopedn? env e)
  (let* ([s-e (scope-expn e)]
         [s-env (size-envn env)])
          (<= s-e s-env)))

; True if all expn in env are closed
(define (wf-envn? env)
   (match env
    [(lang empty)
     #t]
    [(lang (Envn e1:expn env1:envn))
     (and (well-scopedn? (lang empty) e1) (wf-envn? env1))]))

(define (eval-expn env e)
  (match e
    [(lang (Var n:name))
     (eval-expn (lang empty) (lookup-envn (bonsai->number n) env))]
    [(lang (Sn e1:expn))
     (+ 1 (eval-expn env e1))]
    [(lang (op:binop e1:expn e2:expn))
     (interp-binop op (eval-expn env e1) (eval-expn env e2))]
    [(lang (Valn n:natural))
     (bonsai->number n)]))

; Alternative way of modeling applicative contexts
(define (ctx-expn e)
    (assert (and (equal? (scope-expn e) 1) (equal? (numhole-expn e) 1))))

(define (apply-ctxn c e)
  (eval-expn (lang (Envn ,e empty)) c))



(define-language EXPN
  #:grammar lang
  #:expression expn #:size 4 
  #:context envn #:size 4 #:where (lambda (c) (wf-envn? c))
  #:link cons
  #:evaluate (uncurry eval-expn))

#||||||||||||||||||||||||||||#
#| Language expZ            |#
#||||||||||||||||||||||||||||#

(define (lookup-envz n env)
  (match env
    [(lang (Envz e1:expz env1:envz))
     (if (equal? n 0)
         (lang ,e1)
         (lookup-envz (- n 1) env1))]))
  
(define (size-envz env)
  (match env
    [(lang empty)
     0]
    [(lang (Envz e1:expz env1:envz))
     (+ (size-envz env1) 1)]))

(define (scope-expz e)
  (match e
    [(lang (Var n:name))
     (+ (bonsai->number n) 1)]
    [(lang (Sz e1:expz))
     (scope-expz e1)]
    [(lang (Pz e1:expz))
     (scope-expz e1)]
    [(lang (op:binop e1:expz e2:expz))
     (max (scope-expz e1) (scope-expz e2))]
    [_
     0]))

(define (numhole-expz e)
  (match e
    [(lang (Var n:name))
     1]
    [(lang (Sz e1:expz))
     (numhole-expz e1)]
    [(lang (Pz e1:expz))
     (numhole-expz e1)]
    [(lang (op:binop e1:expz e2:expz))
     (+ (numhole-expz e1) (numhole-expz e2))]
    [_
     0]))



(define (well-scopedz? env e)
  (let* ([s-e (scope-expz e)]
         [s-env (size-envz env)])
          (<= s-e s-env)))


(define (wf-envz? env)
   (match env
    [(lang empty)
     #t]
    [(lang (Envn e1:expz env1:envz))
     (and (well-scopedz? (lang empty) e1) (wf-envz? env1))]))


(define (eval-expz env e)
  (match e
    [(lang (Var n:name))
     (let ([e1 (lookup-envz (bonsai->number n) env)])
     (eval-expz (lang empty) e1))]
    [(lang (Sz e1:expz))
     (+ (eval-expz env e1) 1)]
    [(lang (Pz e1:expz))
     (- (eval-expz env e1) 1)]
    [(lang (op:binop e1:expz e2:expz))
     (interp-binop op (eval-expz env e1) (eval-expz env e2))]
    [(lang (Valz z:integer))
     (bonsai->number z)]))


(define (ctx-expz e)
  (assert (and (equal? (scope-expz e) 1) (equal? (numhole-expz e) 1))))


(define (apply-ctxz c e)
  (eval-expz (lang (Envz ,e empty)) c))


(define-language EXPZ
  #:grammar lang
  #:expression expz #:size 4 
  #:context envz #:size 4 #:where (lambda (c) (wf-envz? c))
  #:link cons
  #:evaluate (uncurry eval-expz))


#||||||||||||||||||||||||||||#
#| Compilation              |#
#||||||||||||||||||||||||||||#

(define (n-to-z e)
  (match e
    [(lang (Var n:name))
     (lang (Var ,n))]
    [(lang (Sn e1:expn))
     (let ([e1z (n-to-z e1)])
     (lang (Sz ,e1z)))]
    [(lang (op:binop e1:expn e2:expn))
     (let ([e1z (n-to-z e1)]
           [e2z (n-to-z e2)])
       (lang (,op ,e1z ,e2z)))]
    [(lang (Valn n:natural))
     (lang (Valz ,n))]))

(define (n-to-z-env env)
  (match env
    [(lang (empty))
     (lang (empty))]
    [(lang (e1:expn env1:envn))
           (let* ([e1z (n-to-z e1)]
                  [env1z (n-to-z-env env1)])
             (lang (,e1z ,env1z)))]))


(define-compiler N-TO-Z
  #:source EXPN
  #:target EXPZ
  #:behavior-relation equal?
  #:context-relation (lambda (c1 c2) #t)
  #:compile n-to-z)


#||||||||||||||||||||||||||||#
#| Tests                    |#
#||||||||||||||||||||||||||||#


(define test-expn1
  (lang (Valn 0)))
(define test-expn2
  (lang (+ (Sn (Valn 2)) (Var 0))))
(define test-expn3
  (lang (+ (Sn (Valn 2)) (Valn 3))))

(define test-env1
  (lang empty))
(define test-env2
  (lang (Envn ,test-expn3 empty)))
(define test-env3
  (lang (Envn ,test-expn3 (Envn ,test-expn2 empty))))

(define test-expz1
  (lang (Var 0)))
(define test-expz2
  (lang (+ (Sz (Valz 2)) (Var 0))))
(define test-expz3
  (lang (+ (Sz (Valz 2)) (Valz 3))))



#||||||||||||||||||||||||||||#
#| Synthesis                |#
#||||||||||||||||||||||||||||#


; (1) TODO: not working at the moment -- I would expect something like context (-1, empty) and an expression "Var 0"
; trying to find a weird-component of N-TO-Z
;  find an expression En and context Cz s.t. Cz[n-to-z En] != Cn[En]


#;(begin
    (displayln "(1a) Trying to find a weird component in n1-to-z1 compiler")
  (display-weird-component (time (find-weird-component N1-TO-Z1)) displayln)
  (displayln "(1) Trying to find a weird component in n-to-z compiler")
  (display-weird-component (time (find-weird-component N-TO-Z)) displayln))

; (1b) same as 1 but with applicative context
(define (link-ctxn c e)
  (cons (lang (Envn ,e empty)) c))

(define (link-ctxz c e)
  (cons (lang (Envz ,e empty)) c))


(define-language CEXPN
  #:grammar lang
  #:expression expn #:size 4 #:where (lambda (v) (well-scopedn? (lang empty) v))
  #:context    expn #:size 4 #:where ctx-expn
  #:link link-ctxn
  #:evaluate (uncurry eval-expn))



(define-language CEXPZ
  #:grammar lang
  #:expression expz #:size 4 #:where (lambda (v) (well-scopedz? (lang empty) v))
  #:context    expz #:size 4 #:where ctx-expz
  #:link link-ctxz
  #:evaluate (uncurry eval-expz))


(define-compiler CN-TO-CZ
  #:source CEXPN
  #:target CEXPZ
  #:behavior-relation equal?
  #:context-relation (lambda (c1 c2) #t)
  #:compile n-to-z)


(begin
  (displayln "Trying find-changed-component on N-TO-Z")
  (let* ([lsol (time (find-weird-component CN-TO-CZ #:count 3))])
    (map (lambda (w)
           (begin
             (displayln "-----------------------------")
             (display-weird-component w displayln)))
         lsol)))



; (2)
; trying to synthesize gadget n + 1 in a size 1 context
(define EXPN1
  (refine-language EXPN
                   #:expression-where (lambda (v) (<= (scope-expn v) 1))
                   #:context-where (lambda (c) (equal? (size-envn c) 1))
                   ))


(define (addn1spec p b)
  (match p
    [(cons c e)
     (let* ([n (eval-expn (lang empty) (lookup-envn 0 c))])
       (equal? b (+ n 1)))]))


#;(begin
  (displayln "(2) Trying to find n+1 in EXPN1")
  (display-gadget (find-gadget EXPN1 (lambda (v) #t) addn1spec) displayln))


; (3)
; trying to synthesize gadget n + m in a size 2 context
(define EXPN2
  (refine-language EXPN                   
                   #:expression-where (lambda (v) (<= (scope-expn v) 2))
                   #:context-where (lambda (c) (equal? (size-envn c) 2))
                   ))


(define (addnmspec p b)
  (match p
    [(cons c e)
     (let* ([n (eval-expn (lang empty) (lookup-envn 0 c))]
            [m (eval-expn (lang empty) (lookup-envn 1 c))])
       (equal? b (+ n m)))]))

#;(begin
  (displayln "(3) Trying to find n+m in EXPN2")
  (display-gadget (find-gadget EXPN2 (lambda (v) #t) addnmspec) displayln))


