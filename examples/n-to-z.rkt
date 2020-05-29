#lang seec

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    ))


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


#| |#
(define (uncurry f)
  (lambda (ab)
    (match ab
      [(cons a b)
       (f a b)])))

(define id
  (lambda (a)
    a))


; cons in reverse order
(define snoc
  (lambda (a b) (cons b a)))

#||||||||||||||||||||||||||||#
#| Language expN            |#
#||||||||||||||||||||||||||||#


(define (lookup-envn n env)
  (match env
    [(lang (Envn e1:expn env1:envn))
     (if (equal? n 0)
         (lang ,e1)
         (lookup-envn (- n 1) env1))]))
  
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

; expn with a single hole (Var 0)
(define (ctx-expn e)
    (assert (and (equal? (scope-expn e) 1) (equal? (numhole-expn e) 1))))

(define (well-scopedn? env e)
  (let* ([s-e (scope-expn e)]
         [s-env (size-envn env)])
          (assert (<= s-e s-env))))

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

(define (eval-expn-pair ce)
  (match ce
    [(cons env e)
     (eval-expn env e)]))

(define (apply-ctxn c e)
  (eval-expn (lang (Envn ,e empty)) c))

(define (link-ctxn c e)
  (cons (lang (Envn ,e empty)) c))


(define-language EXPN
  #:grammar lang
  #:expression expn #:size 4 #:where (lambda (v) (well-scopedn? (lang empty) v))
  #:context    expn #:size 4 #:where ctx-expn
  #:link link-ctxn
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

; expz with a single hole (Var 0)
(define (ctx-expz e)
  (assert (and (equal? (scope-expz e) 1) (equal? (numhole-expz e) 1))))

(define (well-scopedz? env e)
  (let* ([s-e (scope-expz e)]
         [s-env (size-envz env)])
          (assert (<= s-e s-env))))


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

(define (apply-ctxz c e)
  (eval-expz (lang (Envz ,e empty)) c))

; decouple eval-expz from apply-ctxz
(define (link-ctxz c e)
  (cons (lang (Envz ,e empty)) c))

(define-language EXPZ
  #:grammar lang
  #:expression expz #:size 4 #:where (lambda (v) (well-scopedz? (lang empty) v))
  #:context    expz #:size 4 #:where ctx-expz
  #:link link-ctxz
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


(define (crel cn cz)
  (let ([cnz (n-to-z-env cn)])
    (equal? cnz cz)))


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


; find an expression En and context Cz s.t. Cz[n-to-z En] != Cn[En] for Cn of bounded size
#;(begin
  (displayln "Trying find-weird-component on N-TO-Z")
  (display-weird-component (time (find-weird-component N-TO-Z))))
    #;[(list vars sol)
     (let* ([vars* (map (lambda (var)
                          (concretize var sol)) vars)])
       (begin
         (displayln "Source, target exp:")
         (displayln (first vars*))
         (displayln (n-to-z (first vars*)))
         (displayln "Target context:")
         (displayln (third vars*))
         (displayln "Target behavior:")
         (displayln (fifth vars*))))]
    #;[_
     (displayln "Synthesis failed")]


;spec of add1 function for expn
(define (add1spec p b)
  (match p
    [(cons c e)
     (let* ([n (eval-expn (lang empty) (lookup-envn 0 c))])
       (equal? b (+ n 1)))]))


(define (link-ctxn2 c e)
  (cons (lang (Envn ,c empty)) e))

; same as expn but with exp and ctx switched
; expression has 1 hole
; ctx has 1 closed expn
(define-language EXPN2
  #:grammar lang
  #:expression expn #:size 4 #:where ctx-expn
  #:context    expn #:size 4 #:where (lambda (v) (well-scopedn? (lang empty) v))
  #:link link-ctxn2
  #:evaluate (uncurry eval-expn))

#;(begin
  (displayln "Trying to find add1 gadget")
  (display-gadget (find-gadget EXPN2 (lambda (v) #t) add1spec) displayln))
; trying to find an exp that adds 1 to the context


; Generating  n + m with a size two context
(define-language EXPN3
  #:grammar lang
  #:expression expn #:size 4 #:where (lambda (v) (<= (scope-expn v) 2))
  #:context envn #:size 5 #:where (lambda (c) (and (equal? (size-envn c) 2) (wf-envn? c)))
  #:link cons
  #:evaluate (uncurry eval-expn))

(define (addnmspec p b)
  (match p
    [(cons c e)
     (let* ([n (eval-expn (lang empty) (lookup-envn 0 c))]
            [m (eval-expn (lang empty) (lookup-envn 1 c))])
       (equal? b (+ n m)))]))

(begin
  (displayln "Trying to find addNM gadget")
  (display-gadget (find-gadget EXPN3 (lambda (v) #t) addnmspec) displayln))


#||||||||||||||||||||||||||||#
#| Synthesis                |#
#||||||||||||||||||||||||||||#


; Find a source expression (expn) which fails to evaluate in the empty context
#|
(displayln "Building a source expression (Expn)")
(define e* (lang expn 3))
(define sol (time
              (verify
                (time (eval-expn (lang empty) e*)))))
(define e (concretize e* sol))
(displayln "Found a source expression (Expn) which fails to evaluate in the empty context")
(displayln e)
(displayln (scope-expn e))
|#

#|
; Find an expn which fails to evaluate in any context of size up to 3
(displayln "Building a source expression (Expn) and context (Envn)")
(define e* (lang expn 3))
(define c* (lang envn 5))
(void (time (assert (wf-envn? c*))))
(void (time (assert (<= 2 (size-envn c*)))))
;(void (time (assert (well-scoped? c* e*))))
(define sol (time
              (verify
               (time (eval-expn c* e*)))))
(define c (concretize c* sol))
(define e (concretize e* sol))
(displayln "Found a source expression (Expn) which fails to evaluate a well-scoped context")
(displayln c)
(displayln e)
li|#

#|
; Find a z* which evaluates to a result which no (bounded) expn evaluates to
(displayln "Building source and target expressions.")
(define n* (time (lang expn 4)))
(define z* (time (lang expz 4)))

(displayln "Restricting to closed expressions.")
(void (time (eval-expz (lang empty) z*)))
(void (time (eval-expn (lang empty) n*)))

(displayln "Find a target expression exhibiting behaviors that no source expression have.")

(define-values (v a) (with-asserts (time (assert (equal? (eval-expn (lang empty) n*) (eval-expz (lang empty) z*))))))
(newline)

(define sol
    (synthesize #:forall n*
                #:guarantee (assert ( !( apply && a)))))
(define z (concretize z* sol))
(displayln "Target expression:")
(displayln z)
(displayln "Evaluation of target expression:")
(displayln (eval-expz (lang empty) z))
|#

#|
; find an expression En and context Cz s.t. Cz[n-to-z En] != Cn[En] for Cn of bounded size
(displayln "Creating a symbolic expression, restricting it to closed expression and compiling it")
(define n* (time (lang expn 4)))
(void (time (well-scopedn? (lang empty) n*)))
(define z* (n-to-z n*))


(displayln "Creating symbolic contexts (expn/expz with a single hole)")
(define cn* (time (lang expn 4)))
(void (time (ctx-expn cn*)))
(define cz* (time (lang expz 4)))
(void (time (ctx-expz cz*)))

;(displayln "Restricting target context and expression to compatible ones")
;(void (time (apply-ctxz cz* z*)))

(displayln "Finding a target context and an expression s.t. no source context exhibit the same behaviors")
(define-values (v a) (with-asserts (time (assert (equal? (apply-ctxn cn* n*) (apply-ctxz cz* z*))))))
(newline)

(define sol
    (synthesize #:forall cn*
                #:guarantee (assert ( !( apply && a)))))
(define cz (concretize cz* sol))
(define n (concretize n* sol))
(define cn (concretize cn* sol))
(define z (time (n-to-z n)))

(displayln "Source Expression (Expn):")
(displayln n)
(displayln "Target Expression (Expz):")
(displayln z)
(displayln "Target Context:")
(displayln cz)

(displayln "Target Evaluation:")
(displayln (apply-ctxz cz z))



|#
