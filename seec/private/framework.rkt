#lang rosette/safe

(provide current-default-bound
         define-language
         refine-language
         define-compiler
         (struct-out language)
         (struct-out compiler)
         find-changed-behavior
         find-changed-component
         find-weird-computation
         find-weird-component
         find-weird-behavior
         find-gadget
         (struct-out solution)
         unpack-language-witness
         unpack-language-witnesses
         display-changed-behavior
         display-changed-component
         display-weird-behavior
         display-weird-component
         display-gadget
         display-list
         seec-add
         seec-subtract
         link
         evaluate
         link-and-evaluate
         compile
         clear-all-queries

         make-symbolic-var
         (struct-out language-witness)
         concretize-witness
         )
(require (only-in racket/base
                  make-parameter
                  parameterize
                  write-string
                  values))
(require (for-syntax syntax/parse)
         (for-syntax racket/syntax)
         racket/stxparam
         racket/contract

         (prefix-in unsafe:
                    (combine-in
                     (only-in racket
                              make-parameter
                              for/list
                              in-range
                              in-producer)
                     (only-in racket/base
                              raise-argument-error
                              raise-arguments-error
                              )
                    racket/generator))
         "bonsai2.rkt")
#|

 This file provides structures to reason abstractly about weird machines.

  "language" represents a language in the weird-machine framework.

  "compiler" represent a compiler in the weird-machine framework.
    In addition to the source and a target language structures,
    it contains trusted relations over behaviors and contexts and
    and a compilation function

   1) Create language structures
      > define-language ...
      > define-compiler ...
   2) Search for witnesses of X
      > find-X ...
      or
      > find-X ... #:count n 
   3) Display the concrete witnesses returned at step 2
      > display-X



|#

; Default bound for any predicated syntactic class generated
(define current-default-bound
  (unsafe:make-parameter 5
                         (lambda (db) 
                           (unless (and (integer? db) (positive? db))
                             (unsafe:raise-argument-error 'current-default-bound "positive integer" db)                  
                             db))))

; Predicated syntactic class
; For the moment, we decouple pred (symbolic restrictions) from gen
; (syntactic generation)
;   generator : bound -> bonsai-tree
;   predicate : bonsai-tree -> bool
;   default-bound : nat
(struct predsyn (generator predicate default-bound))

(define-syntax (define-predsyn stx)
  (syntax-parse stx
    [(_ grammar pat pred default-bound)
     #`(predsyn (lambda (bound) (grammar pat bound)) pred default-bound)]))

(define (make-symbolic-var ps [bound #f])
  (let* ([bound (if bound bound (predsyn-default-bound ps))]
         [s ((predsyn-generator ps) bound)])
    (assert ((predsyn-predicate ps) s))
    s))

; A language
; expression : predsyn
; context : predsyn
; link : ctxt -> expr -> program
; evaluate : program -> behavior
(struct language (expression context link evaluate))

(define (link language expr context)
  ((language-link language) expr context))

(define (evaluate language program)
  ((language-evaluate language) program))

(define (link-and-evaluate language expr context)
  (evaluate language (link language expr context)))

(begin-for-syntax
  (define-splicing-syntax-class predsyn
    (pattern (~seq nt:id
                   (~optional
                    (~seq #:size n:expr)
                    #:defaults ([n #'(current-default-bound)]))
                   (~optional
                    (~seq #:where p:expr)
                    #:defaults ([p #'(lambda (t) #t)])))
             #:with gen #'nt
             #:with pred #'p
             #:with bound #'n)))

(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name
        #:grammar    grammar
        #:expression expr:predsyn
        #:context    ctxt:predsyn
        #:link       link
        #:evaluate   eval)
     #'(define name
         (let* ([predexp (define-predsyn grammar expr.gen expr.pred expr.bound)]
                [predctx (define-predsyn grammar ctxt.gen ctxt.pred ctxt.bound)])
           (language predexp predctx link eval)))]))

(define-syntax (define-language-class stx)
  (syntax-parse stx
    [(_ name
        #:grammar    grammar
        #:expression expr:id
        #:context    ctxt:id
        #:link       link
        #:evaluate   eval)
     #'(define (name expr-tuple ctx-tuple)         
         (let* ([predexp (define-predsyn grammar expr (first expr-tuple) (second expr-tuple))]
                [predctx (define-predsyn grammar ctxt (first ctx-tuple) (second expr-tuple))])
           (language predexp predctx link eval)))]))


; Refine the "where" clause
; and replace the default-bound
; on expression or context 
(define-syntax (refine-language stx)
  (syntax-parse stx
    [(_ name (~seq (~optional
                    (~seq #:expression-bound eb)
                    #:defaults ([eb #'#f]))
                   (~optional
                    (~seq #:expression-where ef)
                    #:defaults ([ef #'#f]))
                   (~optional
                    (~seq #:context-bound cb)
                    #:defaults ([cb #'#f]))
                                      (~optional
                    (~seq #:context-where cf)
                    #:defaults ([cf #'#f]))))
     #`(let* ([oldexpression (language-expression name)]
              [olde-generator (predsyn-generator oldexpression)]
              [olde-predicate (predsyn-predicate oldexpression)]
              [olde-default-bound (predsyn-default-bound oldexpression)]
              [exp (predsyn olde-generator
                            (if ef
                                (lambda (x) (and (olde-predicate x)
                                                 (ef x)))
                                olde-predicate)
                            (if eb
                                eb
                                olde-default-bound))]
              [oldcontext (language-context name)]
              [oldc-generator (predsyn-generator oldcontext)]
              [oldc-predicate (predsyn-predicate oldcontext)]
              [oldc-default-bound (predsyn-default-bound oldcontext)]
              [ctx (predsyn oldc-generator
                            (if cf
                                (lambda (x) (and (oldc-predicate x)
                                                 (cf x)))
                                oldc-predicate)
                            (if cb 
                                cb
                                oldc-default-bound))])
         (language exp ctx (language-link name) (language-evaluate name)))]))



; A compiler between languages consists of:
; source: a lang structure standing in as source
; target: a lang structure standing in as target
; behavior-relation: equivalence class for source and target behaviors
; context-relation:  equivalence class for source and target contexts
; compile: function from source-expression to target-expression
; context-compile: optionally, a function from source.ctx to source.target
(struct compiler (source target behavior-relation context-relation compile))

(define-syntax (define-compiler stx)
  (syntax-parse stx
    [(_ name
        #:source source
        #:target target
        #:behavior-relation brel
        (~optional (~seq #:context-relation crel)
                   #:defaults ([crel #'#f]))
        #:compile compile)
     #`(define name (compiler source target brel crel compile))]))

(define (compile compiler prog)
  ((compiler-compile compiler) prog))

(struct language-witness (expression context program behavior) #:transparent)

; Utility for language-witness:

;
(define (unpack-language-witness v)
  (list (language-witness-expression v)
        (language-witness-context v)
        (language-witness-program v)
        (language-witness-behavior v)))

; unpack a list of two language witness (usually source and target)
(define (unpack-language-witnesses v)
  (list (unpack-language-witness (first v))
        (unpack-language-witness (second v))))

; Group every n elements of the input list into language-witness, where n is the number of field of a language-witness
; Assumes length l is divisible by n
(define (pack-language-witness l)
    (if (empty? l)
        (list)
        (let-values ([(hd tl) (split-at l 4)])
          (let ([packed-hd (language-witness (first hd) (second hd) (third hd) (fourth hd))]
                [packed-tl (pack-language-witness tl)])
            (cons packed-hd packed-tl)))))

; witness is a list of language-witness 
(struct solution (witness model) #:transparent)

(struct failure (message) #:transparent
  #:methods gen:custom-write
  [(define (write-proc f port mode)
     (display (failure-message f) port))])

(define (changed-behavior-solution-write sol port mode)
  (display-changed-behavior sol (lambda (v) (display v port))))

(struct changed-behavior-solution solution () #:transparent
  #:methods gen:custom-write
  [(define write-proc changed-behavior-solution-write)])

(define (weird-component-solution-write sol port mode)
  (display-weird-component sol (lambda (v) (display v port))))

(struct weird-component-solution solution () #:transparent
  #:methods gen:custom-write
  [(define write-proc weird-component-solution-write)])




(define-syntax (run-query stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:count max:expr)
                   #:defaults ([max #'#f]))
         gen)
     #'(if max
           (let* ([witness-list (unsafe:for/list ([i (unsafe:in-range max)]
                                                 [t (unsafe:in-producer gen #f)])
                                                t)])
             witness-list)
           (gen))]))

; if witness-count is #f, return the first witness in witness-list
(define (unwrap-witness witness-count witness-list)
        (if witness-count
          witness-list
          (if witness-list
              (first witness-list)
              witness-list)))

  


; concretize all vars included in the solution, return a list of language-witness with concrete vars
(define/contract (concretize-witness sym-solution)
  (-> solution? (listof language-witness?))
  (let* ([vars (solution-witness sym-solution)]
        [unpacked-vars (map unpack-language-witness vars)]
        [model (solution-model sym-solution)]
        [list-vars (foldr append (list) unpacked-vars)]
        [concretized (concretize list-vars model)])
      (pack-language-witness concretized)))




; show (c1, v1) ~> b1 and (c2, v2) ~> b2
(define (display-changed-behavior vars out)
  (cond
    [(equal? vars #f) (out (format "No changed behavior found~n"))]
    [else
     (let* ([source-vars (first vars)]
            [target-vars (second vars)])
       (begin 
         (out (format
               "Expression ~a~n has behavior ~a~n in source-level context ~a~n"
               (language-witness-expression source-vars)
               (language-witness-behavior source-vars)
               (language-witness-context source-vars)))
         (out (format
               "Compiles to ~a~n with emergent behavior ~a~n in target-level context ~a~n"
               (language-witness-expression target-vars)
               (language-witness-behavior target-vars)
               (language-witness-context target-vars)))))]))

; alias display-changed-behavior
(define (display-changed-component vars out)
  (display-changed-behavior vars out))









(define/contract find-weird-behavior
  (->* (compiler?)
       (#:source-expr-bound (or/c #f integer?)
        #:source-expr any/c
        #:source-expr-constraint (-> any/c boolean?)
        #:source-context-bound (or/c #f integer?)
        #:source-context any/c
        #:source-context-constraint (-> any/c any/c boolean?)
        #:source-behavior-constraint (-> any/c any/c any/c any/c boolean?)
        #:target-context-bound (or/c #f integer?)
        #:target-context any/c
        #:target-context-constraint (-> any/c any/c boolean?)        
        #:target-behavior-constraint (-> any/c any/c any/c any/c boolean?)
        #:fresh-witness boolean?
        #:debug boolean?
        #:forall any/c
        #:forall-extra any/c
        #:count integer?
        #:capture-nondeterminism boolean?
        #:found-core (-> any/c any/c) ; Which part of the witness should not be repeated between examples 
)
       (or/c #f (listof (listof language-witness?))) ; lists of pairs of language-witness (source and target)
       )
  (lambda (comp
           #:source-expr-bound [e1-bound #f]; (or/c #f natural?)
           #:source-expr [e1 (make-symbolic-var (language-expression (compiler-source comp)) e1-bound)]
           ; Provide a concrete expression argument instead of generating a symbolic one
           #:source-expr-constraint [e1-constraint (λ (x) #t)] ; (-> s.expression? boolean?)
           #:source-context-bound [c1-bound #f] ; (or/c #f natural?) 
           #:source-context [c1 (make-symbolic-var (language-context  (compiler-source comp)) c1-bound)]
           #:source-context-constraint [c1-constraint (λ (e1 c1) #t)] ; (-> s.expression? s.context? boolean?)
           ; Constraint the source context according to the source expression
           #:source-behavior-constraint [b1-constraint (λ (e1 c1 c2 b1) #t)] ; (-> s.expression? s.context? t.context? s.behavior boolean?)
           ; Constraint the desired source behavior according to the source expression and the source and target context
           #:target-context-bound [c2-bound #f] ; (or/c #f natural?)
           #:target-context [c2 (make-symbolic-var (language-context (compiler-target comp)) c2-bound)]
           ; Provide a concrete target context instead of generating a symbolic one
           #:target-context-constraint [c2-constraint (λ (e1 c2) #t)] ; (-> s.expression? t.context? boolean?)
           ; Constraint the target context according to the source expression
           #:target-behavior-constraint [b2-constraint (λ (e1 c1 c2 b2) #t)] ; (-> s.expression? s.context? t.context? t.behavior boolean?)
           ; Constraint the desired target behavior according to the source expression and the source and target context
           #:fresh-witness [fresh #t] ; (boolean?)
           ; if #t, generate a fresh context satisfying the constraints
           #:debug [debug #f] ; (boolean?)
           ; if #t, query will synthesize an expression that violates the property
           #:forall [vars (if debug
                              (list )
                              c1)] 
           #:forall-extra [vars-extra (list )]
           #:count [count 1]
           ; the number of different witnesses to return
           #:capture-nondeterminism [nondet #t]
           ; if true, we will quantify over the nondetermism collected when evaluating the source and target program
           #:found-core [found-core (lambda (w) (language-witness-context (second w)))] ; different target context for each returned witness
           )

    (let*
        ([assert-store (asserts)] ; save assertion state on entry
         [source (compiler-source comp)]
         [target (compiler-target comp)]
         [e2 ((compiler-compile comp) e1)]
         [p1 ((language-link source) c1 e1)]
         [p2 ((language-link target) c2 e2)]
         [context-relation  (compiler-context-relation comp)]
         [ccomp (if context-relation
                    (context-relation c1 c2)
                    #t)])
      (let*-values ([(b1 nondet1) (if nondet
                                      (capture-nondeterminism ((language-evaluate source) p1))
                                      (values ((language-evaluate source) p1) (list )))]
                    [(b2 nondet2) (if nondet
                                      (capture-nondeterminism ((language-evaluate target) p2))
                                      (values ((language-evaluate target) p2) (list )))])
        (let* ([behavior-relation (compiler-behavior-relation comp)]
               [equality (with-asserts-only (assert (behavior-relation b1 b2)))]
               [language-witnesses (list (language-witness e1 c1 p1 b1) (language-witness e2 c2 p2 b2))]
               [sym-core (found-core language-witnesses)])
          ; 1. Define a recursive loop to generate `num` pairs of expressions (and corresponding contexts)
          (letrec ([loop (λ (num witness-list found-core-list)
                           (if (<= num 0)
                                 witness-list
                               (let* ([sol (if (andmap empty? (list vars vars-extra nondet1 nondet2)) ; If there's nothing to quantify over, we can use the simple solver
                                             (verify
                                                #:assume (assert (and (e1-constraint e1)
                                                                      (c1-constraint e1 c1)
                                                                      (b1-constraint e1 c1 c2 b1)
                                                                      (c2-constraint e1 c2)
                                                                      (b2-constraint e1 c1 c2 b2)
                                                                      ccomp
                                                                      (not (ormap (lambda (t) (equal? sym-core t)) found-core-list))))
                                                #:guarantee (assert (if debug
                                                                        (! (apply && equality))
                                                                        (apply && equality))))
                                             (synthesize 
                                              #:forall (cons vars (cons vars-extra (cons nondet1 nondet2)))
                                              #:assume (assert (and (e1-constraint e1)
                                                                    (c1-constraint e1 c1)
                                                                    (b1-constraint e1 c1 c2 b1)
                                                                    (c2-constraint e1 c2)
                                                                    (b2-constraint e1 c1 c2 b2)
                                                                    ccomp
                                                                    (not (ormap (lambda (t) (equal? sym-core t)) found-core-list)))
                                                               )
                                              #:guarantee (assert (if debug
                                                                      (apply && equality)
                                                                      (! (apply && equality))))))])
                                 (if (unsat? sol)
                                       #f
                                     ; need to concretize context
                                     (let* ([symbolic-witness (weird-component-solution language-witnesses sol)]
                                            [witness (concretize-witness symbolic-witness)]
                                            [core (found-core witness)]
                                            [e-ctx-concrete (list ; e1 c1 e2 c2
                                                             (language-witness-expression (first witness))
                                                             (language-witness-context (first witness))
                                                             (language-witness-expression (second witness))
                                                             (language-witness-context (second witness)))])
                                       (loop (- num 1)
                                             (cons e-ctx-concrete witness-list)
                                             (cons core found-core-list)))))))])

            ; 2. If the `fresh` flag is true, for each generated expression,
            ; synthesize a new context satisfying the relevant constraints            
            (let* ([exprs (loop count (list ) (list ))]) ; exprs is a list of witness
              (clear-asserts!)
              (for-each (lambda (arg) (assert arg)) assert-store) ; restore assertion state
              (cond
                [(equal? exprs #f)
                   #f]
                [else (map (λ (e-ctx-concrete)
                             (let* ([e1-concrete  (first e-ctx-concrete)]
                                    [e2-concrete  (third e-ctx-concrete)]
                                    [c12-witness (if fresh
                                                     (let* ([wit ; new call to find-weird-behavior
                                                                 ; with no universal quantification
                                                             (find-weird-behavior
                                                                 comp
                                                                 #:source-expr e1-concrete
                                                                 #:source-context-bound c1-bound
                                                                 #:source-context-constraint c1-constraint
                                                                 #:source-behavior-constraint b1-constraint
                                                                 #:target-context-bound c2-bound
                                                                 #:target-context-constraint c2-constraint
                                                                 #:target-behavior-constraint b2-constraint
                                                                 #:fresh-witness #f
                                                                 #:forall (list ))])
                                                       (if (unsat? wit)
                                                           (unsafe:raise-arguments-error
                                                            'find-weird-behavior
                                                            "Could not synthesize fresh witness"
                                                            )
                                                           (let ([c1+ (language-witness-context (first (first wit)))]
                                                                 [c2+ (language-witness-context (second (first wit)))]
                                                                 )
                                                             (cons c1+ c2+))))
                                                     (cons (second e-ctx-concrete) (fourth e-ctx-concrete)))] ; c12-witness should be completely concrete
                                    [c1-witness (car c12-witness)]
                                    [c2-witness (cdr c12-witness)]
                                    [p1-witness ((language-link source) c1-witness e1-concrete)]
                                    [b1-witness ((language-evaluate source) p1-witness)]
                                    [p2-witness ((language-link target) c2-witness e2-concrete)]
                                    [b2-witness ((language-evaluate target) p2-witness)]
                                    
                                    )
                               (list (language-witness e1-concrete
                                                       c1-witness
                                                       p1-witness
                                                       b1-witness)
                                     (language-witness e2-concrete
                                                       c2-witness
                                                       p2-witness
                                                       b2-witness))))
                           exprs)]))))))))           
          


; find-changed-behavior query
; provided as a wrapper to find-weird-behavior
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c1:s.t.context c2:r.t.context,
;    r.ctx-relation(c1, c2)
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
; Returns a list of concrete witness, each of which will have a different source context
(define find-changed-behavior
  (lambda (comp
           v1
           #:source-context-bound [bound-c1 #f]
           #:source-context-where [where-c1 (lambda (v1 c1) #t)]
           #:target-context-bound [bound-c2 #f]
           #:target-context-where [where-c2 (lambda (v1 c2) #t)]
           #:source-behavior-where [where-b1 (lambda (v1 c1 c2 b1) #t)]
           #:target-behavior-where [where-b2 (lambda (v1 c1 c2 b2) #t)]
           #:count [witness-count #f])
    (unwrap-witness witness-count (find-weird-behavior comp
                         #:source-expr v1
                         #:source-context-bound bound-c1
                         #:source-context-constraint where-c1
                         #:target-context-bound bound-c2
                         #:target-context-constraint where-c2
                         #:source-behavior-constraint where-b1
                         #:target-behavior-constraint where-b2
                         #:fresh-witness #f
                         #:forall (list ) ; don't quantify over c2 in changed-behavior
                         #:count (if witness-count witness-count 1)
                         #:capture-nondeterminism #f
                         #:found-core (lambda (w) (language-witness-context (first w)))))))




; find-changed-component query
; provided as a wrapper to find-weird-behavior
; for backward compatibility
; Solve the following synthesis problem:
; (\lambda r).
;   Exists v:r.s.expression
;     find-changed-behavior r v
; Returns a list of witness if #:count is used
; each of which will have a different source expression
(define find-changed-component
  (lambda (comp
           #:source-expression-bound [bound-v1 #f]
           #:source-expression-where [where-v1 (lambda (v1) #t)]
           #:source-context-bound [bound-c1 #f]
           #:source-context-where [where-c1 (lambda (v1 c1) #t)]
           #:target-context-bound [bound-c2 #f]
           #:target-context-where [where-c2 (lambda (v1 c2) #t)]
           #:source-behavior-where [where-b1 (lambda (v1 c1 c2 b1) #t)]
           #:target-behavior-where [where-b2 (lambda (v1 c1 c2 b2) #t)]
           #:count [witness-count #f])
    (unwrap-witness witness-count
                    (find-weird-behavior comp
                                         #:source-expr-bound bound-v1
                                         #:source-expr-constraint where-v1
                                         #:source-context-bound bound-c1
                                         #:source-context-constraint where-c1
                                         #:target-context-bound bound-c2
                                         #:target-context-constraint where-c2
                                         #:source-behavior-constraint where-b1
                                         #:target-behavior-constraint where-b2
                                         #:fresh-witness #f
                                         #:forall (list ) ; don't quantify over c2 in changed-behavior
                                         #:count (if witness-count witness-count 1)
                                         #:capture-nondeterminism #f
                                         #:found-core (lambda (w) (language-witness-expression (first w)))))))


; find-weird-computation query
; provided as a wrapper to find-weird-behavior
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
; Returns a list of concrete witness, each of which will have a different target context
(define find-weird-computation
  (lambda (comp
           v1
           #:source-context-bound [bound-c1 #f]
           #:source-context-where [where-c1 (lambda (v1 c1) #t)]
           #:target-context-bound [bound-c2 #f]
           #:target-context-where [where-c2 (lambda (v1 c2) #t)]
           #:source-behavior-where [where-b1 (lambda (v1 c1 c2 b1) #t)]
           #:target-behavior-where [where-b2 (lambda (v1 c1 c2 b2) #t)]
           #:count [witness-count #f])
    (unwrap-witness witness-count
                    (find-weird-behavior comp
                         #:source-expr v1
                         #:source-context-bound bound-c1
                         #:source-context-constraint where-c1
                         #:target-context-bound bound-c2
                         #:target-context-constraint where-c2
                         #:source-behavior-constraint where-b1
                         #:target-behavior-constraint where-b2
                         ; don't quantify over c2 in changed-behavior
                         #:count (if witness-count witness-count 1)))))

; find-weird-component query
; provided as a wrapper to find-weird-behavior
; Solve the following synthesis problem:
; Exists v1:r.s.expression,
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
; Returns a list of concrete witness, each of which will have a different source expression
(define find-weird-component
  (lambda (comp
           #:source-expression-bound [bound-v1 #f]
           #:source-expr [e1 (make-symbolic-var (language-expression (compiler-source comp))
                                                bound-v1)]
           #:source-expression-where [where-v1 (lambda (v1) #t)]
           #:source-context-bound [bound-c1 #f]
           #:source-context-where [where-c1 (lambda (v1 c1) #t)]
           #:target-context-bound [bound-c2 #f]
           #:target-context [c2 (make-symbolic-var (language-context (compiler-target comp)) bound-c2)]
           #:target-context-where [where-c2 (lambda (v1 c2) #t)]
           #:source-behavior-where [where-b1 (lambda (v1 c1 c2 b1) #t)]
           #:target-behavior-where [where-b2 (lambda (v1 c1 c2 b2) #t)]
           #:capture-nondeterminism [nondet #t]
           #:count [witness-count #f])
    (unwrap-witness witness-count
                    (find-weird-behavior comp
                         #:source-expr-bound bound-v1
                         #:source-expr e1
                         #:source-expr-constraint where-v1
                         #:source-context-bound bound-c1
                         #:source-context-constraint where-c1
                         #:target-context-bound bound-c2
                         #:target-context c2
                         #:target-context-constraint where-c2
                         #:source-behavior-constraint where-b1
                         #:target-behavior-constraint where-b2
                         ; don't quantify over c2 in changed-behavior
                         #:count (if witness-count witness-count 1)
                         #:capture-nondeterminism nondet
                         #:found-core (lambda (w) (language-witness-context (first w)))))))


; show v1, c2 and b2
(define (display-weird-component vars out)
  (cond
    [(equal? vars #f) (out (format "No weird behavior found~n"))]
    [else
     (let* ([source-vars (first vars)]
            [target-vars (second vars)])
       (out (format
             "Expression ~a~n has emergent behavior ~a~n witnessed by target-level context ~a~n"
             (language-witness-expression source-vars)
             (language-witness-behavior target-vars)
             (language-witness-context target-vars))))
       ]))

; alias (display-weird-component)
(define (display-weird-behavior vars out)
  (display-weird-component vars out))


(define/contract (expr-in-witness-list? e witness-list)
  (-> any/c (listof language-witness?) boolean?)
  (ormap (λ (w) (equal? e (language-witness-expression w)))
         witness-list))

; `es` is a list of pairs of expressions and contexts
(define (expr-in-expr-list? e es)
  (ormap (λ (e-ctx) (equal? e (car e-ctx))) es))

; TODO: make sure the assertion state is not changing from this...
(define synthesize-fresh-context
  (λ (lang
      #:expr               e
      #:context-bound      bound-c
      #:context-constraint ctx-constraint
      #:valid-constraint   valid-constraint
      )
    (let* ([ctx-witness (make-symbolic-var (language-context lang) bound-c)]
           [p-witness ((language-link lang) ctx-witness e)]
         #;[b-witness ((language-evaluate lang) p-witness)]
           [sol (synthesize #:forall (list )
                            #:guarantee (assert (and (ctx-constraint ctx-witness)
                                                     (valid-constraint p-witness)
                                                     ))
                            )]
           )
      (if (unsat? sol)
          (unsafe:raise-arguments-error
             'synthesize-fresh-context
             "Could not synthesize a fresh context from the given constraints"
             "language" lang
             "e" (bonsai-pretty e)
             "context bound" (bonsai-pretty bound-c)
;             "context-constraint" ctx-constraint
;             "valid-constraint"   valid-constraint
             )
          (concretize ctx-witness sol))
      )))


(define/contract find-gadget
  (->* (language?
        (-> any/c any/c boolean?))
       (
      #:valid (-> any/c boolean?)

      #:expr-bound (or/c #f integer?)
      #:expr any/c
      #:expr-constraint (-> any/c boolean?)
      #:context-bound (or/c #f integer?)
      #:context any/c
      #:context-constraint (-> any/c boolean?)

      #:fresh-witness boolean?
      #:debug boolean?
      #:forall any/c
      #:forall-extra any/c
      #:count integer?
      )
      (or/c #f (listof language-witness?))
       )
  (λ (lang
      spec                 ; (-> program? behavior? boolean?)

      #:valid              [valid-program (λ (p) #t)] ; (-> program? boolean?)
                           ; Constrain the search to expression-context pairs
                           ; that satisfy the `valid-program` predicate


      #:expr-bound         [bound-e #f] ; (or/c #f natural?)
      #:expr               [e (make-symbolic-var (language-expression lang) bound-e)]
                           ; The `#:expr` argument allows the user to provide
                           ; a concrete expression argument instead of generating a
                           ; symbolic one using `make-symbolic-var`. This could
                           ; be used either during debugging, e.g. a unit test
                           ; for the synthesis query, or a sketch consisting of
                           ; symbolic variables contained inside a frame.
      #:expr-constraint    [e-constraint (λ (x) #t)] ; (-> expr? boolean?) 
                           ; The `#:expr-constraint` argument allows the user to
                           ; constrain the search to expressions that satisfy
                           ; the constraint.

      #:context-bound      [bound-c #f] ; (or/c #f natural?)
      #:context            [ctx (make-symbolic-var (language-context lang) bound-c)]
      #:context-constraint [ctx-constraint (λ (x) #t)] ; (-> context? boolean?)

      #:fresh-witness      [fresh #t]
                           ; if `#t`, will generate a fresh context satisfying
                           ; `valid-program` and `ctx-constraint` to witness the
                           ; satisfiability of the query. This is useful due to
                           ; the `forall` quantifier.
                           ;
                           ; if `#f`, will not generate a fresh context, e.g. if
                           ; you are providing a concrete argument for the
                           ; context or not including any `forall` quantifiers

      #:debug              [debug #f]
                           ; if debug is set, then we will attempt to synthesize
                           ; an expression that violates the specification

      #:forall             [vars (if debug
                                     (list ) ; no quantifiers for debugging
                                     ctx)]   ; any term containing symbolic
                                             ; variables to be quantified over
                           ; Use the `#:forall` argument to replace the default
                           ; set of quantified variables
      #:forall-extra       [vars-extra (list )]
                           ; Use the `#:forall-extra` argument to add to the
                           ; default set of quantified variables without
                           ; replacing it

      #:count              [count 1]
                           ; the number of different witnesses to return

      )
    (let*
        ([p ((language-link lang) ctx e)]
         [b ((language-evaluate lang) p)]
         )
      ; 1. Define a recursive loop to generate `num` pairs of expressions (and corresponding contexts)
      (letrec ([loop (λ (num witness-list)
                       (if (<= num 0)
                           witness-list
                           (let* ([sol (synthesize
                                        #:forall (cons vars vars-extra)
                                        #:assume (assert (and (valid-program p)
                                                              (ctx-constraint ctx)
                                                              (e-constraint e)
                                                              (not (expr-in-expr-list? e witness-list))
                                                              ))
                                        #:guarantee (assert (if debug
                                                                (not (spec p b))
                                                                (spec p b))))
                                       ])
                             (if (unsat? sol)
                                 #f
                                 ; need to concretize context
                                 (let* ([e-ctx-concrete (concretize (cons e ctx) sol)])
                                   (loop (- num 1)
                                         (cons e-ctx-concrete witness-list)))
                                   ))))])
        ; 2. If the `fresh` flag is true, for each generated expression,
        ; synthesize a new context satisfying the relevant constraints
        (let* ([exprs (loop count (list ))]) ; exprs is a list of expression-context pairs
          (clear-asserts!)
          (cond
            [(equal? exprs #f) #f]
            [else (map (λ (e-ctx-concrete)
                 (let* ([e-concrete  (car e-ctx-concrete)]
                        [ctx-witness (if fresh
                                         (synthesize-fresh-context lang
                                            #:expr e-concrete
                                            #:context-bound bound-c
                                            #:context-constraint ctx-constraint
                                            #:valid-constraint valid-program
                                            )
                                         (cdr e-ctx-concrete)
                                         )]; ctx-witness should be completely concrete
                        [p-witness ((language-link lang) ctx-witness e-concrete)]
                        [b-witness ((language-evaluate lang) p-witness)]
                        )
                   (language-witness e-concrete
                                     ctx-witness
                                     p-witness
                                     b-witness)))
               exprs)])
          )))))


; DEBUGGING find-gadget:
; If the gadget fails to synthesize, what could be wrong?

; 1. The specification is unsatisfiable.
;
; Solution: Identify a gadget/context pair that satisfies the specification. Use
;   unit tests (possibly using parameterize debug?) to check that the
;   specification is satisfied for a concrete example. If that succeeds, use
;   #:expr and #:context arguments to check that the find-gadget query succeeds
;   on that concrete argument. Use the argument (#:fresh-witness #f).

; 2. The specification is satisfied for a particular unit test, but fails when
;   quantifying over symbolic variables.
;
; Solution: Use #:forall or #:forall-extra to limit or extend the variables
;   being quantified over. For example, set (#:forall (list )) to stop universal
;   quantification over contexts. If synthesis succeeds when removing one or
;   more quantifiers, use the (#:debug #t) argument to search for
;   counterexamples---instantiations of the variables that cause the
;   specification to fail.

; 2. The expression or context bound is too small
; 
; Solution: Assume you know a gadget/context pair that satisfies Solution 1.
;   Remove the #:expr (resp #:context) argument and replace with
;   (#:expr-constraint (λ (e) (equal? e concrete-e))). If this fails, increase
;   the #:expr-bound argument until it succeeds.

; 3. The witnessed behavior is ERROR and/or the witnessed context is incompatible.
;
; Solution: If this happens when given a concrete context argument, add the
;   argument (#:fresh-witness #f), which will stop the query from generating a
;   new argument and instead reuse the one provided. Otherwise, add a #:valid
;   constraint or #:context-contraint to limit the search to contexts that
;   provide meaningful results.


; Source: format-str, (arg-list x acc), cons, run
; Goal: find a format-str s.t. given a ctx (arg-list, acc), increment the acc. (input is Source, v-ctx:Context -> bool (in addition to the one in source), spec:Context -> behavior -> bool
#;(define-syntax (make-query-gadget stx)
  (syntax-parse stx
    [(_ lang valid-program specification
        bound-v
        bound-c)
     #`(unsafe:generator
        ()
        (let*
            ([c1 (make-symbolic-var (language-context lang) bound-c)]
                 [v1 (make-symbolic-var (language-expression lang) bound-v)]
                 [p1 ((language-link lang) c1 v1)]
                 [b1 ((language-evaluate lang) p1)]
                 ; Creating a second context to return as example
                 [c2 (make-symbolic-var (language-context lang) bound-c)]
                 [p2 ((language-link lang) c2 v1)]
                 [b2 ((language-evaluate lang) p2)])
          (let loop ([found (list)])
            (let* ([tmpsol (synthesize
                     #:forall c1
                     #:assume (assert (and (valid-program p1)
                                           (not (ormap (lambda (t) (equal? v1 t)) found))))
                     #:guarantee (assert (specification p1 b1)))])
              (if (unsat? tmpsol)
                  #f
                  (let* ([symbolic-witness (solution (list (language-witness v1 c2 p2 b2)) tmpsol)]
                         
                         [witness (concretize-witness symbolic-witness)]
                         ; Projecting v1 out of the concrete witness
                         [core (language-witness-expression (first witness))])
                    (unsafe:yield witness)
                    (loop (cons core found))))))))]))

; Usage: find-gadget lang valid spec
;                    (#:expression-bound bound-v)
;                    (#:context-bound bound-c)
;                    (#:count num)
; where
; - [lang] is a SEEC language
; - [valid] is a predicate characterizing valid [lang] programs (pairs of
;     expressions and contexts)
; - [spec] is the desired property that takes two arguments: the program and the
;     behavior resulting from evaluating the program
#;(define-syntax (find-gadget stx)
    (syntax-parse stx
    [(_ lang valid-program specification
        (~seq
         (~optional
          (~seq #:expression-bound bound-v)
          #:defaults ([bound-v #'#f]))
         (~optional
          (~seq #:context-bound bound-c)
          #:defaults ([bound-c #'#f]))
         (~optional
          (~seq #:count witness-count)
          #:defaults ([witness-count #'#f]))))
     #`(let*
           ([assert-store (asserts)] ; save assertions on entry
            [gen (make-query-gadget lang valid-program specification bound-v bound-c)]
            [witness (run-query #:count witness-count gen)])
         (clear-asserts!)
         (for-each (lambda (arg) (assert arg)) assert-store) ; restore entry assertions
         witness)]))



(define/contract (display-gadget vars out)
  (-> (or/c #f (listof language-witness?)) any/c any)
  (cond
    [(equal? vars #f) (out (format "Gadget failed to synthesize~n"))]
    [(equal? vars (list )) (out (format "All gadgets synthesized~n"))]
    [else
     (let* ([lang-vars (first vars)])
       (out (format
          "Expression ~a~n is a gadget for the provided specification, as witnessed by behavior ~a~n in context ~a~n"
          (language-witness-expression lang-vars)
          (language-witness-behavior lang-vars)
          (language-witness-context lang-vars)))
       (display-gadget (rest vars) out)
     )]
    ))


(define (display-list list)
  (for-each displayln list)
  (void))

(define (seec-add n1 n2)
  (bonsai-integer (+ (bonsai-integer-value n1)
                     (bonsai-integer-value n2))))

(define (seec-subtract n1 n2)
  (bonsai-integer (- (bonsai-integer-value n1)
                     (bonsai-integer-value n2))))


(define (clear-all-queries)
  (begin
    (clear-asserts!)
    (clear-terms!)))
