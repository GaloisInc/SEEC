#lang rosette/safe

(provide define-language
         define-compiler
         (struct-out language)
         (struct-out compiler)
         find-changed-behavior
         find-weird-computation
         find-weird-component
         (struct-out witness)
         concretize-witness
         display-changed-behavior
         display-weird-component)

(require (for-syntax syntax/parse)
         "bonsai2.rkt")

#|

 This file provides structures to reason abstractly about weird machines.

  "language" represents a language in the weird-machine framework.

  "compiler" represent a compiler in the weird-machine framework.
    In addition to the source and a target language structures,
    it contains trusted relations over behaviors and contexts and
    and a compilation function



TODO: give more examples with nondet (e.g. buggy set)
TODO: pack the vars in witness in a structure
TODO: create more macros:
   e.g. set e.g. 1 where verify is used instead of synthesize
   e.g. n-to-z style where C2 is computed from C1

|#

; Predicated syntactic class
; For the moment, we decouple pred (symbolic restrictions) from gen
; (syntactic generation)
;   generator : () -> bonsai-tree
;   predicate : bonsai-tree -> bool
(struct predsyn (generator predicate))

(define-syntax (define-predsyn stx)
  (syntax-parse stx
    [(_ grammar pat pred bound)
     #`(predsyn (thunk (grammar pat bound)) pred)]))

(define (make-symbolic-var ps)
  (let ([s ((predsyn-generator ps))])
    (assert ((predsyn-predicate ps) s))
    s))

; A language
; expression : predsyn
; context : predsyn
; link : ctxt -> expr -> program
; evaluate : program -> behavior
(struct language (expression context link evaluate))

(begin-for-syntax
  (define-splicing-syntax-class predsyn
    (pattern (~seq nt:id #:size n:expr)
             #:with gen #'nt
             #:with pred #'(lambda (t) #t)
             #:with bound #'n)
    (pattern (~seq nt:id #:size n:expr #:where p:expr)
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
        #:context-relation crel
        #:compile compile)
     #`(define name (compiler source target brel crel compile))]))



;(struct variables (expression context program behavior) #:transparent)
(struct witness (source-vars target-vars solution) #:transparent)


; find-changed-behavior: {r:scomp} r.source.expression -> witness + #f
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c1:s.t.context c2:r.t.context,
;    r.ctx-relation(c1, c2)
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
(define-syntax (find-changed-behavior stx)
  (syntax-parse stx
    [(_ comp v1)
     #`(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
              [c1 (make-symbolic-var (language-context source))]
              [c2 (make-symbolic-var (language-context target))]
              [source-evaluate (language-evaluate source)]
              [source-link (language-link source)]
              [p1 (source-link c1 v1)]
              [b1 (source-evaluate p1)]
              [target-evaluate (language-evaluate target)]
              [target-link (language-link target)]
              [compile (compiler-compile comp)]
              [v2 (compile v1)]
              [p2 (target-link c2 v2)]
              [b2 (target-evaluate p2)]
              [context-relation (compiler-context-relation comp)]
              [ccomp (context-relation c1 c2)]
              [behavior-relation (compiler-behavior-relation comp)]
              [equality (with-asserts-only (assert (behavior-relation b1 b2)))]
              [sol (verify
                    #:assume (assert ccomp)
                    #:guarantee (assert (apply && equality)))])
         (if (unsat? sol)
             #f
             (witness (list v1 c1 p1 b1) (list v2 c2 p2 b2) sol)))]))

; find-emergent-computation :
;     {r:comp} r.source.expression -> witness + #f
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
(define-syntax (find-weird-computation stx)
  (syntax-parse stx
    [(_ comp v1)
     #`(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
              [c1 (make-symbolic-var (language-context source))]
              [c2 (make-symbolic-var (language-context target))]
              [source-evaluate (language-evaluate source)] 
              [source-link (language-link source)]
              [target-evaluate (language-evaluate target)] 
              [target-link (language-link target)]
              [compile (compiler-compile comp)]
              [context-relation  (compiler-context-relation comp)]
              [ccomp (context-relation c1 c2)]
              [behavior-relation (compiler-behavior-relation comp)]
              [v2 (compile v1)]
              [p1 (source-link c1 v1)]
              [p2 (target-link c2 v2)])
         (let*-values ([(b1 nondet1) (capture-nondeterminism (source-evaluate p1))] ; capture nondet
                       [(b2 nondet2) (capture-nondeterminism (target-evaluate p2))])
           (let*
               ([equality (with-asserts-only (assert (behavior-relation b1 b2)))]
                [sol (synthesize
                      #:forall (cons c1 (cons nondet1 nondet2)) ; quantify over nondet
                      #:assume (assert ccomp) 
                      #:guarantee (assert (! (apply && equality))))])
             (if (unsat? sol)
                 #f
                 (witness (list v1 c1 p1 b1) (list v2 c2 p2 b2) sol)))))]))

(define (concretize-witness sym-witness)
  (let ([source-vars (witness-source-vars sym-witness)]
        [target-vars (witness-target-vars sym-witness)]
        [solution (witness-solution sym-witness)])
    (let ([concretized (concretize (append source-vars target-vars) solution)])
      (list (take concretized 4) (drop concretized 4)))))


#;(define (display-witness witness)
  (if witness
      (let ([concretized (concretize-witness witness)])
        (printf
          "Expression ~a~n    has emergent behavior ~a~n    witnessed by target-level context ~a~n"
          (witness-program concretized)
          (witness-behavior concretized)
          (witness-context concretized)))
      (displayln "Failed to synthesis emergent computation")))


; show (c1, v1) ~> b1 and (c2, v2) ~> b2
(define (display-changed-behavior witness)
  (if witness
      (let* ([vars (concretize-witness witness)]
             [source-vars (first vars)]
             [target-vars (second vars)])
        (begin 
          (printf
           "Expression ~a~n has behavior ~a~n in source-level context ~a~n"
           (first source-vars)
           (fourth source-vars)
           (second source-vars))
          (printf
           "Compiles to ~a~n with emergent behavior ~a~n in target-level context ~a~n"
           (first target-vars)
           (fourth target-vars)
           (second target-vars))))
      (displayln "Failed to synthesis a changed behavior")))

; find-weird-component
; find-weird-component: comp -> witness + #f
; (\lambda r).
;   Exists v:r.s.expression
;     find-exploit r v
(define-syntax (find-weird-component stx)
  (syntax-parse stx
    [(_ comp)
     #`(let* ([v (make-symbolic-var
                  (language-expression (compiler-source comp)))])
         (find-weird-computation comp v))]))


; show v1, c2 and b2
(define (display-weird-component witness)
  (if witness
      (let* ([vars (concretize-witness witness)]
             [source-vars (first vars)]
             [target-vars (second vars)])
        (printf
          "Expression ~a~n has emergent behavior ~a~n witnessed by target-level context ~a~n"
          (first source-vars)
          (fourth target-vars)
          (second target-vars)))
      (displayln "Failed to synthesis a changed behavior")))



;
; Source: format-str, (arg-list x acc), cons, run
; Target:  ", run'
; Compiler: ?
; Goal: find a format-str s.t. given a ctx (arg-list, acc), increment the acc. (input is Source, v-ctx:Context -> bool (in addition to the one in source), spec:Context -> behavior
