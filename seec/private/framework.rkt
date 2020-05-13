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
         display-witness)

(require (for-syntax syntax/parse)
         "bonsai2.rkt")

#|

 This file provides structures to reason abstractly about weird machines.

  "language" represents a language in the weird-machine framework.

  "compiler" represent a compiler in the weird-machine framework.
    In addition to the source and a target language structures,
    it contains trusted relations over behaviors and contexts and
    and a compilation function



TODO: deal with nondet
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

; Question: this definition of a compiler doesn't consider
; nondeterminism. Could add nondet as part of ; context, or have it be
; a part of linking.

(struct witness (program context behavior solution) #:transparent)

; find-changed-behavior: {r:scomp} r.source.expression -> witness + #f
; Solve the following synthesis problem:
; (\lambda v).
; Exists c1:s.t.context c2:r.t.context,
;    r.ctx-relation(c1, c2)
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax (find-changed-behavior stx)
  (syntax-parse stx
    [(_ comp v)
     #`(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
              [c1 (make-symbolic-var (language-context source))]
              [c2 (make-symbolic-var (language-context target))]
              [source-evaluate (language-evaluate source)]
              [source-link (language-link source)]
              [b1 (source-evaluate (source-link c1 v))]
              [target-evaluate (language-evaluate target)]
              [target-link (language-link target)]
              [compile (compiler-compile comp)]
              [b2 (target-evaluate (target-link c2 (compile v)))]
              [context-relation (compiler-context-relation comp)]
              [ccomp (context-relation c1 c2)]
              [behavior-relation (compiler-behavior-relation comp)]
              [equality (with-asserts-only (assert (behavior-relation b1 b2)))]
              [sol (verify
                    #:assume (assert ccomp)
                    #:guarantee (assert (apply && equality)))])
         (if (unsat? sol)
             #f
             (witness v c2 b2 sol)))]))

; find-emergent-computation :
;     {r:comp} r.source.expression -> witness + #f
; Solve the following synthesis problem:
; (\lambda v).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax (find-weird-computation stx)
  (syntax-parse stx
    [(_ comp v)
     #`(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
              [c1 (make-symbolic-var (language-context source))]
              [c2 (make-symbolic-var (language-context target))]
              [source-evaluate (language-evaluate source)]
              [source-link (language-link source)]
              [b1 (source-evaluate (source-link c1 v))]
              [target-evaluate (language-evaluate target)]
              [target-link (language-link target)]
              [compile (compiler-compile comp)]
              [b2 (target-evaluate (target-link c2 (compile v)))]
              [context-relation  (compiler-context-relation comp)]
              [ccomp (context-relation c1 c2)]
              [behavior-relation (compiler-behavior-relation comp)]
              [equality (with-asserts-only (assert (behavior-relation b1 b2)))]
              [sol (synthesize
                    #:forall c1
                    #:assume (assert ccomp)
                    #:guarantee (assert (! (apply && equality))))])
         (if (unsat? sol)
             #f
             (witness v c2 b2 sol)))]))

(define (concretize-witness sym-witness)
  (let ([program  (witness-program sym-witness)]
        [context  (witness-context sym-witness)]
        [behavior (witness-behavior sym-witness)]
        [solution (witness-solution sym-witness)])
    (let ([concretized (concretize (list program context behavior) solution)])
      (witness (first concretized)
               (second concretized)
               (third concretized)
               solution))))

(define (display-witness witness)
  (if witness
      (let ([concretized (concretize-witness witness)])
        (printf
          "Expression ~a~n    has emergent behavior ~a~n    witnessed by target-level context ~a~n"
          (witness-program concretized)
          (witness-behavior concretized)
          (witness-context concretized)))
      (displayln "Failed to synthesis emergent computation")))

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
