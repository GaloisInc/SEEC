#lang rosette/safe

(provide define-language
         define-compiler
         (struct-out language)
         (struct-out compiler)
         find-changed-behavior
         find-weird-computation
         find-weird-component
         (struct-out solution)
         concretize-witness
         display-changed-behavior
         display-weird-component
         find-gadget
         display-gadget
         display-list
         seec-add
         seec-subtract
         link
         evaluate
         link-and-evaluate
         compile)

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
TODO: pack the vars in solution in a structure
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

(define (link language expr context)
  ((language-link language) expr context))

(define (evaluate language program)
  ((language-evaluate language) program))

(define (link-and-evaluate language expr context)
  (evaluate language (link language expr context)))

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


; find-changed-behavior: {r:scomp} r.source.expression -> solution + failure
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
              [ccomp (if context-relation
                         (context-relation c1 c2)
                         #t)]
              [behavior-relation (compiler-behavior-relation comp)]
              [equality (with-asserts-only (assert (behavior-relation b1 b2)))]
              [sol (verify
                    #:assume (assert ccomp)
                    #:guarantee (assert (apply && equality)))])
         (if (unsat? sol)
             (failure "Failed to synthesize a changed behavior")
             (changed-behavior-solution (list (language-witness v1 c1 p1 b1) (language-witness v2 c2 p2 b2)) sol)))]))

; find-emergent-computation :
;     {r:comp} r.source.expression -> solution + failure
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
              [ccomp (if context-relation
                         (context-relation c1 c2)
                         #t)]
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
                 (failure "Failed to synthesize a weird computation")
                 (weird-component-solution (list (language-witness v1 c1 p1 b1) (language-witness v2 c2 p2 b2)) sol)))))]))


; concretize all vars included in the solution, return a list of language-witness with concrete vars
(define (concretize-witness sym-solution)
  (let* ([vars (solution-witness sym-solution)]
        [unpacked-vars (map unpack-language-witness vars)]
        [model (solution-model sym-solution)]
        [list-vars (foldr append (list) unpacked-vars)]
        [concretized (concretize list-vars model)])
      (pack-language-witness concretized)))


#;(define (display-solution solution)
  (if solution
      (let ([concretized (concretize-witness solution)])
        (printf
          "Expression ~a~n    has emergent behavior ~a~n    witnessed by target-level context ~a~n"
          (solution-program concretized)
          (solution-behavior concretized)
          (solution-context concretized)))
      (displayln "Failed to synthesis emergent computation")))


; show (c1, v1) ~> b1 and (c2, v2) ~> b2
(define (display-changed-behavior solution out)
  (let* ([vars (concretize-witness solution)]
         [source-vars (first vars)]
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
            (language-witness-context target-vars))))))

; find-weird-component
; find-weird-component: comp -> solution + failure
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
(define (display-weird-component solution out)
  (let* ([vars (concretize-witness solution)]
         [source-vars (first vars)]
         [target-vars (second vars)])
    (out (format
          "Expression ~a~n has emergent behavior ~a~n witnessed by target-level context ~a~n"
          (language-witness-expression source-vars)
          (language-witness-behavior target-vars)
          (language-witness-context target-vars)))))




#|
 Notes for Printf's uses of the framework:

LANG
Expression:
fmt (format strings)
Context:

Behavior:
(res, config)
Program:
(f:fmt, args:vlist, conf:config)
Link:

Evaluate:
interp-fmt-unsafe

OTHER:
Valid-program:

conf is of the form (,(printf-lang integer 1) mnil)
AND
fmt-consistent-with-vlist? f args

Specification:
 get f and conf and arg out of program
  is-constant-add f 1 args conf

|#

; Source: format-str, (arg-list x acc), cons, run
; Goal: find a format-str s.t. given a ctx (arg-list, acc), increment the acc. (input is Source, v-ctx:Context -> bool (in addition to the one in source), spec:Context -> behavior -> bool
(define-syntax (find-gadget stx)
  (syntax-parse stx
    [(_ lang valid-program specification)
     #`(let* ([c1 (make-symbolic-var (language-context lang))]
              [v1 (make-symbolic-var (language-expression lang))]
              [p1 ((language-link lang) c1 v1)]
              [b1 ((language-evaluate lang) p1)]
              ; Creating a second context to return as example
              [c2 (make-symbolic-var (language-context lang))]
              [p2 ((language-link lang) c2 v1)]
              [b2 ((language-evaluate lang) p2)]
              [sol (synthesize
                    #:forall c1
                    #:assume (assert (valid-program p1))
                    #:guarantee (assert (specification p1 b1)))])
         (if (unsat? sol)
             (failure "Failed to synthesize a gadget")
             (solution (list (language-witness v1 c1 p1 b1)) sol)))]))

(define (display-gadget solution out)
  (let* ([vars (concretize-witness solution)]
         [lang-vars (first vars)])
    (out (format
          "Expression ~a~n is a gadget for the provided specification, as witnessed by behavior ~a~n in context ~a~n"
          (language-witness-expression lang-vars)
          (language-witness-behavior lang-vars)
          (language-witness-context lang-vars)))))

(define (display-list list)
  (for-each displayln list)
  (void))

(define (seec-add n1 n2)
  (bonsai-integer (+ (bonsai-integer-value n1)
                     (bonsai-integer-value n2))))

(define (seec-subtract n1 n2)
  (bonsai-integer (- (bonsai-integer-value n1)
                     (bonsai-integer-value n2))))
