#lang rosette/safe
(provide define-language
         define-compiler
         (struct-out language)
         (struct-out compiler)
         find-simple-exploit
         find-exploit
         find-exploitable-component)
(require (for-syntax syntax/parse))
(require racket/match)

#|

 This file provides structures to reason abstractly about weird machines.

  "language" represents a language in the weird-machine framework.

  "compiler" represent a compiler in the weird-machine framework.
    In addition to the source and a target language structures,
    it contains trusted relations over behaviors and contexts and
    and a compilation function
          


TODO: fix find-exploit and unsafe
TODO: deal with nondet
TODO: create more macros:
   e.g. set e.g. 1 where verify is used instead of synthesize
   e.g. n-to-z style where C2 is computed from C1
   

|#



; Predicated syntactic class
; For the moment, we decouple pred (symbolic restrictions) from gen (syntactic generation)
(struct predsyn (gen; () -> bonsai-tree 
                 pred ; name -> bool - nothing
                 ))


(define-syntax (define-predsyn stx)
  (syntax-parse stx
    [(_ grammar pat pred bound)
        #`(predsyn (lambda ()
                       (grammar pat bound)) pred)]
    ))

(define (make-symbolic-var ps)
  (let ([s ((predsyn-gen ps))])
    (assert ((predsyn-pred ps) s))
    s))




#| example
(make-predsyn exp 'interaction (lambda (e) #t))
(make-predsyn set 'list valid-set?)
|#


; A language 
(struct language (exp ; predsyn
              ctx   ; predsyn
              ;behavior   ; nothing
              ;program    ; nothing
              link       ; context -> expression -> program
              evaluate)) ; program -> behavior
#;(define-for-syntax (make-language name grammar exp vexp bexp ctx vctx bctx link eval)
  #`(define #,name
    (let* ([predexp (define-Predsyn #,grammar '#,exp '#,vexp #,bexp)]
           [predctx (define-Predsyn #,grammar '#,ctx '#,vctx #,bctx)])
      (lang predexp predctx #,link #,eval))))  

(define-syntax (define-language stx)
  (syntax-parse stx
    [(_ name grammar exp vexp bexp ctx vctx bctx link eval)
     #`(define name
         (let* ([predexp (define-predsyn grammar exp vexp bexp)]
                [predctx (define-predsyn grammar ctx vctx bctx)])
           (language predexp predctx link eval)))]
    [(_ name grammar exp bexp ctx bctx link eval)
     #`(define-language name grammar exp (lambda (e) #t) bexp ctx (lambda (c) #t) bctx link eval)]      
       ))
    

#| example:
 (define-lang source 
    'set-api exp 'list 'valid-set? 'list (cons 'list 'interaction) cons 'abstract-interpret)


 (define-lang target 
    'set-api exp set  'list (cons 'list 'interaction) cons concrete-interpret)

 (define-lang buggy-target 
    'set-api exp set 'list (cons 'list 'interaction) cons buggy-concrete-interpret)




          
|#


; A compiler between languages consists of:
; source: A lang structure standing in as source 
; target: "                            as target
; brel (behavior-relation): equivalence class for source and target's behaviors
; crel (context-relation) : "'s context
; compile: function from source-expression to target-expression
; contextcompile: optionally, a function from source.ctx to source.target
(struct compiler (source target brel crel compile))

(define-syntax (define-compiler stx)
  (syntax-parse stx
    [(_ name source target brel crel compile)
     #`(define name (compiler source target brel crel compile))]
    ))

#| example:

(define-comp buggy-comp source target equal? equal? id)

Question: this doesn't consider nondet. Could add nondetas part of context, or have it be a part of linking. 
          if as part of con


|#



#|
; find-simple-exploit: {r:scomp} r.source.expression -> (rel-target-context * SAT) + ()
; Solve the following synthesis problem:
; (\lambda v).
; Exists c2:r.t.context,
;     r.context-compile(c1) = c2 ->
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax (find-simple-exploit stx)
  (syntax-parse stx
    [(_ comp compilecontext v)
     #`(let* ([source (Comp-source comp)]
              [target (Comp-target comp)]
              [c1 (make-symbolic-var (language-ctx source))]
              [c2 (compilecontext c1)]
              [b1 ((language-evaluate source) ((language-link source) c1 v))]
              [b2 ((language-evaluate target) ((language-link target) c2 ((Comp-compile comp) v)))]
              [equality (assert ((Comp-brel comp) b1 b2))]
              [sol (verify equality)])
         (if (unsat? sol)
             '()
             (list c2 sol)))]
             ;(let ([instance (concretize c2 sol)])
              ; (list instance sol))))]
     ))

|#

; find-simple-exploit: {r:scomp} r.source.expression -> (rel-target-context * SAT) + ()
; Solve the following synthesis problem:
; (\lambda v).
; Exists c1:s.t.context c2:r.t.context,
;    r.ctx-relation(c1, c2)
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax (find-simple-exploit stx)
  (syntax-parse stx
    [(_ comp v)
     #`(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
              [c1 (make-symbolic-var (language-ctx source))]
              [c2 (make-symbolic-var (language-ctx target))]
              [b1 ((language-evaluate source) ((language-link source) c1 v))]
              [b2 ((language-evaluate target) ((language-link target) c2 ((compiler-compile comp) v)))]
              [ccomp ((compiler-crel comp) c1 c2)]
              [equality (with-asserts-only (assert ((compiler-brel comp) b1 b2)))]
              [sol (verify #:assume (assert ccomp) #:guarantee (assert (apply && equality)))])
         (if (unsat? sol)
             '()
             (list (list c1 c2 b1 b2) sol)))]
     ))



; find-exploit: {r:comp} r.source.expression -> (rel-target-context * SAT) + ()
; Solve the following synthesis problem:
; (\lambda v).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax (find-exploit stx)
  (syntax-parse stx
    [(_ comp v)
     #`(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
              [c1 (make-symbolic-var (language-ctx source))]
              [c2 (make-symbolic-var (language-ctx target))]
              [b1 ((language-evaluate source) ((language-link source) c1 v))]
              [b2 ((language-evaluate target) ((language-link target) c2 ((compiler-compile comp) v)))]
              [ccomp ((compiler-crel comp) c1 c2)]
              [equality (with-asserts-only (assert ((compiler-brel comp) b1 b2)))]
              [sol (synthesize #:forall c1 #:assume (assert ccomp) #:guarantee (assert (!(apply && equality))))])
         (if (unsat? sol)
             '()
             (list (list c1 c2 b1 b2) sol)))]
     ))



; find-exploitable-component: comp -> (compiler-source-expression * compiler-target-context * SAT) + ()
; (\lambda r).
;   Exists v:r.s.expression
;     find-exploit r v
(define-syntax (find-exploitable-component stx)
  (syntax-parse stx
    [(_ comp)
     #`(let* ([v (make-symbolic-var (language-exp (compiler-source comp)))]
              [exploit (find-exploit comp v)])           
         (match exploit
           [(list (list c1 c2 b1 b2) sol)
              (list (list v c1 c2 b1 b2) sol)]
           [_ '()]))]))
                   


