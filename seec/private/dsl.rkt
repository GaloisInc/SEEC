#lang rosette/safe
(provide define-Lang
         define-Comp
         (struct-out Lang)
         (struct-out Comp))


#|

 This file provides structures to reason abstractly about weird machines.

  "lang" represents a language in the weird-machine framework.

  "comp" represent a compiler in the weird-machine framework.
    In addition to the source and a target language structures,
    it contains trusted relations over behaviors and contexts and
    and a compilation function
          


TODO: fix find-exploit and unsafe
TODO: deal with nondet
|#



; Predicated syntactic class
; For the moment, we decouple pred (symbolic restrictions) from gen (syntactic generation)
(struct Predsyn (gen; () -> bonsai-tree 
                 pred ; name -> bool - nothing
                 ))


(define-syntax define-Predsyn
  (syntax-rules ()
    [(_ grammar pat pred)
        #`(predsyn (lambda (x)
                       (#,grammar #,pat bound)) pred)
     ]))

(define (make-symbolic-var ps)
  (let ([s (Predsyn-gen ps)])
    (assert ((Predsyn-pred ps) s))
    s))




#| example
(make-predsyn exp 'interaction (lambda (e) #t))
(make-predsyn set 'list valid-set?)
|#


; A language 
(struct Lang (exp ; predsyn
              ctx    ; predsyn
              ;behavior   ; nothing
              ;program    ; nothing
              link       ; context -> expression -> program
              evaluate)) ; program -> behavior

(define-syntax define-Lang
  (syntax-rules ()
    [(_ name grammar exp vexp bexp ctx vctx bctx link eval)
     (let* ([predexp empty] ;(define-Predsyn grammar exp vexp bexp)]
            [predctx empty] ; (define-Predsyn grammar ctx vctx bctx)]
           #`(define name (lang #,predexp #,predctx link eval))))]
    [(_ name grammar exp bexp ctx bctx  link eval)
     (define-Lang name grammar (lambda (e) #t) bexp ctx (lambda (c) #t) bctx link eval)]      
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
(struct Comp (source target brel crel compile))

(define-syntax define-Comp
  (syntax-rules ()
    [(_ name source target brel crel compile)
     #`(define name (comp source target brel crel compile))]
    ))

#| example:

(define-comp buggy-comp source target equal? equal? id)

Question: this doesn't consider nondet. Could add nondetas part of context, or have it be a part of linking. 
          if as part of con


|#






; find-exploit: {r:comp} r.source.expression -> (rel-target-context * SAT) + ()
; Solve the following synthesis problem:
; (\lambda v).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax-rule (find-exploit comp v)
                #`(let* ([c1 (make-symbolic-var #,(Lang-ctx (Comp-source comp)))]
                         [c2 (make-symbolic-var #,(Lang-ctx (Comp-target comp)))]
                         [b1 (#,(Lang-eval (Comp-source comp)) c1 v)]
                         [b2 (#,(Lang-eval (Comp-target comp)) c2 (#,(Comp-compile comp) v))]
                         [ccomp (#,(Comp-crel comp) c1 c2)]
                         [equality (assert (#,(Comp-brel comp) b1 b2))]
                         [sol (synthesize #:forall c1 #:assume ccomp #:guarantee (assert (!(apply && equality))))])
                    (if (unsat? sol)
                        (empty)
                        (define instance (concretize c2 sol)
                          (list instance sol)))))



; unsafe: comp -> (comp-source-expression * comp-target-context * SAT) + ()
; (\lambda r).
;   Exists v:r.s.expression
;     find-exploit r v
(define-syntax-rule (find-exploitable-component comp)
  #`(let* ([v (make-symbolic-var #,(Lang-exp (Comp-source comp)))]
           [exploit (find-exploit #,comp v)])           
      (match exploit
        [(list c2 sol)
         (define instance (concretize v sol)
           (list v c2 sol))]
        [_ empty])))
                   


