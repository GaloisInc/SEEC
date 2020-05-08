#lang rosette/safe
(provide define-lang
         (struct-out lang)
         (struct-out comp))


#|

 This file provides structures to reason abstractly about weird machines.

  "lang" represents a language in the weird-machine framework.

  "rel-lang" represent a compiler in the weird-machine framework.
    In addition to the source and a target language structures,
    it contains trusted relations over behaviors and contexts and
    and a compilation function
          


TODO: bound updates for lang
TODO: define-rel-lang
TODO: fix find-exploit and unsafe
|#



; A predicated syntactic class is
; - name: lit
; - pred: name -> bool
(struct predsyn (name pred))


#| example
(make-predsyn exp 'interaction (lambda (e) #t))
(make-predsyn set 'list valid-set?)
|#


; A language consists of:
; - scope:lit
; - expression: predsyn
; - eallowed (valid-expression): expression -> bool
; - context: predsyn
; - callowed (valid-context): context -> bool
; - behaviors: lit
; - program: lit
; - bounds: hash map from lit -> integer
; - apply (or link): function from context -> expression -> program
; - evaluate: function from program -> behavior
(struct lang (scope expression eallowed context callowed behaviors program bounds apply evaluate))

(define-syntax define-lang
  (syntax-rules ()
    [(_ name scope exp vexp ctx vctx beh prog apply eval)
     (define bounds (make-hash)
       (define predexp (define-predsyn exp vexp)
         (define predctx (define-predsyn ctx vctx)
           (define name (lang name predexp predctx beh prog bounds apply eval)))))]
       [(_ name scope exp ctx beh prog apply eval)
        (define-lang name scope exp (lambda (e) #t) ctx (lambda (c) #t) beh prog apply eval)]      
       ))
    

#| example:
 (define-lang source 
    'set-api exp set 'list (cons 'list 'interaction) cons abstract-interpret)


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
(struct comp (source target brel crel compile))


#| example:

(define-comp buggy-comp source target equal? equal? id)

Question: this doesn't consider nondet. Could add nondetas part of context, or have it be a part of linking. 
          if as part of con


|#



(define-syntax-rule (make-symbolic-var lang name)
  (let* ([s (generate-temporary)])
    #`(let ([s #,lang-scope name #,(hash-ref lang-bounds #'name)])
      (assert (#,lang-name-pred s))
      s)))




; find-exploit: {r:comp} r.source.expression -> (rel-target-context * SAT) + ()
; Solve the following synthesis problem:
; (\lambda v).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax-rule (find-exploit comp v)
                #`(define c1 (make-symbolic-var #,comp-source #,comp-source-context)
                    (define c2 (make-symbolic-var #,comp-source #,comp-source-context)  
                      (define b1 (#,comp-source-evaluate c1 v)
                        (define b2 (#,comp-target-evaluate c2 (comp-compile v))
                          (define ccomp (#,comp-crel c1 c2)
                            (define equality (assert (#,comp-brel b1 b2))
                              (define sol (synthesize #:forall c1 #:assume ccomp #:guarantee (assert (!(apply && equality))))
                                (if (unsat? sol)
                                    (empty)
                                    (define instance (concretize c2 sol)
                                      (list instance sol)))))))))))



; unsafe: comp -> (comp-source-expression * comp-target-context * SAT) + ()
; (\lambda r).
;   Exists v:r.s.expression
;     find-exploit r v
(define-syntax-rule (find-exploitable-component comp)
                #`(define v (make-symbolic-var #,comp-source #,comp-source-expression)
                  (match (find-exploit #,comp v)
                    [(list c2 sol)
                     (define instance (concretize v sol)
                       (list v c2 sol))]
                    [_ empty])))
                   

