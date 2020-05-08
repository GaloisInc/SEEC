#lang rosette/safe
(provide define-lang
         (struct-out lang)
         (struct-out rel-lang))


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


; A language consists of:
; - scope:lit
; - expression: predsyn
; - valid-expression: expression -> bool
; - context: predsyn
; - valid-context: context -> bool
; - behaviors: lit
; - program: lit
; - bounds: hash map from lit -> integer
; - apply (or link): function from context -> expression -> program
; - evaluate: function from program -> behavior
(struct lang (scope expression valid-expression context valid-context behaviors program bounds apply evaluate))

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
    



; A relation between languages consists of:
; source-lang (abr:s): A lang structure standing in as source 
; target-lang (abr:t): "                            as target
; behavior-relation: equivalence class for source-lang and target-lang's behaviors
; context-relation : "'s context
; compile: function from source-expression to target-expression
(struct rel-lang (source-lang target-lang behavior-relation context-relation compile))




(define-syntax-rule (make-symbolic-var lang name)
     #`(#,lang-scope name #,(hash-ref lang-bounds #'name)))




; find-exploit: {r:rel-lang} r.source-lang.expression SAT
; Solve the following synthesis problem:
; (\lambda v).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v), r.t.apply(c2, r.compile(v))))
(define-syntax-rule (find-exploit rel v)
                #`(define c1 (make-symbolic-var #,rel-source-lang #,rel-source-lang-context)
                    (define c2 (make-symbolic-var #,rel-source-lang #,rel-source-lang-context)  
                      (define b1 (#,rel-source-lang-evaluate c1 v)
                        (define b2 (#,rel-target-lang-evaluate c2 (rel-compile v))
                          (define crel (#,rel-context-relation c1 c2)
                            (define equality (assert (#,rel-behavior-relation b1 b2))
                              (define sol (synthesize #:forall c1 #:assume crel #:guarantee (assert (!(apply && equality))))
                                (if (unsat? sol)
                                    (empty)
                                    (define instance (concretize c2 sol)
                                      (list instance sol)))))))))))



; unsafe: rel-lang -> SAT
; (\lambda r).
;   Exists v:r.s.expression
;     find-exploit r v
(define-syntax-rule (find-exploitable-component rel)
                #`(define v (make-symbolic-var #,rel-source-lang #,rel-source-lang-expression)
                  (match (find-exploit #,rel v)
                    [(list c2 sol)
                     (define instance (concretize v sol)
                       (list v c2 sol))]
                    [_ empty])))
                   

