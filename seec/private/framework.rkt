#lang rosette/safe

(provide current-default-bound
         define-language
         refine-language
         define-compiler
         (struct-out language)
         (struct-out compiler)
         find-changed-behavior
         find-changed-behavior-inc
         find-changed-component
         find-changed-component-inc
         find-weird-computation
         find-weird-component
         find-gadget
         (struct-out solution)
         unpack-language-witness
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
                              raise-argument-error)
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


 TODO: change rel to be
  Eq (use the same symbolic var)
  Fn 
TODO: Get inc-changed-behavior to work




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



; inner-changed-behavior
(define-syntax (inner-changed-behavior stx)
  (syntax-parse stx
    [(_ comp
        v
        bound-v1
        bound-c1
        bound-c2
        where-vars
        found-core)                
     #'(unsafe:generator
        ()
        (let*
            ([source (compiler-source comp)]
             [target (compiler-target comp)]
             [v1 (if v
                     v
                     (let* ([v* (make-symbolic-var (language-expression source) bound-v1)])
;                       (assert (where-v1 v*))
                       v*))]
               [c1 (make-symbolic-var (language-context source) bound-c1)]                
               [c2 (make-symbolic-var (language-context target) bound-c2)]
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
               [language-witnesses (list (language-witness v1 c1 p1 b1) (language-witness v2 c2 p2 b2))]
               [sym-core (found-core language-witnesses)])
         (let loop ([found (list)])
          (let* 
              ([tmpsol (verify
                        #:assume (assert (and ccomp
                                              (where-vars v1 v2 c1 c2 b1 b2)
                                              (not (ormap (lambda (t) (equal? sym-core t)) found))))
                        #:guarantee (assert (apply && equality)))])
            (if (unsat? tmpsol)
                #f
                (let* ([symbolic-witness (changed-behavior-solution language-witnesses tmpsol)]                    
                       [witness (concretize-witness symbolic-witness)]
                       [core (found-core witness)])
                  (unsafe:yield witness)
                  (loop (cons core found))))))))]))

; incremental version of inner-changed-behavior + run-query
(define-syntax (inc-changed-behavior stx)
  (syntax-parse stx
    [(_ comp
        v
        bound-v1
        where-v1
        bound-c1
        where-c1
        bound-c2
        where-c2
        found-core)                
     #'(lambda (num-sol)
         (let*
             ([assert-store (asserts)] ; save assertions on entry
              [source (compiler-source comp)]
              [target (compiler-target comp)]
              [v1 (if v
                      v
                      (let* ([v* (make-symbolic-var (language-expression source) bound-v1)])
                        (assert (where-v1 v*))
                        v*))]
              [c1 (make-symbolic-var (language-context source) bound-c1)]                
              [c2 (make-symbolic-var (language-context target) bound-c2)]
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
              [behavior-relation (compiler-behavior-relation comp)]
              [equality (with-asserts-only (assert (behavior-relation b1 b2)))]
              [language-witnesses (list (language-witness v1 c1 p1 b1) (language-witness v2 c2 p2 b2))]
              [sym-core (found-core language-witnesses)])
           (assert (and ; ccomp
                    (if context-relation
                        (context-relation c1 c2)
                        #t)
                    (where-c1 v1 c1)
                    (where-c2 v1 c2)))
           (assert (apply || (map ! equality))) ; inequality of behavior
           (let ([inc (solve+)])
             (let loop ([witnesses (list)]
                        [cur-num num-sol]
                        [last-found #t])
               (if (equal? cur-num 0)
                   (begin 
                     ; Shutdown the solver, restore assertion state to pre-query and return the list of witnesses
                     (inc 'shutdown)
                     (clear-asserts!)
                     (for-each (lambda (arg) (assert arg)) assert-store)
                     witnesses)                 
                   (let* 
                       ([tmpsol (inc (not (equal? sym-core last-found)))])
                     (if (unsat? tmpsol)
                           (loop witnesses 0) ; shortcut to end of loop)                           
                         (let* ([symbolic-witness (changed-behavior-solution language-witnesses tmpsol)]                    
                                [witness (concretize-witness symbolic-witness)]
                                [core (found-core witness)])
                           (loop (cons witness witnesses) (- cur-num 1) core)))))))))]))


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



; inner-weird-computation
(define-syntax (inner-weird-computation stx)
  (syntax-parse stx
    [(_ comp
        v
        bound-v1
        bound-c1
        bound-c2
        where-vars
        found-core)
     #`(let*
           ([source (compiler-source comp)]
            [target (compiler-target comp)]
            [v1 (if v
                    v
                    (let* ([v* (make-symbolic-var (language-expression source) bound-v1)])
                      v*))]
            [c1 (make-symbolic-var (language-context source) bound-c1)]
            [c2 (make-symbolic-var (language-context target) bound-c2)]
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
           (let* ([equality (with-asserts-only (assert (behavior-relation b1 b2)))]
                  [language-witnesses (list (language-witness v1 c1 p1 b1) (language-witness v2 c2 p2 b2))]
                  [sym-core (found-core language-witnesses)])
             (unsafe:generator
              ()
              (let loop ([found (list)])
                (let ([tmpsol (synthesize
                               #:forall (cons c1 (cons nondet1 nondet2)) ; quantify over nondet
                               #:assume (assert (and ccomp
                                                     (where-vars v1 v2 c1 c2 b1 b2)
                                                     (not (ormap (lambda (t) (equal? sym-core t)) found))))
                               #:guarantee (assert (! (apply && equality))))])
                  (if (unsat? tmpsol)
                      #f
                      (let* ([symbolic-witness (weird-component-solution language-witnesses tmpsol)]                             
                             [witness (concretize-witness symbolic-witness)]
                             ; Projecting c2 out of the concrete witness
                             [core (found-core witness)])                        
                        (unsafe:yield witness)
                        (loop (cons core found))))))))))]))


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


; Find changed behavior: {r:comp} r.source.expression -> concrete witness 
; 1) Create a generator for changed behavior
; 2) Run generator n times (if count argument is provided, in which case a list of witness is provided)
; 3) Restore assertion state to pre-query
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c1:s.t.context c2:r.t.context,
;    r.ctx-relation(c1, c2)
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
; Returns a list of concrete witness, each of which will have a different source context
(define-syntax (find-changed-behavior stx)
  (syntax-parse stx
    [(_ comp v1
        (~seq
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:source-context-where where-c1)
          #:defaults ([where-c1 #'(lambda (v1 c1) #t)]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))
         (~optional
          (~seq #:target-context-where where-c2)
          #:defaults ([where-c2 #'(lambda (v1 c2) #t)])))
        (~optional
         (~seq #:source-behavior-where where-b1)
         #:defaults ([where-b1 #'(lambda (v1 c1 c2 b1) #t)]))
        (~optional
         (~seq #:target-behavior-where where-b2)
         #:defaults ([where-b2 #'(lambda (v1 c1 c2 b2) #t)]))
        (~optional
         (~seq #:count witness-count)
         #:defaults ([witness-count #'#f])))
     #'(let*
           ([assert-store (asserts)] ; save assertions on entry
            [where-vars (lambda (v1 v2 c1 c2 b1 b2) (and (where-c1 v1 c1)
                                                         (where-c2 v1 c2)
                                                         (where-b1 v1 c1 c2 b1)
                                                         (where-b2 v1 c1 c2 b2)))]
            [gen (inner-changed-behavior comp v1 #f #f bound-c1 bound-c2 where-vars (lambda (w) (language-witness-context (first w))))]
            [witness (run-query #:count witness-count gen)])
         (clear-asserts!)
         (for-each (lambda (arg) (assert arg)) assert-store) ; restore entry assertions
         witness)]))

(define-syntax (find-changed-behavior-inc stx)
  (syntax-parse stx
    [(_ comp v1
        (~seq
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:source-context-where where-c1)
          #:defaults ([where-c1 #'(lambda (v1 c1) #t)]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))
         (~optional
          (~seq #:target-context-where where-c2)
          #:defaults ([where-c2 #'(lambda (v1 c2) #t)])))
        (~optional
         (~seq #:source-behavior-where where-b1)
         #:defaults ([where-b1 #'(lambda (v1 c1 c2 b1) #t)]))
        (~optional
         (~seq #:target-behavior-where where-b2)
         #:defaults ([where-b2 #'(lambda (v1 c1 c2 b2) #t)]))
         (~optional
          (~seq #:count witness-count)
          #:defaults ([witness-count #'1])))        
     #'((inc-changed-behavior comp v1 #f #f bound-c1 where-c1 bound-c2 where-c2 where-b1 where-b2 (lambda (w) (language-witness-context (first w)))) witness-count)]))


                
; find-changed-component: {r:comp} concrete witness
; Returns a list of witness if #:count is used
; Solve the following synthesis problem:
; (\lambda r).
;   Exists v:r.s.expression
;     find-changed-behavior r v
; Returns a list of concrete witness, each of which will have a different source expression
(define-syntax (find-changed-component stx)
  (syntax-parse stx
    [(_ comp
        (~seq
         (~optional
          (~seq #:source-expression-bound bound-v1)
          #:defaults ([bound-v1 #'#f]))
         (~optional
          (~seq #:source-expression-where where-v1)
          #:defaults ([where-v1 #'(lambda (v1) #t)]))
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:source-context-where where-c1)
          #:defaults ([where-c1 #'(lambda (v1 c1) #t)]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))
         (~optional
          (~seq #:target-context-where where-c2)
          #:defaults ([where-c2 #'(lambda (v1 c2) #t)]))
         (~optional
          (~seq #:source-behavior-where where-b1)
          #:defaults ([where-b1 #'(lambda (v1 c1 c2 b1) #t)]))
         (~optional
          (~seq #:target-behavior-where where-b2)
          #:defaults ([where-b2 #'(lambda (v1 c1 c2 b2) #t)]))
         (~optional
          (~seq #:count witness-count)
          #:defaults ([witness-count #'#f]))))
     #`(let*
           ([assert-store (asserts)] ; save assertions on entry
            [where-vars (lambda (v1 v2 c1 c2 b1 b2) (and (where-v1 v1)
                                                         (where-c1 v1 c1)                                                         
                                                         (where-c2 v1 c2)
                                                         (where-b1 v1 c1 c2 b1)
                                                         (where-b2 v1 c1 c2 b2)))]
            [gen (inner-changed-behavior comp #f bound-v1 bound-c1 bound-c2 where-vars (lambda (w) (language-witness-expression (first w))))]
            [witness (run-query #:count witness-count gen)])
         (clear-asserts!)
         (for-each (lambda (arg) (assert arg)) assert-store) ; restore assertion state to what it was on entry
         witness)]))

(define-syntax (find-changed-component-inc stx)
  (syntax-parse stx
    [(_ comp
        (~seq
         (~optional
          (~seq #:source-expression-bound bound-v1)
          #:defaults ([bound-v1 #'#f]))
         (~optional
          (~seq #:source-expression-where where-v1)
          #:defaults ([where-v1 #'(lambda (v1) #t)]))
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:source-context-where where-c1)
          #:defaults ([where-c1 #'(lambda (v1 c1) #t)]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))
         (~optional
          (~seq #:target-context-where where-c2)
          #:defaults ([where-c2 #'(lambda (v1 c2) #t)]))
         (~optional
          (~seq #:count witness-count)
          #:defaults ([witness-count #'1]))))
     #`(let ([query (inc-changed-behavior comp #f bound-v1 where-v1 bound-c1 where-c1 bound-c2 where-c2 (lambda (w) (language-witness-expression (first w))))])
         (query witness-count))]))



; find-weird-computation: {r:comp} r.source.expression -> list witness
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
; Returns a list of concrete witness, each of which will have a different target context
(define-syntax (find-weird-computation stx)
  (syntax-parse stx
    [(_ comp v1 (~seq
                 (~optional
                  (~seq #:source-context-bound bound-c1)
                  #:defaults ([bound-c1 #'#f]))
                 (~optional
                  (~seq #:source-context-where where-c1)
                  #:defaults ([where-c1 #'(lambda (v1 c1) #t)]))
                 (~optional
                  (~seq #:target-context-bound bound-c2)
                  #:defaults ([bound-c2 #'#f]))
                 (~optional
                  (~seq #:target-context-where where-c2)
                  #:defaults ([where-c2 #'(lambda (v1 c2) #t)]))
                 (~optional
                  (~seq #:source-behavior-where where-b1)
                  #:defaults ([where-b1 #'(lambda (v1 c1 c2 b1) #t)]))
                 (~optional
                  (~seq #:target-behavior-where where-b2)
                  #:defaults ([where-b2 #'(lambda (v1 c1 c2 b2) #t)]))                          
                 (~optional
                  (~seq #:count witness-count)
                  #:defaults ([witness-count #'#f]))))
     #`(let*
           ([assert-store (asserts)] ; save assertions on entry
            [where-vars (lambda (v1 v2 c1 c2 b1 b2) (and (where-v1 v1)
                                                         (where-c1 v1 c1)                                                         
                                                         (where-c2 v1 c2)
                                                         (where-b1 v1 c1 c2 b1)
                                                         (where-b2 v1 c1 c2 b2)))]
            [gen (inner-weird-computation comp v1 #f #f bound-c1 bound-c2 where-vars (lambda (w) (language-witness-context (second w))))]
            [witness (run-query #:count witness-count gen)])
         (clear-asserts!)
         (for-each (lambda (arg) (assert arg)) assert-store) ; restore entry assertions
         witness)]))



; find-weird-component: {r:comp} -> list witness
; (\lambda r).
;   Exists v:r.s.expression
;     find-weird-computation r v
; Returns a list of concrete witness, each of which will have a different source expression
(define-syntax (find-weird-component stx)
  (syntax-parse stx
    [(_ comp
        (~seq
         (~optional
          (~seq #:source-expression-bound bound-v1)
          #:defaults ([bound-v1 #'#f]))
         (~optional
          (~seq #:source-expression-where where-v1)
          #:defaults ([where-v1 #'(lambda (v1) #t)]))
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:source-context-where where-c1)
          #:defaults ([where-c1 #'(lambda (v1 c1) #t)]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))
         (~optional
          (~seq #:target-context-where where-c2)
          #:defaults ([where-c2 #'(lambda (v1 c2) #t)]))
         (~optional
          (~seq #:source-behavior-where where-b1)
          #:defaults ([where-b1 #'(lambda (v1 c1 c2 b1) #t)]))
         (~optional
          (~seq #:target-behavior-where where-b2)
          #:defaults ([where-b2 #'(lambda (v1 c1 c2 b2) #t)]))
         (~optional
          (~seq #:count witness-count)
          #:defaults ([witness-count #'#f]))))
          #`(let*
                ([assert-store (asserts)] ; save assertions on entry
                 [where-vars (lambda (v1 v2 c1 c2 b1 b2) (and (where-v1 v1)
                                                              (where-c1 v1 c1)                                                         
                                                              (where-c2 v1 c2)
                                                              (where-b1 v1 c1 c2 b1)
                                                              (where-b2 v1 c1 c2 b2)))]
                 [gen (inner-weird-computation comp #f bound-v1 bound-c1 bound-c2 where-vars (lambda (w) (language-witness-expression (first w))))]
                 [witness (run-query #:count witness-count gen)])
         (clear-asserts!)
         (for-each (lambda (arg) (assert arg)) assert-store) ; restore entry assertion state
         witness)]))


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
         ; creating second context to return as example if the first is symbolic
         [ctx-witness (if fresh
                          (make-symbolic-var (language-context lang) bound-c)
                          ctx
                          )]
         [p-witness ((language-link lang) ctx-witness e)]
         [b-witness ((language-evaluate lang) p-witness)] ; NOTE: don't do this
                                                          ; evaluation here; do
                                                          ; it after it's
                                                          ; concretized
         )
      (letrec ([loop (λ (num witness-list)
                       (if (<= num 0)
                           witness-list
                           (let* ([sol (synthesize
                                        #:forall (cons vars vars-extra)
                                        #:assume (assert (and (valid-program p)
                                                              (valid-program p-witness)
                                                              (ctx-constraint ctx)
                                                              (ctx-constraint ctx-witness)
                                                              (e-constraint e)
                                                              (not (expr-in-witness-list? e witness-list))
                                                              ))
                                        #:guarantee (assert (if debug
                                                                (not (spec p b))
                                                                (spec p b))))
                                       ])
                             (if (unsat? sol)
                                 #f
                                 (let* ([symbolic-witness
                                         (solution
                                          (list (language-witness e ctx-witness p-witness b-witness))
                                          sol)]
                                        [witness (concretize-witness symbolic-witness)]
                                        )
                                   (loop (- num 1)
                                         (append witness witness-list))))
                             )))])
        (define result (loop count (list )))
        (clear-asserts!)
        result
        ))))


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
