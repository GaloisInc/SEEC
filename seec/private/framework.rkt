#lang rosette/safe

(provide current-default-bound
         define-language
         refine-language
         define-compiler
         (struct-out language)
         (struct-out compiler)
         make-query-changed-behavior
         make-query-changed-component
         make-query-weird-computation
         make-query-weird-component
         (struct-out solution)
         concretize-witness
         ;enumerate-witness
         run-query
         display-changed-behavior
         display-weird-component
         make-query-gadget
         display-gadget
         display-list
         seec-add
         seec-subtract
         link
         evaluate
         link-and-evaluate
         compile

         make-symbolic-var
         )

(require (for-syntax syntax/parse)
         racket/stxparam
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
   2) Create query
      > make-query-X ...
   3) Run the query n times
      > run-query #:count n
   4) Display the concrete witnesses returned by the query
      > display-X


 TODO: change rel to be
  Eq (use the same symbolic var)
  Fn 
TODO, can use solve+ instead of verify for some queries?




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
    [(_ comp v1
        bound-c1
        bound-c2
        found-core)                
     #'(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
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
         (unsafe:generator
          ()
          (let loop ([found (list)])
            (let* (
                   [tmpsol (verify
                                     #:assume (assert (and ccomp
                                                           (not (ormap (lambda (t) (equal? sym-core t)) found))))
                                     #:guarantee (assert (apply && equality)))])
                       (if (unsat? tmpsol)
                           #f
                           (let* ([symbolic-witness (changed-behavior-solution language-witnesses tmpsol)]
                                 
                                  [witness (concretize-witness symbolic-witness)]
                                  [core (found-core witness)]) 
                             (unsafe:yield witness)
                             (loop (cons core found))))))))]))


(define-syntax (run-query stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:count max:expr)
                   #:defaults ([max #'#f]))
         gen)
     #'(unsafe:for/list ([i (unsafe:in-range max)]
                           [t (unsafe:in-producer gen #f)])
                          t)]))


; inner-weird-computation
(define-syntax (inner-weird-computation stx)
  (syntax-parse stx
    [(_ comp v1
        bound-c1
        bound-c2
        found-core)                   
     #`(let* ([source (compiler-source comp)]
              [target (compiler-target comp)]
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
(define (concretize-witness sym-solution)
  (let* ([vars (solution-witness sym-solution)]
        [unpacked-vars (map unpack-language-witness vars)]
        [model (solution-model sym-solution)]
        [list-vars (foldr append (list) unpacked-vars)]
        [concretized (concretize list-vars model)])
      (pack-language-witness concretized)))




; show (c1, v1) ~> b1 and (c2, v2) ~> b2
(define (display-changed-behavior vars out)
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
            (language-witness-context target-vars))))))



; make-query-changed-behavior: {r:comp} r.source.expression -> generator witness
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c1:s.t.context c2:r.t.context,
;    r.ctx-relation(c1, c2)
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
; Returns a generator of concrete witness, each of which will have a different source context
(define-syntax (make-query-changed-behavior stx)
  (syntax-parse stx
    [(_ comp v1
        (~seq
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))))
     #'(inner-changed-behavior comp v1 bound-c1 bound-c2 (lambda (w) (language-witness-context (first w))))]))

; make-query-changed-component: {r:comp} generator witness
; Solve the following synthesis problem:
; (\lambda r).
;   Exists v:r.s.expression
;     make-query-changed-behavior r v
; Returns a generator of concrete witness, each of which will have a different source expression
(define-syntax (make-query-changed-component stx)
  (syntax-parse stx
    [(_ comp
        (~seq
         (~optional
          (~seq #:source-expression-bound bound-v1)
          #:defaults ([bound-v1 #'#f]))
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))))
     #`(let* ([v (make-symbolic-var
                  (language-expression (compiler-source comp) bound-v1))])
         (inner-changed-behavior comp v bound-c1 bound-c2 (lambda (w) (language-witness-expression (first w)))))]))



; make-query-emergent-computation: {r:comp} r.source.expression -> generator witness
; Solve the following synthesis problem:
; (\lambda v1).
; Exists c2:r.t.context,
;   Forall c1:r.s.context,
;     r.context-relation(c1, c2) ->
;       not (r.behavior-relation(r.s.apply(c1, v1), r.t.apply(c2, r.compile(v1))))
; Returns a generator of concrete witness, each of which will have a different target context
(define-syntax (make-query-weird-computation stx)
  (syntax-parse stx
    [(_ comp v1 (~seq
                 (~optional
                  (~seq #:source-context-bound bound-c1)
                  #:defaults ([bound-c1 #'#f]))
                 (~optional
                  (~seq #:target-context-bound bound-c2)
                  #:defaults ([bound-c2 #'#f]))))
     #`(inner-weird-computation comp v1 bound-c1 bound-c2 (lambda (w) (language-witness-context (second w))))]))




; make-query-weird-component: {r:comp} -> generator witness
; (\lambda r).
;   Exists v:r.s.expression
;     make-query-weird-computation r v
; Returns a generator of concrete witness, each of which will have a different source expression
(define-syntax (make-query-weird-component stx)
  (syntax-parse stx
    [(_ comp
        (~seq
         (~optional
          (~seq #:source-expression-bound bound-v1)
          #:defaults ([bound-v1 #'#f]))
         (~optional
          (~seq #:source-context-bound bound-c1)
          #:defaults ([bound-c1 #'#f]))
         (~optional
          (~seq #:target-context-bound bound-c2)
          #:defaults ([bound-c2 #'#f]))))
     #`(let* ([v (make-symbolic-var
                  (language-expression (compiler-source comp) bound-v1))])
         (inner-weird-computation comp v bound-c1 bound-c2 (lambda (w) (language-witness-expression (first w)))))]))


; show v1, c2 and b2
(define (display-weird-component vars out)
  (cond
    [(equal? vars #f) (out (format "No weird components found~n"))]
    [else
     (let* ([source-vars (first vars)]
            [target-vars (second vars)])
       (out (format
             "Expression ~a~n has emergent behavior ~a~n witnessed by target-level context ~a~n"
             (language-witness-expression source-vars)
             (language-witness-behavior target-vars)
             (language-witness-context target-vars))))
       ]))




; Source: format-str, (arg-list x acc), cons, run
; Goal: find a format-str s.t. given a ctx (arg-list, acc), increment the acc. (input is Source, v-ctx:Context -> bool (in addition to the one in source), spec:Context -> behavior -> bool
(define-syntax (make-query-gadget stx)
  (syntax-parse stx
    [(_ lang valid-program specification
        (~seq
         (~optional
          (~seq #:expression-bound bound-v)
          #:defaults ([bound-v #'#f]))
         (~optional
          (~seq #:context-bound bound-c)
          #:defaults ([bound-c #'#f]))))
     #`(let* ([c1 (make-symbolic-var (language-context lang) bound-c)]
              [v1 (make-symbolic-var (language-expression lang) bound-v)]
              [p1 ((language-link lang) c1 v1)]
              [b1 ((language-evaluate lang) p1)]
              ; Creating a second context to return as example
              [c2 (make-symbolic-var (language-context lang) bound-c)]
              [p2 ((language-link lang) c2 v1)]
              [b2 ((language-evaluate lang) p2)])
         (unsafe:generator
          ()
          (let loop ([found (list)])
            (let ([tmpsol (synthesize
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

(define (display-gadget vars out)
  (cond
    [(equal? vars #f) (out (format "Gadget failed to synthesize~n"))]
    [else
     (let* ([lang-vars (first vars)])
       (out (format
          "Expression ~a~n is a gadget for the provided specification, as witnessed by behavior ~a~n in context ~a~n"
          (language-witness-expression lang-vars)
          (language-witness-behavior lang-vars)
          (language-witness-context lang-vars))))
     ]))

(define (display-list list)
  (for-each displayln list)
  (void))

(define (seec-add n1 n2)
  (bonsai-integer (+ (bonsai-integer-value n1)
                     (bonsai-integer-value n2))))

(define (seec-subtract n1 n2)
  (bonsai-integer (- (bonsai-integer-value n1)
                     (bonsai-integer-value n2))))
