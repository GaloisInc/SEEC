#lang rosette/safe

(provide match
         match-let*
         define-match-expander)

(require (for-syntax racket/syntax
                     syntax/parse
                     syntax/id-table
                     (only-in racket/match/stxtime make-struct-type-property/accessor)))

(begin-for-syntax
  (define-values (prop:match-expander match-expander? match-expander-proc) 
    (make-struct-type-property/accessor 'prop:match-expander))

  (define make-match-expander
    (let ()
      (struct match-expander (match-xform macro-xform)
        #:property prop:set!-transformer 
        (λ (me stx)
          (define xf (match-expander-macro-xform me))
          (define proc
            (cond [(rename-transformer? xf)
                   (lambda (x)
                     (define target (rename-transformer-target xf))
                     (syntax-case stx (set!)
                       [(set! id args ...)
                        #`(set! #,target args ...)]
                       [(id args ...)
                        (datum->syntax stx
                                       `(,target ,@(syntax->list #'(args ...)))
                                       stx stx)]
                       [_ (rename-transformer-target xf)]))]
                  [(set!-transformer? xf) (set!-transformer-procedure xf)]
                  [(procedure? xf)
                   (lambda (stx)
                     (syntax-case stx (set!)
                       [(set! . _)
                        (raise-syntax-error #f "cannot mutate syntax identifier" stx)]
                       [_ (xf stx)]))]
                  [else (raise-syntax-error
                         #f
                         "not a procedure for match expander transformer" stx)]))
          (proc stx))
        #:property prop:match-expander (struct-field-index match-xform))
      (values match-expander)))

  (struct match-rule (vars tmps condition body-transformer) #:transparent)
  
  (define (compile-rule tmp stx)
    (syntax-parse stx
      #:literals (list cons)
      #:datum-literals (? ! _)
      [_ (match-rule (set) (set) #'#t (λ (b) b))]
      [var:id
       (with-syntax ([vartmp (quasisyntax/loc #'var #,(gensym (syntax->datum #'var)))])
         (match-rule (set #'var)
                     (set #'vartmp)
                     #`(begin (set! vartmp #,tmp) #t)
                     (λ (body)
                       #`(let-syntax ([var (make-rename-transformer #'vartmp)])
                           #,body))))]
      [(? pred pat)
       (let ([compiled (compile-rule tmp #'pat)])
         (match-rule (match-rule-vars compiled)
                     (match-rule-tmps compiled)
                     #`(and (pred #,tmp) #,(match-rule-condition compiled))
                     (match-rule-body-transformer compiled)))]
      [(! transformer pat)
       (with-syntax ([transformed #'transformed])
         (let ([compiled (compile-rule #'transformed #'pat)])
           (match-rule (match-rule-vars compiled)
                       (match-rule-tmps compiled)
                       #`(let ([transformed (transformer #,tmp)])
                           #,(match-rule-condition compiled))
                       (match-rule-body-transformer compiled))))]
      [(cons pata patb)
       (with-syntax ([elementa #'elementa]
                     [elementb #'elementb])
         (let* ([compileda (compile-rule #'elementa #'pata)]
                [compiledb (compile-rule #'elementb #'patb)]
                [varsa (match-rule-vars compileda)]
                [varsb (match-rule-vars compiledb)]
                [vars     (let ([i (set-intersect varsa varsb)])
                                     (unless (set-empty? i)
                                       (wrong-syntax (set-first i) "duplicate pattern variable"))
                                     (set-union varsa varsb))]
                [tmpsa (match-rule-tmps compileda)]
                [tmpsb (match-rule-tmps compiledb)]
                [tmps  (set-union tmpsa tmpsb)]
                [conditiona (match-rule-condition compileda)]
                [conditionb (match-rule-condition compiledb)])
           (match-rule vars
                       tmps
                       #`(and (pair? #,tmp)
                              (let ([elementa (car #,tmp)])
                                #,conditiona)
                              (let ([elementb (cdr #,tmp)])
                                #,conditionb))
                       (compose (match-rule-body-transformer compileda) (match-rule-body-transformer compiledb)))))]
      [(list pat ...)
       (with-syntax ([element #'element])
         (let* ([compiled (map (λ (p) (compile-rule #'element p)) (syntax->list #'(pat ...)))]
                [vars     (foldl (λ (s1 s2)
                                   (let ([i (set-intersect s1 s2)])
                                     (unless (set-empty? i)
                                       (wrong-syntax (set-first i) "duplicate pattern variable"))
                                     (set-union s1 s2)))
                                 (set)
                                 (map match-rule-vars compiled))]
                [tmps     (foldl set-union (set) (map match-rule-tmps compiled))])
           (match-rule vars
                       tmps
                       #`(and (list? #,tmp)
                              (= (length #,tmp) #,(length compiled))
                              #,@(map (λ (i condition)
                                        #`(let ([element (list-ref #,tmp #,(datum->syntax tmp i))])
                                            #,condition))
                                      (range (length compiled))
                                      (map match-rule-condition compiled)))
                       (foldl compose (λ (b) b) (map match-rule-body-transformer compiled)))))])))

(define-syntax (define-match-expander stx)
  (syntax-parse stx
    [(_ name:id as-expander-proc:expr as-expr-proc:expr)
     #'(define-syntax name
         (make-match-expander as-expander-proc as-expr-proc))]
    [(_ name:id as-expander-proc:expr)
     #'(define-syntax name
         (make-match-expander as-expander-proc
                              (lambda (stx)
                                (raise-syntax-error
                                 #f "this match expander must be used inside match"
                                 stx))))]))

(begin-for-syntax
  (define (rewrite-expander stx)
    (syntax-parse stx
      [(name:id pat ...)
       (if (match-expander? (syntax-local-value #'name (λ () #f)))
           (let* ([new ((match-expander-proc (syntax-local-value #'name)) stx)])
             (rewrite-expander new))
           #`(name #,@(map rewrite-expander (syntax->list #'(pat ...)))))]
      [pat #'pat])))

(define-syntax (match stx)
  (syntax-parse stx
    [(_ val:expr [pat body ...] ...)
     (with-syntax ([(newpat ...) (map rewrite-expander (syntax->list #'(pat ...)))]
                   [(newres ...) (syntax->list #'((begin body ...) ...))])
     #`(match/int val [newpat newres] ...))]))

(define-syntax (match-let* stx)
  (syntax-parse stx
    [(_ ([pat val:expr] ...) body ...+)
     (foldr (lambda (pat val nbody)
              #`(match #,val [#,pat #,nbody]))
            #'(begin body ...)
            (syntax->list #'(pat ...))
            (syntax->list #'(val ...)))]))

(define-syntax (match/int stx)
  (syntax-parse stx
    [(_ val:expr [pat body] ...)
     (with-syntax ([tmp #'tmp])
       (let ([compiled-rules (map (λ (pat) (compile-rule #'tmp pat)) (syntax->list #'(pat ...)))])
         (with-syntax ([(decl ...)  (set->list (foldl set-union (set) (map match-rule-tmps compiled-rules)))]
                       [(check ...) (map match-rule-condition compiled-rules)]
                       [(body ...)  (map (λ (body compiled)
                                           ((match-rule-body-transformer compiled) body))
                                         (syntax->list #'(body ...))
                                         compiled-rules)])
           #`(let ([tmp val])
               (let ([decl #f] ...)
                 (cond
                   [check body]
                   ...
                   [else (assert #f "inexhaustive match")]))))))]))
