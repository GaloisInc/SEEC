#lang rosette/safe

(provide define-grammar
         syntax-match?
         enumerate
         make-generator)

(require "bonsai3.rkt"
         "match.rkt"
         "solver-aided.rkt"
         (only-in "string.rkt"
                  char
                  string
                  char?
                  string?
                  ))
(require (only-in racket/base
                  [string? racket/string?]
                  [char? racket/char?]
                  raise-argument-error
                  parameterize
                  ))


(require (for-syntax syntax/parse)
         (for-syntax (only-in racket/syntax
                              format-id
                              ))
         (prefix-in unsafe:
                    (combine-in
                     (only-in racket
                              raise-arguments-error
                              for
                              for/fold
                              for/hash
                              for/list
                              in-list
                              in-set
                              list->set
                              set->list
                              set
                              set-add
                              set-union
                              set-subtract
                              set-intersect
                              set-empty?
                              hash
                              make-immutable-hash
                              hash-set
                              hash->list
                              values
                              string-append
                              symbol?
                              symbol->string
                              string->symbol
                              sequence->stream
                              in-range
                              in-producer)
                     racket/match
                     racket/generator
                     (only-in racket/string
                              string-prefix?
                              string-suffix?
                              string-trim))))


(struct grammar (nonterminals
                  terminals
                  productions
                  max-width))
(begin-for-syntax

  ; A grammar+ structure is a syntax-level representation of grammar terminals
  ; and nonterminals, used for extending a parent grammar to a child grammar.
  ; Without this structure, the parent grammar data would not be available at
  ; macro expansion time.
  ;
  ; The struct will be used as follows:
  ;
  ;   (define-syntax lang (grammar+ match-expander terminalstx nonterminalstx))
  ;
  ; where `match-expander` is the (temporary) name of the relevant match
  ; expander, which gets exposed via `lang`; in other words, users will be able
  ; to write:
  ;
  ;   (lang 3)
  ;
  ; or
  ;
  ;  (match (lang 3) [(lang n:integer) n])
  (struct grammar+ (id
                    terminals
                    nonterminals)
    #:property prop:set!-transformer
    (λ (me stx)
      (with-syntax ([target (grammar+-id me)])
        (syntax-parse stx #:literals (set!)
          [(set! id args ...)
           #'(set! target args ...)]
          [(id args ...)
           #'(target args ...)]
          [_ #'target])))
    #:property prop:match-expander
    (λ (stx)
      (syntax-parse stx
        [(id args ...)
         (let ([match-expander (grammar+-id (syntax-local-value #'id))])
           #`(#,match-expander args ...))]))
    )

  ; Access terminal and nonterminal data at macro expansion time
  (define (get-nonterminal-stx stx)
    (grammar+-nonterminals (syntax-local-value stx)))
  (define (get-terminal-stx stx)
    (grammar+-terminals (syntax-local-value stx)))
  )


(define (max-width ls)
  (cond
    [(list? ls)
     (apply max (length ls) (map max-width ls))]
    [(symbol-is-polymorphic-type? "list" ls)
     2]
    [else
     1]
    ))

(begin-for-syntax
  (define builtin-nonterminals '(integer natural boolean bitvector char string any))
  (define builtin-nonterminal-functions '(list))
  (define-literal-set builtin-terminals #:datum-literals (nil cons bv) ())
  (define builtins (append builtin-nonterminals builtin-nonterminal-functions))
)
(define builtin-nonterminals '(integer natural boolean bitvector char string any))
(define builtin-nonterminal-functions '(list))
(define builtin-terminals '(nil cons bv))
(define builtin-keywords (append builtin-nonterminal-functions builtin-terminals))


; OSTODO: properly populate the grammar for polymorphic types
(define make-grammar
  (λ (rules
      #:parent [parent #f]
      )
  (define-values (nonterminals metavars productions prod-max-width)
    (unsafe:for/fold ([nonterminals (if parent
                                        (unsafe:list->set (grammar-nonterminals parent))
                                        (unsafe:set))]
                      [metavars     (if parent
                                        (unsafe:set-union
                                          (unsafe:list->set builtin-nonterminals)
                                          (unsafe:list->set (grammar-terminals parent))
                                          (unsafe:list->set (grammar-nonterminals parent)))
                                        (unsafe:list->set builtin-nonterminals))]

                      [productions  (if parent
                                        (unsafe:make-immutable-hash (grammar-productions parent))
                                        (unsafe:hash))]
                      [prod-width   (if parent
                                        (grammar-max-width parent)
                                        0)])
                     ([production (unsafe:in-list rules)])
                     (let* ([nt             (first production)]
                            [new-nts        (unsafe:set-add nonterminals nt)]
                            [new-meta       (unsafe:set-union metavars
                                                              (unsafe:list->set (flatten production)))]
                            [new-prods      (unsafe:hash-set productions nt (rest production))]
                            [new-prod-width (apply max prod-width (map max-width (rest production)))])
                       (unsafe:values new-nts new-meta new-prods new-prod-width))))

  (let* ([terminals (unsafe:set-subtract metavars nonterminals)]
         )
       (unsafe:for ([mv (unsafe:in-set metavars)])
                   (register-enum mv))
       (grammar (unsafe:set->list nonterminals)
                (unsafe:set->list terminals)
                (unsafe:hash->list productions)
                prod-max-width)
       )
  ))



(define (symbol-is-polymorphic-type? t symb)
  (and (unsafe:symbol? symb)
       (let ([str (unsafe:symbol->string symb)])
         (and
          (unsafe:string-prefix? str (unsafe:string-append t "<"))
          (unsafe:string-suffix? str ">")
          ))))

  ; if stx is of the form t<a>, returns a syntax element a
  ; expects (syntax-is-polymorphic-type? t stx)
(define (extract-polymorphic-type-symbol t symb)
  (let* ([str (unsafe:symbol->string symb)]
         [a (unsafe:string-trim
             (unsafe:string-trim str (unsafe:string-append t "<")
                                 #:right? #f #:repeat? #f)
             ">" #:left? #f #:repeat? #f)]
         )
    (unsafe:string->symbol a)))


; return #t if if `pattern` is a type compatible with the grammar `lang` and
; `tree` is a data structure of that type.
(define (syntax-match? lang pattern tree)
    (for/all [(tree tree)]
      (cond
        ; tree patterns
        [(equal? 'nil pattern)
         (seec-empty? tree)]
        [(and (list? pattern)
              (= (length pattern) 3)
              (equal? (first pattern) 'cons))
         (seec-cons-match?
          (curry syntax-match? lang (second pattern))
          (curry syntax-match? lang (third pattern))
          tree)]

        ; test if pattern is a tuple of patterns
        [(list? pattern)
         (let ([pattern-length (length pattern)])
           (and (bonsai-list? tree)
                (andmap-indexed
                 (λ (i tree-i)
                   (cond
                     [(< i pattern-length) (syntax-match? lang (list-ref pattern i) tree-i)]
                     [else (bonsai-null? tree-i)]))
                 (bonsai-list-nodes tree))))]

        [(equal? 'any pattern)
         (bonsai? tree)]
        [(equal? 'integer pattern)
         (integer? tree)]
        [(equal? 'natural pattern)
         (and (integer? tree)
              (>= tree 0))]
        [(equal? 'char pattern)
         (char? tree)]
        [(equal? 'string pattern)
         (string? tree)]
        [(equal? 'boolean pattern)
         (boolean? tree)]
        [(equal? 'bitvector pattern)
         (bv? tree)]
        [(symbol-is-polymorphic-type? "list" pattern)
         (let* ([a (extract-polymorphic-type-symbol "list" pattern)])
           (seec-list-match? (curry syntax-match? lang) a tree))]
        [(member pattern (grammar-nonterminals lang))
         (let ([productions (cdr (assoc pattern (grammar-productions lang)))])
           (ormap (λ (pat) (syntax-match? lang pat tree)) productions))]
        [(member pattern (grammar-terminals lang))
         (and (bonsai-terminal? tree)
              (equal? (symbol->enum pattern) (bonsai-terminal-value tree)))]
        [else #f])))

(begin-for-syntax
  (define (syntax->string stx)
    (symbol->string (syntax->datum stx)))
  (define (string->syntax stx str)
    (datum->syntax stx (string->symbol str)))

  (define (syntax-has-colon? stx)
    (string-contains? (syntax->string stx) ":"))
  (define (before-colon stx)
    (string->syntax stx (first (string-split (syntax->string stx) ":"))))
  (define (after-colon stx)
    (string->syntax stx (second (string-split (syntax->string stx) ":"))))

  ; Here, t is a string
  ; Return true if stx has the form t<a> for some syntax a
  (define (polymorphic-type? t str)
      (and
       (string-prefix? str (string-append t "<"))
       (string-suffix? str ">")
       ))

  (define (syntax-is-polymorphic-type? t stx)
    (let ([str (syntax->string stx)])
      (polymorphic-type? t str)))

  ; if stx is of the form t<a>, returns a syntax element a
  ; expects (syntax-is-polymorphic-type? t stx)
  (define (extract-polymorphic-type t str)
    (string-trim (string-trim str (string-append t "<")
                              #:right? #f #:repeat? #f)
                 ">" #:left? #f #:repeat? #f))


  (define (syntax-extract-polymorphic-type t stx)
    (let* ([str (syntax->string stx)])
      (string->syntax stx (extract-polymorphic-type t str))))

  (define (syntax-is-any? stx)
    #;(printf "is this any? ~a~n" stx)
    (and (syntax? stx) (equal? (syntax->datum stx) 'any)))

  ; SEEC types have the following form:
  ; typ ::= terminal | list<typ>
  ; returns true if pat has that form.
  ;
  ; Here, `pat` is a syntax object
  (define (is-type? terminals pat)
      (cond
        [(syntax-is-polymorphic-type? "list" pat)
         (is-type? terminals (syntax-extract-polymorphic-type "list" pat))]
        [(syntax-is-any? pat) #t]
        [(syntax? pat) (set-member? terminals (syntax->datum pat))]
        [else #f]
        ))

  ; Terms in the grammar `lang-name` with terminals drawn from the set
  ; `terminals`.
  (define-syntax-class (term lang-name terminals)
    #:attributes (match-pattern stx-pattern depth)
    #:literal-sets (builtin-terminals)
    #:description (format "~a pattern ~a" lang-name terminals)
    #:opaque
    (pattern n:id ; (lang-name X) for X a type
             #:when (and (syntax? #'n)
                         (not (syntax-has-colon? #'n))
                         (is-type? terminals #'n)
                         #;(set-member? terminals (syntax->datum #'n))
                         )
             #:attr match-pattern #'_
             #:attr stx-pattern   #'n
             #:attr depth         #'1)
    (pattern n:id ; (lang-name n:X) for X a type
             #:when (and (syntax? #'n)
                         (syntax-has-colon? #'n)
                         (is-type? terminals (after-colon #'n))
                         #;(set-member? terminals (syntax->datum (after-colon #'n)))
                         )
             #:attr match-pattern (before-colon #'n)
             #:attr stx-pattern   (after-colon #'n)
             #:attr depth         #'1)
    (pattern n:integer
             #:when (and (set-member? terminals 'natural) (>= (syntax->datum #'n) 0))
             #:attr match-pattern #'(? (λ (v) (equal? n v)) _)
             #:attr stx-pattern   #'integer
             #:attr depth         #'1)
    (pattern n:integer
             #:when (set-member? terminals 'integer)
             #:attr match-pattern #'(? (λ (v) (equal? n v)) _)
             #:attr stx-pattern   #'integer
             #:attr depth         #'1)
    (pattern c:char
             #:when (set-member? terminals 'char)
             #:attr match-pattern #'(? (λ (v) (equal? (char c) v)) _)
             #:attr stx-pattern   #'char
             #:attr depth         #'1)
    (pattern s:string
             #:when (set-member? terminals 'string)
             #:attr match-pattern #'(? (λ (v) (equal? (string s) v)) _)
             #:attr stx-pattern   #'string
             #:attr depth         #'1)
    (pattern b:boolean
             #:when (set-member? terminals 'boolean)
             #:attr match-pattern #'(? (λ (v) (equal? b v)) _)
             #:attr stx-pattern   #'boolean
             #:attr depth         #'1)

    (pattern (bv b)
             #:declare b integer
             #:when (set-member? terminals 'bitvector)
             #:attr match-pattern #'(? (λ (v) (equal? b v)) _)
             #:attr stx-pattern   #'bitvector
             #:attr depth         #'1)
    (pattern nil
;             #:when (set-member? terminals 'list)
             #:attr match-pattern #'bonsai-null
             #:attr stx-pattern   #'nil
             #:attr depth         #'0)
    (pattern (cons p-first p-rest)
             #:declare p-first    (term lang-name terminals)
             #:declare p-rest     (term lang-name terminals)
             #:attr match-pattern #'(bonsai-list p-first.match-pattern p-rest.match-pattern)
             #:attr stx-pattern   #'(cons p-first.stx-pattern p-rest.stx-pattern)
             #:attr depth         (datum->syntax
                                   #'((~datum 'cons) p-first p-rest)
                                   (add1 (max (syntax->datum #'p-first.depth)
                                              (syntax->datum #'p-rest.depth)))))
    (pattern (p ...)
             #:declare p (term lang-name terminals)
             #:attr match-pattern #'(bonsai-list p.match-pattern ...)
             #:attr stx-pattern   #'(p.stx-pattern ...)
             #:attr depth         (datum->syntax
                                   #'(p ...)
                                   (add1 (apply max (syntax->datum #'(p.depth ...)))))))


  (define-syntax-class (concrete-term lang-name terminals builtins)
    #:literals (unquote)
    #:literal-sets (builtin-terminals)
    #:description (format "concrete ~a pattern ~a" lang-name terminals)
    #:opaque
    (pattern n:id
             #:when (and (not (syntax-has-colon? #'n))
                         #;(is-type? terminals #'n)
                         (set-member? terminals (syntax->datum #'n))
                         ))
    (pattern n:integer
             #:when (and (set-member? builtins 'natural) (>= (syntax->datum #'n) 0)))
    (pattern n:integer
             #:when (set-member? builtins 'integer))
    (pattern c:char
             #:when (set-member? builtins 'char))
    (pattern s:string
             #:when (set-member? builtins 'string))
    (pattern b:boolean
             #:when (set-member? builtins 'boolean))
    (pattern (bv b:integer)
             #:when (set-member? builtins 'bitvector)
             )
    (pattern (unquote expr))
    (pattern nil
             #:when (set-member? builtins 'list)
             )
    (pattern (cons p-first p-rest)
             #:declare p-first (concrete-term lang-name terminals builtins)
             #:declare p-rest (concrete-term lang-name terminals builtins)
             #:when (set-member? builtins 'list)
             )
    (pattern (p ...)
             #:declare p (concrete-term lang-name terminals builtins)))

  (define (sytnax-set stx)
    (set (syntax->datum stx)))

  #;(define (syntax-set stx)
    (datum->syntax #f (apply set (syntax->list stx)))
    #;(cond
      [(equal? stx #f) (set)]
      ;[else (apply set (syntax->list stx))]
      [else (set)]
      )
    )
  #;(define (syntax-set-union stx)
    (datum->syntax #f (apply set-union (syntax->datum stx) ...)))

  ; QUESTION: does this syntax class need more structure than just to say it is
  ; not in this set of builtin-nonterminals? What about other terminal vaalues?
  (define-syntax-class nonterminal
    #:description "nonterminal"
    #:opaque
    (pattern nt:id
             #:when (not (member (syntax->datum #'nt) builtin-nonterminals))))

  (define-syntax-class builtin
    #:description "built-in nonterminal"
    #:opaque
    (pattern nt:id
             #:when (member (syntax->datum #'nt) builtin-nonterminals)))

  (define-syntax-class type
    #:attributes (type-terminals)
    #:datum-literals ,builtins
    (pattern x:id
             #:when (and (syntax-is-polymorphic-type? "list" #'x)
                         (syntax-parse (syntax-extract-polymorphic-type "list" #'x)
                           [t:type #t]
                           [_ #f]))
             #:attr type-terminals (set-union
                                    (set 'list)
                                    (syntax-parse (syntax-extract-polymorphic-type "list" #'x)
                                      [t:type (attribute t.type-terminals)]))
             )
    (pattern nt:nonterminal
             #:attr type-terminals (set (syntax->datum #'nt)))
    (pattern nt:builtin
             #:attr type-terminals (set (syntax->datum #'nt)))
    )


  (define-syntax-class production
    #:description "production"
    #:attributes (terminals)
    #:opaque
    (pattern ty:type
             #:attr terminals (attribute ty.type-terminals)
             )
    (pattern (p:production ...)
             #:attr terminals (apply set-union (attribute p.terminals)))
    )





  ; INPUT: syntax of productions
  ; OUTPUT: a set of the terminals that occur in the productions
  (define (prods->terminals prods)
    (syntax-parse prods
      [p:production (attribute p.terminals)]
      )
    )
  )


; Define type classifiers of the form lang-nt?
(define-syntax-rule (check-nonterminal lang nt0 expr)
  (match expr
    [(lang nt0) #t]
    [_ #f]
    ))
(define-syntax (define-nonterminal-predicate stx)
  (syntax-case stx ()
    [(_ lang nt0)
     (with-syntax ([new-name (format-id #'lang "~a-~a?" #'lang #'nt0)])
       #`(define (new-name expr)
           (check-nonterminal lang nt0 expr)))]))

(define-syntax (define-nonterminal-predicates stx)
  (syntax-case stx ()
    [(_ lang nt0 ...)
     #`(begin
       (define-nonterminal-predicate lang nt0)
       ...)
     ]))

; The temporary name will be used as a target of the macro expander, but will be
; renamed by make-grammar+.
(define-syntax (define-grammar-match-expander stx)
  (syntax-parse stx
    [(_ tmp-name:id name:id grammar terminalstx ntstx)
     #`(define-match-expander tmp-name
               ; The first argument of the match-expander is the behavior used
               ; with the `match` construct. That is, the match pattern
               ;
               ; (match e
               ;    [(name pat) continuation]
               ;    ...)
               ;
               ; will match against `e` provided:
               ;
               ; 1. `pat` is a member of the `term` syntax class for the grammar
               ; `name`;
               ;
               ; 2. the function `syntax-match?` returns #t when applied to the
               ; syntax-pattern associated with `pat` and the runtime representation of `e`;
               ;
               ; In that case, the match will expand to
               ; (match e
               ;    [pat.match-pattern continuation]
               ;    ...)
               ;
               (lambda (stx)
                 (syntax-parse stx
                   [(_ pat)
                    #:declare pat (term #,(syntax->string #'name)
                                        terminalstx)
                    #'(? (λ (t) (syntax-match? name 'pat.stx-pattern t)) pat.match-pattern)]))
               (lambda (stx)
                 (syntax-parse stx
                   [n:id #'grammar]
                   [(_ pat)
                    #:declare pat (concrete-term
                                   #,(syntax->string #'name)
                                   (set-subtract (list->set terminalstx)
                                                 (list->set ntstx)
                                                 (list->set builtins))
                                   (set-intersect (list->set terminalstx) (list->set builtins)))
                    #'(make-concrete-term! name pat)]
                   [(_ pat depth)
                    #:declare pat (term #,(syntax->string #'name)
                                        terminalstx)
                    #'(make-term! name pat depth)]
                   )))]))



(define-syntax (check-reserved-keywords stx)
  (syntax-parse stx
    [(_ grammar)
             ; Throw an exception if any reserved keywords from
             ; `builtin-keywords` occured in the grammar
             #`(let ([keywords-in-nonterminals
                    (unsafe:set-intersect (grammar-nonterminals grammar)
                                          builtin-keywords)]
                   [keywords-in-terminals
                    (unsafe:set-intersect (grammar-terminals grammar)
                                          builtin-keywords)]
                   )
               (cond
                 [(not (unsafe:set-empty? (unsafe:set-union keywords-in-nonterminals
                                                            keywords-in-terminals)))
                  (unsafe:raise-arguments-error 'define-grammar
                                                "Illegal use of reserved keywords"
                                                "keywords used as nonterminals" keywords-in-nonterminals
                                                "keywords used as terminals" keywords-in-terminals
                                                )]
                 ))
             ]))


; Define a grammar+ instance to encode syntax. Note that the procedure
; associated with the grammar+ instance will expose the match expander via a
; call directly to (name), and (get-terminal-stx name) and (get-nonterminal-stx
; name) will expose the syntax-level data.
(define-syntax (make-grammar+ stx)
  (syntax-parse stx
    [(_ name:id match-expander:id terminals nonterminals)
     (with-syntax ([id-syntax (format-id #'name "~a-syntax" #'name)])
       #`(define-syntax name (grammar+ #'match-expander #'terminals #'nonterminals))
       )]))

(define-syntax (define-grammar stx)
  (syntax-parse stx
    #:datum-literals (::=)
    [(_ name:id
        (~optional (~seq #:extends parent))
        (nt:nonterminal ::= prod:production ...) ...)
     ; If a parent grammar is supplied, we will add the parent's terminals and
     ; nonterminals to the new grammar
     (with-syntax ([old-nts       (if (attribute parent)
                                      (get-nonterminal-stx #'parent)
                                      #`(list ))]
                   [old-terminals (if (attribute parent)
                                      (get-terminal-stx #'parent)
                                      #'(list ))]
                   )
     (let* ([prods         (syntax->datum #'((nt prod ...) ...))]
            [new-nts       (syntax->datum #'(nt ...))]
            [nts           (append (syntax->datum #'old-nts) new-nts)]
            [new-terminals (set->list (prods->terminals prods))]
            [terminals     (append (syntax->datum #'old-terminals) new-terminals)]
            [builtin-nts   (set->list (set-intersect (list->set terminals)
                                                     (list->set builtin-nonterminals)))]
            )
         #`(begin
             (define lang-struct (make-grammar '#,prods #:parent #,(attribute parent)))

             ; Throw an exception if any reserved keywords from
             ; `builtin-keywords` occured in the grammar
             (check-reserved-keywords lang-struct)

             ; Define the match expander
             (define-grammar-match-expander tmp-match-expander name lang-struct '#,terminals '#,nts)

             ; Register the syntax level terminals and nonterminals
             (make-grammar+ name tmp-match-expander #,terminals #,nts)

             ; Add predicates for each nonterminal
             ;
             ; Usage: For each user-defined or builtin nonterminal `nt` that
             ; occurs in the grammar `name`, we define a function `name-nt?`
             ; that takes `x` of any type and returns a boolean---`#t` if `x`
             ; matches the pattern `(name nt)` and `#f` otherwise
             (define-nonterminal-predicates name nt ...)
             (define-nonterminal-predicates name #,@builtin-nts)

             )))]))


(define-syntax (make-concrete-term! stx)
  (syntax-parse stx
    #:literals (unquote)
    #:literal-sets (builtin-terminals)
    [(_ lang:id nil)
     #'seec-empty]
    [(_ lang:id (cons p-first p-rest))
     #`(seec-cons (make-concrete-term! lang p-first) (make-concrete-term! lang p-rest))]
    [(_ lang:id (bv b))
     #`(integer->bv b)]

    [(_ lang:id n:integer)
     #'n]
    [(_ lang:id c:char)
     #'(char c)]
    [(_ lang:id s:string)
     #'(string s)]
    [(_ lang:id b:boolean)
     #'b]
    [(_ lang:id s:id)
     #`(bonsai-terminal (symbol->enum 's))]
    [(_ lang:id (unquote e:expr)) #'e] ; TODO: do  we want to add a check that e
                                       ;  has bonsai?  type? If  so, I'm  afraid
                                       ;  doing  it  here  would add  a  lot  of
                                       ; unnecessary noise on symbolic terms.
    [(_ lang:id (pat ...))
     #`(bonsai-list (list (make-concrete-term! lang pat) ...))]))

(define-syntax (make-term! stx)
  (syntax-parse stx
    [(_ lang:id pat depth:expr)
     #`(let ([tree (make-tree! depth (grammar-max-width lang))])
         (assert
          (parameterize ([check-unreachable #f])
            (match tree
              [(lang pat) #t]
              [_ #f])))
         tree)]))

(define-syntax (make-generator stx)
  (syntax-parse stx
    [(_ pat (~optional (~seq #:where assert-fun:expr)
                       #:defaults ([assert-fun #'(lambda (t) #t)])))
     #'(unsafe:generator
        ()
        (let loop ([found (list)])
          (let* ([tmp pat]
                 [tmpsol (solve (assert
                                 (and (not (ormap (lambda (t) (equal? tmp t)) found))
                                      (assert-fun tmp))))])
            (if (unsat? tmpsol)
                #f
                (let ([newfound (concretize tmp tmpsol)])
                  (unsafe:yield newfound)
                  (loop (cons newfound found)))))))]))

(define-syntax (enumerate stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:count max:expr)
                   #:defaults ([max #'#f]))
        pat
        (~optional (~seq #:where assert-fun:expr)
                   #:defaults ([assert-fun #'(lambda (t) #t)])))
     #'(let ([generator (make-generator pat #:where assert-fun)])
         (unsafe:for/list ([i (unsafe:in-range max)]
                           [t (unsafe:in-producer generator #f)])
                          t))]))

;;;;;;;;;;;
;; TESTS ;;
;;;;;;;;;;;

(module* test rosette/safe
  (require rackunit)
  (require (only-in racket/base
                    raise
                    exn:fail?
                    make-exn:fail
                    current-continuation-marks
                    parameterize))
  (require (submod ".."))
  (require seec/private/match
           seec/private/bonsai3
           seec/private/solver-aided)
  (require (for-syntax syntax/parse))


  (define-grammar test-grammar
    (base     ::= integer natural boolean bitvector)
    (op       ::= + - and or)
    (exp      ::= base (op exp exp) (Var integer))
    (prog     ::= list<exp>))

  (define-grammar test-grammar-extra #:extends test-grammar
     (foo     ::= base (op foo foo) FOO)
     )

  (test-case
      "Concrete term constructors"
    (check-equal? (bonsai-terminal (symbol->enum '+))
                  (test-grammar +))
    (check-equal? (bonsai-terminal (symbol->enum 'FOO))
                  (test-grammar-extra FOO))
    (check-equal? (bonsai-terminal (symbol->enum '+))
                  (test-grammar-extra +))
    (check-equal? (test-grammar-extra (- FOO 3))
                  (bonsai-list (list (test-grammar-extra -)
                                     (test-grammar-extra FOO)
                                     (test-grammar-extra 3))))
    (check-equal? (bonsai-terminal (symbol->enum 'and))
                  (test-grammar and))
    (check-equal? (bonsai-list
                   (list (bonsai-terminal (symbol->enum '+))
                         42
                         #f))
                  (test-grammar (+ 42 #f)))
    )

  (define-syntax (match-check stx)
    (syntax-parse stx
      [(_ val pat body)
       #'(check-not-exn
          (thunk (unless (parameterize ([check-unreachable #f]) (match val [pat body]))
                   (raise (make-exn:fail "Failed match-check"
                                         (current-continuation-marks))))))]))

  (test-case
      "Match expanders"
    (match-check
     (test-grammar 5)
     (test-grammar i:integer)
     (eq? 5 i))
    (match-check
     (test-grammar -5)
     (test-grammar i:integer)
     (eq? -5 i))
    (match-check
     (test-grammar 5)
     (test-grammar n:natural)
     (eq? 5 n))
    (match-check
     (test-grammar #t)
     (test-grammar b:boolean)
     b)
    (match-check
     (test-grammar #f)
     (test-grammar b:boolean)
     (not b))
    (match-check
     (test-grammar (bv 3))
     (test-grammar b:bitvector)
     (eq? (integer->bv 3) b))
    (match-check
     (test-grammar (+ 5 #f))
     (test-grammar exp)
     #t)
    (match-check
     (test-grammar (+ 5 #f))
     (test-grammar (op exp exp))
     #t)
    (match-check
     (test-grammar (+ 5 #f))
     (test-grammar (+ natural boolean))
     #t)
    (match-check
     (test-grammar (cons 5 (cons 5 (cons 5 nil))))
     (test-grammar (cons natural list<natural>))
     #t)
    (match-check
     (test-grammar-extra (- FOO FOO))
     (test-grammar-extra (o:op f:foo FOO))
     (and (equal? o (test-grammar-extra -))
          (equal? f (test-grammar-extra FOO))))
    )

  (test-case
      "Symbolic term constructors"
    (match-check
     (test-grammar integer 1)
     (test-grammar i:integer)
     (integer? i))
    (match-check
     (test-grammar integer 1)
     (test-grammar n:natural)
     (>= n 0))
    (match-check
     (test-grammar exp 3)
     (test-grammar (Var x:integer))
     (= x 0))
    (match-check
     (test-grammar-extra foo 2)
     (test-grammar-extra (b:integer))
     (integer? b))
    (match-check
     (test-grammar-extra foo 2)
     (test-grammar-extra FOO)
     #t)
    )

  (test-case "Types"
     (check-equal? (test-grammar-base? (test-grammar 5)) #t)
     (check-equal? (test-grammar-base? (test-grammar +)) #f)
     (check-equal? (test-grammar-op? (test-grammar 5)) #f)
     (check-equal? (test-grammar-op? (test-grammar +)) #t)
     (check-equal? (test-grammar-natural? (test-grammar 5)) #t)
     (check-equal? (test-grammar-extra-natural? (test-grammar 5)) #t)
     (check-equal? (test-grammar-extra-foo? (test-grammar 5)) #t)
     (check-equal? (test-grammar-extra-foo? (test-grammar-extra +)) #f)
     )
  )
