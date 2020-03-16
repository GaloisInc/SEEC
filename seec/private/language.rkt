#lang rosette/safe

(provide define-language
         syntax-match?
         enumerate)

(require "bonsai2.rkt"
         "match.rkt")

(require (for-syntax syntax/parse)
         (prefix-in unsafe:
                    (combine-in
                     (only-in racket/match)
                     (only-in racket
                              for
                              for/fold
                              for/hash
                              in-list
                              in-set
                              list->set
                              set->list
                              set
                              set-add
                              set-union
                              set-subtract
                              hash
                              hash-set
                              hash->list
                              values))))

(struct language (nonterminals
                  terminals
                  productions
                  max-width))

(define (max-width ls)
  (cond
    [(list? ls) (apply max (length ls) (map max-width ls))]
    [else 0]))

(define (make-language rules)
  (define-values (nonterminals metavars productions prod-max-width)
    (unsafe:for/fold ([nonterminals (unsafe:set)]
               [metavars     (unsafe:set 'integer 'boolean 'natural)]
               [productions  (unsafe:hash)]
               [prod-width   0])
              ([production (unsafe:in-list rules)])
      (let* ([nt             (first production)]
             [new-nts        (unsafe:set-add nonterminals nt)]
             [new-meta       (unsafe:set-union metavars (unsafe:list->set (flatten production)))]
             [new-prods      (unsafe:hash-set productions nt (rest production))]
             [new-prod-width (apply max prod-width (map max-width (rest production)))])
        (unsafe:values new-nts new-meta new-prods new-prod-width))))
  (let* ([terminals (unsafe:set-subtract metavars nonterminals)])
    (unsafe:for ([mv (unsafe:in-set metavars)])
      (register-enum mv))
    (language (unsafe:set->list nonterminals)
              (unsafe:set->list terminals)
              (unsafe:hash->list productions)
              prod-max-width)))

(define (to-indexed xs)
  (define (to-indexed/int xs i)
    (if (empty? xs)
        '()
        (cons (cons i (car xs)) (to-indexed/int (cdr xs) (+ i 1)))))
  (to-indexed/int xs 0))

(define (syntax-match? lang pattern tree)
  (for/all [(tree tree)]
    (cond
      [(list? pattern)
       (let ([pattern-length (length pattern)])
         (and (bonsai-list? tree)
              (andmap (λ (e) (let ([i (car e)]
                                   [n (cdr e)])
                               (cond
                                 [(< i pattern-length) (syntax-match? lang (list-ref pattern i) n)]
                                 [else (bonsai-null? n)])))
                      (to-indexed (bonsai-list-nodes tree)))))]
      [(equal? 'integer pattern)
       (bonsai-integer? tree)]
      [(equal? 'natural pattern)
       (and (bonsai-integer? tree)
            (>= (bonsai-integer-value tree) 0))]
      [(equal? 'boolean pattern)
       (bonsai-boolean? tree)]
      [(member pattern (language-nonterminals lang))
       (let ([productions (cdr (assoc pattern (language-productions lang)))])
         (ormap (λ (pat) (syntax-match? lang pat tree)) productions))]
      [(member pattern (language-terminals lang))
       (and (bonsai-terminal? tree)
            (equal? (symbol->enum pattern) (bonsai-terminal-value tree)))]
      [else #f])))

(begin-for-syntax
  (define (syntax->string stx)
    (symbol->string (syntax->datum stx)))
  (define (string->syntax stx str)
    (datum->syntax stx (string->symbol str)))

  (define-syntax-class (term lang-name terminals)
    #:attributes (match-pattern stx-pattern depth)
    #:description (format "~a pattern ~a" lang-name terminals)
    #:opaque
    (pattern n:id
             #:when (and (= (length (string-split (syntax->string #'n) ":")) 1)
                         (set-member? terminals (syntax->datum #'n)))
             #:attr match-pattern #'_
             #:attr stx-pattern   #'n
             #:attr depth         #'1)
    (pattern n:id
             #:when (and (= (length (string-split (syntax->string #'n) ":")) 2)
                         (set-member? terminals (string->symbol (second (string-split (syntax->string #'n) ":")))))
             #:attr match-pattern (string->syntax #'n (first (string-split (syntax->string #'n) ":")))
             #:attr stx-pattern   (string->syntax #'n (second (string-split (syntax->string #'n) ":")))
             #:attr depth         #'1)
    (pattern n:integer
             #:when (and (set-member? terminals 'natural) (>= (syntax->datum #'n) 0))
             #:attr match-pattern #'(bonsai-integer (? (λ (v) (equal? n v)) _))
             #:attr stx-pattern   #'integer
             #:attr depth         #'1)
    (pattern n:integer
             #:when (set-member? terminals 'integer)
             #:attr match-pattern #'(bonsai-integer (? (λ (v) (equal? n v)) _))
             #:attr stx-pattern   #'integer
             #:attr depth         #'1)
    (pattern b:boolean
             #:when (set-member? terminals 'boolean)
             #:attr match-pattern #'(bonsai-boolean (? (λ (v) (equal? b v)) _))
             #:attr stx-pattern   #'boolean
             #:attr depth         #'1)
    (pattern (p ...)
             #:declare p (term lang-name terminals)
             #:attr match-pattern #'(bonsai-list p.match-pattern ...)
             #:attr stx-pattern   #'(p.stx-pattern ...)
             #:attr depth         (datum->syntax
                                   #'(p ...)
                                   (add1 (apply max (syntax->datum #'(p.depth ...)))))))

  (define-syntax-class (concrete-term lang-name terminals special)
    #:literals (unquote)
    #:description (format "concrete ~a pattern ~a" lang-name terminals)
    #:opaque
    (pattern n:id
             #:when (and (= (length (string-split (syntax->string #'n) ":")) 1)
                         (set-member? terminals (syntax->datum #'n))))
    (pattern n:integer
             #:when (and (set-member? special 'natural) (>= (syntax->datum #'n) 0)))
    (pattern n:integer
             #:when (set-member? special 'integer))
    (pattern b:boolean
             #:when (set-member? special 'boolean))
    (pattern (unquote expr))
    (pattern (p ...)
             #:declare p (concrete-term lang-name terminals special)))

  (define-syntax-class nonterminal
    #:description "nonterminal"
    #:opaque
    (pattern nt:id
             #:when (not (member (syntax->datum #'nt) '(integer natural boolean)))))

  (define-syntax-class builtin
    #:description "built-in nonterminal"
    #:opaque
    (pattern nt:id
             #:when (member (syntax->datum #'nt) '(integer natural boolean))))

  (define-syntax-class production
    #:description "production"
    #:opaque
    #:datum-literals (integer natural boolean)
    (pattern nt:nonterminal)
    (pattern nt:builtin)
    (pattern (p:production ...))))

(define-syntax (define-language stx)
  (syntax-parse stx
    #:datum-literals (::=)
    [(_ name:id (nt:nonterminal ::= prod:production ...) ...)
     (let ([prods         (syntax->datum #'((nt prod ...) ...))]
           [nts           (syntax->datum #'(nt ...))])
       #`(begin
           (define lang-struct
             (make-language
              '#,prods))
           
           (define-match-expander name
             (lambda (stx)
               (syntax-parse stx
                 [(_ pat)
                  #:declare pat (term #,(syntax->string #'name)
                                      (list->set (flatten '#,prods)))
                  #'(? (λ (t) (syntax-match? name 'pat.stx-pattern t)) pat.match-pattern)]))
             (lambda (stx)
               (syntax-parse stx
                 [n:id #'lang-struct]
                 [(_ pat)
                  #:declare pat (concrete-term
                                 #,(syntax->string #'name)
                                 (set-subtract (list->set (flatten '#,prods))
                                               (list->set '#,nts))
                                 (set-intersect (list->set (flatten '#,prods))
                                                (set 'integer 'boolean 'natural)))
                  #'(make-concrete-term! name pat)]
                 [(_ pat depth)
                  #:declare pat (term #,(syntax->string #'name)
                                      (list->set (flatten '#,prods)))
                  #'(make-term! name pat depth)])))))]))

(define-syntax (make-concrete-term! stx)
  (syntax-parse stx
    #:literals (unquote)
    [(_ lang:id n:integer)
     #`(bonsai-integer n)]
    [(_ lang:id b:boolean)
     #`(bonsai-boolean b)]
    [(_ lang:id s:id)
     #`(bonsai-terminal (symbol->enum 's))]
    [(_ lang:id (unquote e:expr))
     #'e]
    [(_ lang:id (pat ...))
     #`(bonsai-list (list (make-concrete-term! lang pat) ...))]))

(define-syntax (make-term! stx)
  (syntax-parse stx
    [(_ lang:id pat depth:expr)
     #`(let ([tree (make-tree! depth (language-max-width lang))])
         (assert
          (match tree
            [(lang pat) #t]
            [_ #f]))
         tree)]))

(define-syntax (enumerate stx)
  (syntax-parse stx
    [(_ pat assert-fun:expr max:expr)
     #'(let ()
         (define (loop found count)
           (if (> count 0)
               (let* ([tmp pat]
                      [tmpsol (solve (assert (and (not (ormap (λ (f) (equal? tmp f)) found))
                                                  (assert-fun tmp))))])
                 (if (unsat? tmpsol)
                     found
                     (loop (cons (concretize tmp tmpsol) found) (- count 1))))
               found))
         (loop '() max))]))
