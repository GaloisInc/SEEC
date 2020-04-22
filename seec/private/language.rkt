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

; OSTODO: properly populate the language for polymorphic types
(define (make-language rules)
  (define-values (nonterminals metavars productions prod-max-width)
    (unsafe:for/fold ([nonterminals (unsafe:set)]
                      [metavars     (unsafe:set 'integer 'boolean 'natural 'char 'string 'list)]
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

; is the given tree a bonsai-linked-list of the shape
; list-a ::= nil (x:a l:list-a)
(define (bonsai-linked-list? syntax-match? a tree)
  (andmap (λ (e) (let ([i (car e)]
                       [d (cdr e)])
                   (cond                     
                     [(= i 0) (syntax-match? a d)]
                     [(= i 1) (bonsai-linked-list? syntax-match? a d)]
                     [else (bonsai-null? d)])))))

(define (syntax-match? lang pattern tree)
  (for/all [(tree tree)]
    (cond
      ; test if pattern == (list pattern')
      [(and (list? pattern)
            (= (length pattern) 2)
            (equal? (first pattern) 'list))
       (let ([ty (second pattern)])
         (and (bonsai-list? tree) (bonsai-linked-list? (syntax-match? lang) ty tree)))]
      ; test if pattern is a list of patterns
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
      [(equal? 'char pattern)
       (bonsai-char? tree)]
      [(equal? 'string pattern)
       (bonsai-string? tree)]
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

  (define (syntax-has-colon? stx)
    (string-contains? (syntax->string stx) ":"))
  (define (before-colon stx)
    (string->syntax stx (first (string-split (syntax->string stx) ":"))))
  (define (after-colon stx)
    (string->syntax stx (second (string-split (syntax->string stx) ":"))))
  (define (syntax-is-polymorphic-type? ty stx)
    (let ([str (syntax->string stx)])
      (and
       (string-prefix? str ty)
       (string-contains? str "<")
       (string-suffix? str ">")
    )))
  ; if stx is of the form t<a>,
  ; returns (t . a)
  (define (parse-polymorphic-type stx)
    (let* ([str (syntax->string stx)]
           [strsplit (string-split str "<")]
           [t (first strsplit)]
           [a (string-trim (string-join (second strsplit) "<") ">" #:left? #f)])
      `( ,(string->syntax stx t)  . ,(string->syntax stx a))
      ))

  
  ; returns true if pats has the following form:
  ; pats ::= nt | list<pats>
  (define (is-nested-list-of-terminals? terminals pat)
    (let ([pats (syntax->datum pat)])
      (cond
        [(and (list? pats)
              (= (length pats) 1))
         (set-member? terminals pats)]
        [(and (list? pats)
              (= (length pats) 1)
              (syntax-is-polymorphic-type? "list" pats)
         (is-nested-list-of-terminals? terminals (second (parse-polymorphic-type pats))))]
        [else #f])))

  (define-syntax-class (term lang-name terminals)
    #:attributes (match-pattern stx-pattern depth)
    #:datum-literals (nil cons)
    #:description (format "~a pattern ~a" lang-name terminals)
    #:opaque
    (pattern n:id
             #:when (and (not (syntax-has-colon? #'n))
                         (is-nested-list-of-terminals? terminals #'n))
             #:attr match-pattern #'_
             #:attr stx-pattern   #'n
             #:attr depth         #'1)
    (pattern n:id
             #:when (and (syntax-has-colon? #'n)
                         (is-nested-list-of-terminals? terminals (after-colon #'n)))
             #:attr match-pattern (before-colon #'n)
             #:attr stx-pattern   (after-colon #'n)
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
    (pattern c:char
             #:when (set-member? terminals 'char)
             #:attr match-pattern #'(bonsai-char (? (λ (v) (equal? c v)) _))
             #:attr stx-pattern   #'char
             #:attr depth         #'1)
    (pattern s:string
             #:when (set-member? terminals 'string)
             #:attr match-pattern #'(bonsai-string (? (λ (v) (equal? s v)) _))
             #:attr stx-pattern   #'string
             #:attr depth         #'1)
    (pattern b:boolean
             #:when (set-member? terminals 'boolean)
             #:attr match-pattern #'(bonsai-boolean (? (λ (v) (equal? b v)) _))
             #:attr stx-pattern   #'boolean
             #:attr depth         #'1)

    (pattern nil
             #:when (set-member? terminals 'list)
             #:attr match-pattern #'(bonsai-null)
             #:attr stx-pattern   #'nil
             #:attr depth         #'0)
    (pattern (cons p-first p-rest)
             #:declare p-first    (term lang-name terminals)
             #:declare p-rest     (term lang-name terminals)
             #:attr match-pattern #'(bonsai-list p-first.match-pattern p-last.match-pattern)
             #:attr stx-pattern   #'(cons p-first.stx-pattern p-rest.stx-pattern)
             #:attr depth         (datum->syntax 
                                   #'((~datum 'cons) p-first p-last)
                                   (add1 (apply max (syntax->datum #'p-first.depth #'p-rest.depth)))))
    (pattern (p ...)
             #:declare p (term lang-name terminals)
             #:attr match-pattern #'(bonsai-list p.match-pattern ...)
             #:attr stx-pattern   #'(p.stx-pattern ...)
             #:attr depth         (datum->syntax
                                   #'(p ...)
                                   (add1 (apply max (syntax->datum #'(p.depth ...)))))))

  (define-syntax-class (concrete-term lang-name terminals special)
    #:literals (unquote)
    #:datum-literals (nil cons)
    #:description (format "concrete ~a pattern ~a" lang-name terminals)
    #:opaque
    (pattern n:id
             #:when (and (not (syntax-has-colon? #'n))
                         (is-nested-list-of-terminals? terminals #'n)))
    (pattern n:integer
             #:when (and (set-member? special 'natural) (>= (syntax->datum #'n) 0)))
    (pattern n:integer
             #:when (set-member? special 'integer))
    (pattern c:char
             #:when (set-member? special 'char))
    (pattern s:string
             #:when (set-member? special 'string))
    (pattern b:boolean
             #:when (set-member? special 'boolean))
    (pattern (unquote expr))
    (pattern nil)
    (pattern (cons p-first p-rest)
             #:declare p-first (concrete-term lang-name terminals special)
             #:declare p-rest (concrete-term lang-name terminals special))
    (pattern (p ...)
             #:declare p (concrete-term lang-name terminals special)))

  (define-syntax-class nonterminal
    #:description "nonterminal"
    #:opaque
    (pattern nt:id
             #:when (not (member (syntax->datum #'nt) '(integer natural boolean char string list)))))

  (define-syntax-class builtin
    #:description "built-in nonterminal"
    #:opaque
    (pattern nt:id
             #:when (member (syntax->datum #'nt) '(integer natural boolean char string list))))

  (define-syntax-class production
    #:description "production"
    #:opaque
    #:datum-literals (integer natural boolean char string list)
    (pattern nt:nonterminal)
    (pattern nt:builtin)
    (pattern (list p:production))
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
                                                (set 'integer 'boolean 'natural 'char 'string)))
                  #'(make-concrete-term! name pat)]
                 [(_ pat depth)
                  #:declare pat (term #,(syntax->string #'name)
                                      (list->set (flatten '#,prods)))
                  #'(make-term! name pat depth)])))))]))

; what is the difference between make-concrete-term! and the match-pattern
; attribute in the term syntax class? Just code duplication since one is at
; compile time and not runtime?
(define-syntax (make-concrete-term! stx)
  (syntax-parse stx
    #:literals (unquote)
    #:datum-literals (nil cons)
    [(_ lang:id n:integer)
     #`(bonsai-integer n)]
    [(_ lang:id c:char)
     #`(bonsai-char c)]
    [(_ lang:id s:string)
     #`(bonsai-string s)]
    [(_ lang:id b:boolean)
     #`(bonsai-boolean b)]
    [(_ lang:id s:id)
     #`(bonsai-terminal (symbol->enum 's))]
    [(_ lang:id (unquote e:expr))
     #'e]
    [(_ lang:id nil)
     #'(bonsai-null)]
    [(_ lang:id (cons p-first p-rest))
     #`(bonsai-list (list (make-concrete-term! lang p-first) (make-concrete-term! lang p-rest)))]
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
