#lang rosette/safe

(provide (struct-out bonsai)
         (except-out (struct-out bonsai-null) bonsai-null)
         (except-out (struct-out bonsai-terminal) bonsai-terminal)
         (except-out (struct-out bonsai-boolean) bonsai-boolean)
         (except-out (struct-out bonsai-bv) bonsai-bv)
         (except-out (struct-out bonsai-integer) bonsai-integer)
         (except-out (struct-out bonsai-char) bonsai-char)
         (except-out (struct-out bonsai-string) bonsai-string)
         (except-out (struct-out bonsai-list) bonsai-list)
         (rename-out [match-bonsai-null bonsai-null]
                     [match-bonsai-terminal bonsai-terminal]
                     [match-bonsai-boolean bonsai-boolean]
                     [match-bonsai-bv bonsai-bv]
                     [match-bonsai-integer bonsai-integer]
                     [match-bonsai-char bonsai-char]
                     [match-bonsai-string bonsai-string]
                     [match-bonsai-list bonsai-list])

         bonsai-depth
         bonsai-leaves
         enum->symbol
         symbol->enum
         register-enum
         make-tree!
         nondet!
         capture-nondeterminism
         concretize
         concretize+
         instantiate
         expand-solution
         ; utilities
         andmap-indexed
         ; linked lists
         bonsai-cons-match?
         bonsai-cons?
         bonsai-linked-list-match?
         bonsai-linked-list?
         bonsai-ll-head
         bonsai-ll-tail
         bonsai-ll-length
         bonsai-ll-append
         bonsai->racket
         ; bitvectors
         integer->bvw
         set-bvw
         current-bv-width
         bvw?

         bonsai-pretty
         )

(require (for-syntax syntax/parse)
         (only-in racket/base
                  make-parameter
                  parameterize
                  write-string
                  values))
(require "string.rkt"
         "match.rkt")

(define bonsai-width 32)

(define (bonsai-write b port mode)
  (case mode
    [(#f) (bonsai-display b (λ (v) (display v port)))]
    [(#t) (bonsai-print b (λ (v) (display v port)) (lambda (v) (write v port)))]
    [else (bonsai-print b (λ (v) (display v port)) (lambda (v) (print v port)))]))

(define (bonsai-list-equal l r recur)
  (let ([ll (length (bonsai-list-nodes l))]
        [lr (length (bonsai-list-nodes r))])
    (cond
      [(= ll lr) (recur (bonsai-list-nodes l)
                        (bonsai-list-nodes r))]
      [(< ll lr) (and (recur (bonsai-list-nodes l)
                             (take (bonsai-list-nodes r) ll))
                      (andmap bonsai-null?
                              (drop (bonsai-list-nodes r) ll)))]
      [(> ll lr) (and (recur (take (bonsai-list-nodes l) lr)
                             (bonsai-list-nodes r))
                      (andmap bonsai-null?
                              (drop (bonsai-list-nodes l) lr)))])))

(define (bonsai-list-hash l recur)
  (recur (bonsai-list-nodes l)))

(struct bonsai ()
  #:transparent)
(struct bonsai-null bonsai ()
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-list bonsai (nodes)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)]
  #:methods gen:equal+hash
  [(define equal-proc bonsai-list-equal)
   (define hash-proc  bonsai-list-hash)
   (define hash2-proc bonsai-list-hash)])
(struct bonsai-integer bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-char bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-string bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-boolean bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-bv bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-terminal bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])

(define (bonsai-display b out)
  (cond
    [(bonsai-terminal? b)
     (out (enum->symbol (bonsai-terminal-value b)))]
    [(bonsai-integer? b)
     (out (bonsai-integer-value b))]
    [(bonsai-char? b)
     (out (print-char (bonsai-char-value b)))]
    [(bonsai-string? b)
     (out (print-string (bonsai-string-value b)))]
    [(bonsai-boolean? b)
     (out (bonsai-boolean-value b))]
    [(bonsai-bv? b)
     (out (bonsai-bv-value b))]
    [(bonsai-null? b)
     (out "*null*")]
    [(bonsai-list? b)
     (out "(")
     (let ([nodes (filter (lambda (n) (not (bonsai-null? n))) (bonsai-list-nodes b))])
       (unless (empty? nodes)
         (out (first nodes))
         (map (λ (n) (out " ") (out n)) (rest nodes))))
     (out ")")]))

(define (bonsai-print b out recur)
  (cond
    [(bonsai-terminal? b)
     (out "(bonsai-terminal ")
     (recur (bonsai-terminal-value b))
     (out ")")]
    [(bonsai-integer? b)
     (out "(bonsai-integer ")
     (recur (bonsai-integer-value b))
     (out ")")]
    [(bonsai-char? b)
     (out "(bonsai-char ")
     (recur (bonsai-char-value b))
     (out ")")]
    [(bonsai-string? b)
     (out "(bonsai-string ")
     (recur (bonsai-string-value b))
     (out ")")]
    [(bonsai-boolean? b)
     (out "(bonsai-boolean ")
     (recur (bonsai-boolean-value b))
     (out ")")]
    [(bonsai-bv? b)
     (out "(bonsai-bv ")
     (recur (bonsai-bv-value b))
     (out ")")]
    [(bonsai-null? b)
     (out "(bonsai-null)")]
    [(bonsai-list? b)
     (out "(bonsai-list (list ")
     (let ([nodes (bonsai-list-nodes b)])
       (unless (empty? nodes)
         (recur (first nodes))
         (map (λ (n) (out " ") (recur n)) (rest nodes))))
     (out "))")]))

(define (bonsai-pretty b)
  (cond
    [(bonsai-terminal? b)
     (bonsai-terminal-value b)]
    [(bonsai-integer? b)
     (bonsai-integer-value b)]
    [(bonsai-char? b)
     (print-char (bonsai-char-value b))
     ]
    [(bonsai-string? b)
     (print-string (bonsai-string-value b))
     ]
    [(bonsai-boolean? b)
     (bonsai-boolean-value b)
     ]
    [(bonsai-bv? b)
     (bonsai-bv-value b)]
    [(bonsai-null? b) "-"]
    [(bonsai-list? b)
     (add-between (map bonsai-pretty (bonsai-list-nodes b)) " ")
     ]
    ))


(define (bonsai-tree? b)
  (cond
    [(bonsai-list? b)
     (andmap bonsai-tree? (bonsai-list-nodes b))]
    [(and (bonsai? b)
          (not (bonsai-list? b))) #t]
    [else #f]))

(define (bonsai-depth b)
  (cond
    [(bonsai-list? b)
     (let ([children (map bonsai-depth (bonsai-list-nodes b))])
       (+ 1 (apply max children)))]
    [else 1]))

(define (bonsai-leaves b)
  (cond
    [(bonsai-list? b) (foldl + 0 (map bonsai-leaves (bonsai-list-nodes b)))]
    [(bonsai-null? b) 0]
    [else 1]))

(define (bonsai->racket b)
  (cond
    [(bonsai-null? b) #f]
    [(bonsai-terminal? b) (enum->symbol (bonsai-terminal-value b))]
    [(bonsai-boolean? b) (bonsai-boolean-value b)]
    [(bonsai-bv? b) (bonsai-bv-value b)]
    [(bonsai-integer? b) (bonsai-integer-value b)]
    [(bonsai-list? b)
     (map bonsai->racket (filter (lambda (b) (not (bonsai-null? b)))
                                 (bonsai-list-nodes b)))]))

(define nondeterminism (make-parameter (list)))

(define (nondet!)
  (define-symbolic* nondet boolean?)
  (nondeterminism (cons nondet (nondeterminism)))
  nondet)

(define bonsai-bv-width (cond
                          [(equal? (current-bitwidth) #f) 32]
                          [else (- (current-bitwidth) 1)]))
(define (set-bvw w)
  (assert (or (= #f (current-bitwidth))
              (< w (current-bitwidth))))
  (set! bonsai-bv-width w)
  )
(define (current-bv-width) bonsai-bv-width)

; bvw? is a classifier of bitvectors of width (current-bv-width). For example,
; use to create symbolic bitvectors with `(define-symbolic b bvw?)`.
(define bvw? (bitvector (current-bv-width)))

(define (integer->bvw n)
  (integer->bitvector n bvw?))

(define-syntax (capture-nondeterminism stx)
  (syntax-parse stx
    [(_ body ...)
     #'(parameterize ([nondeterminism (list)])
         (define result
           body ...)
         (values result (nondeterminism)))]))

(define (havoc!)
  (define-symbolic* havoc boolean?)
  havoc)

(define (new-boolean!)
  (define-symbolic* bool-val boolean?)
  (bonsai-boolean bool-val))

(define (new-bv!)
  (define-symbolic* bv-val bvw?)
  (bonsai-bv bv-val)
  )

(define (new-integer!)
  (define-symbolic* int-val integer?)
  (bonsai-integer int-val))

(define (new-char!)
  (define char-val (new-symbolic-char))
  (bonsai-char char-val))

(define (new-string! max-length)
  (assert (>= max-length 0))
  (if (havoc!)
      (bonsai-string (new-symbolic-string max-length))
      (new-string! (- max-length 1))))

(define (new-natural!)
  (define-symbolic* nat-val integer?)
  (assert (>= nat-val 0))
  (bonsai-integer nat-val))

(define (new-term!)
  (define-symbolic* term-val (bitvector bonsai-width))
  (bonsai-terminal term-val))

(define *null* (bonsai-null))

(define enum-map '())
(define enum-map-inv '())
(define enum-next 0)

(define (register-enum sym)
  (let ([a (assoc sym enum-map)])
    (if a
        (cdr a)
        (let ([val (bv enum-next bonsai-width)])
          (set! enum-next (add1 enum-next))
          (set! enum-map (cons (cons sym val) enum-map))
          (set! enum-map-inv (cons (cons val sym) enum-map-inv))
          val))))

(define (enum->symbol e)
  (let ([a (assoc e enum-map-inv)])
    (if a
        (cdr a)
        #f)))

(define (symbol->enum e)
  (let ([a (assoc e enum-map)])
    (if a
        (cdr a)
        #f)))

(define (make-list k proc)
  (if (> k 0)
      (cons (proc) (make-list (- k 1) proc))
      '()))

(define (make-tree! depth width)
  (assert (> depth 0))
  (cond
    [(havoc!) (bonsai-list (make-list width (λ () (make-tree! (- depth 1) width))))]
    [(havoc!) (new-term!)]
    [(havoc!) (new-integer!)]
    [(havoc!) (new-boolean!)]
    [(havoc!) (new-bv!)]
    [(havoc!) (new-natural!)]
    [(havoc!) (new-char!)]
    [(havoc!) (new-string! depth)]
    [else *null*]))

(define (concretize v sol)
  (evaluate v (complete-solution sol (symbolics v))))

(define (instantiate v)
  (let ([sol (solve v)])
    (if (unsat? sol)
        sol
        (concretize v sol))))

(define (expand-solution sol expr-list)
  (complete-solution sol (flatten (map symbolics expr-list))))
(define (concretize+ v sol)
  (evaluate v sol))

;;;;;;;;;;;;;;;;;;
;; Linked lists ;;
;;;;;;;;;;;;;;;;;;

(define (to-indexed xs)
  (define (to-indexed/int xs i)
    (if (empty? xs)
        '()
        (cons (cons i (car xs)) (to-indexed/int (cdr xs) (+ i 1)))))
  (to-indexed/int xs 0))
(define (andmap-indexed f ls)
  (andmap (lambda (e) (let ([i (car e)]
                            [n (cdr e)])
                        (f i n)))
          (to-indexed ls)))


; The given tree a bonsai-linked-list of the shape
; (list<ty> ::= nil (x:ty l:list<ty>))
; that is, it is a bonsai tree that is either null, or has the shape
; (x xs y1 .. yn)
; where:
;   - x matches the pattern a 
;   - xs matches the pattern as
;   - each yi is null
(define (bonsai-cons-match? syntax-match-a? syntax-match-as? tree)
  (and (bonsai-list? tree)
       (andmap-indexed
        (λ (i tree-i) (cond
                        [(= i 0) (syntax-match-a? tree-i)]
                        [(= i 1) (syntax-match-as? tree-i)]
                        [else (bonsai-null? tree-i)]))
        (bonsai-list-nodes tree))))
(define (bonsai-linked-list-match? syntax-match-lang? a tree)
  (or (bonsai-null? tree)
      (bonsai-cons-match? (curry syntax-match-lang? a)
                          (curry bonsai-linked-list-match? syntax-match-lang? a)
                          tree)))


(define (bonsai-cons? tree)
  (bonsai-cons-match? (λ (x) #t) (λ (x) #t) tree))
(define (bonsai-ll-head tree)
  (first (bonsai-list-nodes tree)))
(define (bonsai-ll-tail tree)
  (second (bonsai-list-nodes tree)))
(define (bonsai-linked-list? tree)
  (or (bonsai-null? tree)
      (and (bonsai-cons? tree)
           (bonsai-linked-list? (bonsai-ll-tail tree)))))



(define (bonsai-ll-length tree)
  (cond
    [(bonsai-null? tree) 0]
    [(bonsai-cons? tree)
     (+ 1 (bonsai-ll-length (bonsai-ll-tail tree)))]
    ))
(define (bonsai-ll-append tree1 tree2)
  (cond
    [(bonsai-null? tree1) tree2]
    [(bonsai-cons? tree1)
     (bonsai-list (map (λ (x) (let ([i (car x)]
                                    [tree-i (cdr x)])
                                (cond
                                  [(= i 0) tree-i]
                                  [(= i 1) (bonsai-ll-append tree-i tree2)]
                                  [else (bonsai-null)])))
                       (to-indexed (bonsai-list-nodes tree1))))]))

(define-match-expander match-bonsai-null
  (lambda (stx)
    (syntax-parse stx
      [(_)
       #'(? bonsai-null? _)]))
  (make-rename-transformer #'bonsai-null))

(define-match-expander match-bonsai-terminal
  (lambda (stx)
    (syntax-parse stx
      [(_ pat)
       #'(? bonsai-terminal? (! bonsai-terminal-value pat))]))
  (make-rename-transformer #'bonsai-terminal))

(define-match-expander match-bonsai-boolean
  (lambda (stx)
    (syntax-parse stx
      [(_ pat)
       #'(? bonsai-boolean? (! bonsai-boolean-value pat))]))
  (make-rename-transformer #'bonsai-boolean))

(define-match-expander match-bonsai-bv
  (lambda (stx)
    (syntax-parse stx
      [(_ pat)
       #'(? bonsai-bv? (! bonsai-bv-value pat))]))
  (make-rename-transformer #'bonsai-bv))

(define-match-expander match-bonsai-integer
  (lambda (stx)
    (syntax-parse stx
      [(_ pat)
       #'(? bonsai-integer? (! bonsai-integer-value pat))]))
  (make-rename-transformer #'bonsai-integer))

(define-match-expander match-bonsai-char
  (lambda (stx)
    (syntax-parse stx
      [(_ pat)
       #'(? bonsai-char? (! bonsai-char-value pat))]))
  (make-rename-transformer #'bonsai-char))

(define-match-expander match-bonsai-string
  (lambda (stx)
    (syntax-parse stx
      [(_ pat)
       #'(? bonsai-string? (! bonsai-string-value pat))]))
  (make-rename-transformer #'bonsai-string))

(define-match-expander match-bonsai-list
  (lambda (stx)
    (syntax-parse stx
      [(_ pat ...)
       (with-syntax ([len (datum->syntax stx (length (syntax->list #'(pat ...))))])
         #'(? bonsai-list?
              (! (lambda (blist) (take (bonsai-list-nodes blist) len))
                 (list pat ...))))]))
  (make-rename-transformer #'bonsai-list))

(module* test rosette/safe
  (require rackunit)
  (require (submod ".."))
  (require seec/private/match)

  (define null (bonsai-null))
  (define term (bonsai-terminal (bv 2 32)))
  (define bool (bonsai-boolean #t))
  (define bv+  (bonsai-bv (integer->bvw 4)))
  (define int  (bonsai-integer 5))
  (define char (bonsai-char 36))
  (define str  (bonsai-string (list 36 36 36)))
  (define blst (bonsai-list (list term null)))

  (test-case
      "Predicate matches"
    (check-equal? null (match null [(? bonsai-null? x) x]))
    (check-equal? term (match term [(? bonsai-terminal? x) x]))
    (check-equal? bool (match bool [(? bonsai-boolean? x) x]))
    (check-equal? bv+  (match bv+  [(? bonsai-bv? x) x]))
    (check-equal? int  (match int  [(? bonsai-integer? x) x]))
    (check-equal? char (match char [(? bonsai-char? x) x]))
    (check-equal? str  (match str  [(? bonsai-string? x) x]))
    (check-equal? blst (match blst [(? bonsai-list? x) x])))

(test-case
    "Match expanders"
  (check-equal? #t
                (match null
                  [(bonsai-null) #t]
                  [_ #f]))
  (check-equal? (bonsai-terminal-value term)
                (match term
                  [(bonsai-terminal v) v]))
  (check-equal? (bonsai-boolean-value bool)
                (match bool
                  [(bonsai-boolean v) v]))
  (check-equal? (bonsai-bv-value bv+)
                (match bv+
                  [(bonsai-bv v) v]))
  (check-equal? (bonsai-integer-value int)
                (match int
                  [(bonsai-integer v) v]))
  (check-equal? (bonsai-char-value char)
                (match char
                  [(bonsai-char v) v]))
  (check-equal? (bonsai-string-value str)
                (match str
                  [(bonsai-string v) v]))
  (check-equal? (bonsai-list-nodes blst)
                (match blst
                  [(bonsai-list x y) (list x y)]))))
