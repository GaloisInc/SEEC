#lang rosette/safe

; A version of bonsai that doesn't use structs

(require (for-syntax syntax/parse)
         (only-in racket/base
                  make-parameter
                  parameterize
                  write-string
                  values
                  ))
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))
(require racket/contract)
(require rackunit)
(require rackunit/text-ui)

(require "string.rkt"
         "match.rkt")

(provide bonsai?
         (except-out (struct-out bonsai-null) bonsai-null)
         (except-out (struct-out bonsai-terminal) bonsai-terminal)
         (except-out (struct-out bonsai-list) bonsai-list)
         (rename-out [match-bonsai-null bonsai-null]
                     [match-bonsai-terminal bonsai-terminal]
                     [match-bonsai-list bonsai-list]
                     )

         bonsai-depth
         seec->racket

         ; utilities
         make-tree!
         havoc!
         new-boolean!
         new-bv!
         new-integer!
         new-natural!
         new-char!
         new-string!
         new-term!
         make-list

         ; nondeterminism
         nondet!
         capture-nondeterminism

         ; bitvectors
         integer->bv
         set-bitwidth
         get-bv-width

         ; seec-lists
         seec-list?
         seec-list-of?
         seec-empty?
         seec-empty
         seec-cons?
         seec-cons
         seec-singleton
         seec-head
         seec-tail
         list->seec
         seec->list
         seec-length
         seec-append
         ; seec-list-utilities
         seec-cons-match?
         seec-list-match?

         ; solver interfaces
         concretize
         instantiate
         concretize+
         expand-solution

         ; utilities
         enum->symbol
         symbol->enum
         register-enum
         andmap-indexed
         )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bonsai data structures ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (bonsai-write b port mode)
  (case mode
    [(#f) (bonsai-display b (λ (v) (display v port)))]
    [(#t) (bonsai-print b (λ (v) (display v port)) (lambda (v) (write v port)))]
    [else (bonsai-print b (λ (v) (display v port)) (lambda (v) (print v port)))]))
(define (bonsai-list-equal l r recur)
  (let* ([l-nodes (bonsai-list-nodes l)]
         [r-nodes (bonsai-list-nodes r)]
         [ll (length l-nodes)]
         [lr (length r-nodes)])
    (cond
      [(= ll lr) (recur l-nodes r-nodes)]
      [(< ll lr) (and (recur l-nodes (take r-nodes ll))
                      (andmap bonsai-null?
                              (drop r-nodes ll)))]
      [(> ll lr) (and (recur (take l-nodes lr) r-nodes)
                      (andmap bonsai-null?
                              (drop l-nodes lr)))])))
(define (bonsai-list-hash l recur)
  (recur (bonsai-list-nodes l)))

(struct bonsai-terminal (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-null ()
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(define *null* (bonsai-null))
(struct bonsai-list (nodes)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)]
  #:methods gen:equal+hash
  [(define equal-proc bonsai-list-equal)
   (define hash-proc  bonsai-list-hash)
   (define hash2-proc bonsai-list-hash)])


; A bonsai data structure is either: (1) a list of bonsai data structures; (2) bonsai-terminals;
;                                    (3) a primitive type: integer, boolean, char, string, bitvector
(define (bonsai? b)
  (or (bonsai-terminal? b)
      (bonsai-null? b)
      (integer? b)
      (boolean? b)
      (char? b)
      (string? b)
      (bv? b)
      (bonsai-list? b)
      #;(and (bonsai-list? b)
           (andmap bonsai? (bonsai-list-nodes b)))
      ))

(define (bonsai-depth b)
  (cond
    [(bonsai-list? b)
     (let ([children (map bonsai-depth (bonsai-list-nodes b))])
       (+ 1 (apply max children)))]
    [else 1]))

(define (seec->racket b)
  (cond
    [(bonsai-null? b) #f]
    [(bonsai-terminal? b) (enum->symbol (bonsai-terminal-value b))]
    [(bonsai-list? b)
     (map seec->racket (filter (lambda (b) (not (bonsai-null? b)))
                                 (bonsai-list-nodes b)))]
    [else b]
    ))

;;;;;;;;;;;;;;;;;;;;
;; Nondeterminism ;;
;;;;;;;;;;;;;;;;;;;;

(define nondeterminism (make-parameter (list)))

(define (nondet!)
  (define-symbolic* nondet boolean?)
  (nondeterminism (cons nondet (nondeterminism)))
  nondet)

(define-syntax (capture-nondeterminism stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:nondet nondet)
                   #:defaults ([nondet '#f]))
        body ...)
     #'(if nondet
           (parameterize ([nondeterminism (list)])
             (define result
               body ...)
             (values result (nondeterminism)))
           (begin
             (define result
               body ...)
             (values result (list )))
           )]
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bitwidth and bitvector width ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bonsai-width 32)

; current-bv-width is  a racket  parameter that holds  the width  of bonsai/seec
; bitvectors. We  use a parameter  to store this instead  of letting it  vary by
; use-site because otherwise make-tree! would need  to be a much larger union of
; bitvectors of all possible sizes.
(define current-bv-width
  (make-parameter (if (equal? (current-bitwidth) #f)
                      32
                      (- (current-bitwidth) 1))
                  (λ (w) (cond
                           [(equal? (current-bitwidth) #f) w]
                           [(< 0 w (current-bitwidth)) w]
                           [else (- (current-bitwidth) 1)]
                           ))
                  ))

(define set-bitwidth
  (λ (int-width [bv-width (- int-width 1)])
    (cond
      [(not (positive? bv-width))
       (raise-argument-error 'set-bitwidth
                             "positive?" bv-width)]

      [(not (or (positive? int-width) (equal? int-width #f)))
       (raise-argument-error 'set-bitwidth
                             "(or/c positive? #f)" int-width)]

      [(and (positive? int-width) (not (< bv-width int-width)))
       (raise-arguments-error 'set-bitwidth
                              "bv-width argument should be strictly less than int-width argument"
                              "int-width" int-width
                              "bv-width" bv-width)]

      [else (begin
              (current-bitwidth int-width)
              (current-bv-width bv-width))]
      )))
(define (get-bv-width) (current-bv-width))

(define (integer->bv n)
  (integer->bitvector n (bitvector (current-bv-width))))

;;;;;;;;;;;;;;;;;;
;; Constructors ;;
;;;;;;;;;;;;;;;;;;


(define (havoc!)
  (define-symbolic* havoc boolean?)
  havoc)

(define (new-boolean!)
  (define-symbolic* bool-val boolean?)
  bool-val)

(define (new-bv!)
  (define-symbolic* bv-val (bitvector (current-bv-width)))
  bv-val)

(define (new-integer!)
  (define-symbolic* int-val integer?)
  int-val)

(define (new-natural!)
  (define-symbolic* nat-val integer?)
  (assert (>= nat-val 0))
  nat-val)

(define (new-char!)
  (define char-val (new-symbolic-char*))
  char-val)


(define (new-string! max-length)
  (assert (>= max-length 0))

  ; First produce the naked list of seec-char?
  (define/contract (new-string+ len)
    (-> integer? list?)
    (cond
      [(= len 0) (list )]
      [(havoc!)  (list )]
      [else      (let ([c  (new-char!)])
                   (cons c (new-string+ (- len 1)))
                   )]
      ))
  (char-list->string (new-string+ max-length))
  #;(if (havoc!)
      (new-symbolic-string* max-length)
      (new-string! (- max-length 1)))
  )


; Define abstract terminal values
(define (new-term!)
  (define-symbolic* term-val (bitvector bonsai-width))
  (bonsai-terminal term-val))

; Make a list of length k, with elements coming from the procedure (proc)
(define (make-list k proc)
  (if (> k 0)
      (cons (proc) (make-list (- k 1) proc))
      '()))

; Make a bonsai tree of given depth and width. Both depth and width should be
; concrete positive integers
(define (make-tree! depth width)
  (assert (> depth 0))
  (cond
    #;[(<= depth 0) *null*]
    [(havoc!) (bonsai-list (make-list width (λ () (make-tree! (- depth 1) width))))]
    [(havoc!) (new-term!)]
    [(havoc!) (let ([x (new-integer!)])
                  (cond [(havoc!)
                         (assert (>= x 0))]) ; either a natural number, or not
                  x)]
    [(havoc!) (new-boolean!)]
    [(havoc!) (new-bv!)]
    [(havoc!) (new-char!)]
    [(havoc!) (new-string! depth)]
    [else     *null*]
    ))


;;;;;;;;;;;;;;;;;;;;;
;; Match expanders ;;
;;;;;;;;;;;;;;;;;;;;;

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

(define-match-expander match-bonsai-list
  (lambda (stx)
    (syntax-parse stx
      [(_ pat ...)
       (with-syntax ([len (datum->syntax stx (length (syntax->list #'(pat ...))))])
         #'(? bonsai-list?
              (! (lambda (blist) (take (bonsai-list-nodes blist) len))
                 (list pat ...))))]))
  (make-rename-transformer #'bonsai-list))


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


(define (seec-empty? tree) (bonsai-null? tree))

; The given tree a seec-list/bonsai-linked-list of the shape
; (list<ty> ::= nil (x:ty l:list<ty>))
; that is, it is a bonsai tree that is either null, or has the shape
; (x xs y1 .. yn)
; where:
;   - x matches the pattern a 
;   - xs matches the pattern as
;   - each yi is null
(define (seec-cons-match? syntax-match-a? syntax-match-as? tree)
  (for/all [(tree tree)]
  (and (bonsai-list? tree)
       (list? (bonsai-list-nodes tree))
       (andmap-indexed
        (λ (i tree-i) (cond
                        [(= i 0) (syntax-match-a? tree-i)]
                        [(= i 1) (syntax-match-as? tree-i)]
                        [else (bonsai-null? tree-i)]))
        (bonsai-list-nodes tree)))))
(define (seec-list-match? syntax-match-lang? a tree)
  (or (seec-empty? tree)
      (seec-cons-match? (curry syntax-match-lang? a)
                        (curry seec-list-match? syntax-match-lang? a)
                        tree)))

(define (seec-cons? tree)
  (seec-cons-match? (λ (x) #t) (λ (x) #t) tree))
(define (seec-head tree)
  (first (bonsai-list-nodes tree)))
(define (seec-tail tree)
  (second (bonsai-list-nodes tree)))

(define (seec-list? tree)
  (or (seec-empty? tree)
      (and (seec-cons? tree)
           (bonsai? (seec-head tree))
           (seec-list? (seec-tail tree)))))

; TODO: get rid of contracts?
(define (seec-cons x xs)
  #;(-> bonsai? seec-list? seec-list?)
  (bonsai-list (list x xs))) ; This is `list` here, not a cons, because
                             ; seec-lists are made up of cons cells
(define seec-empty *null*)
(define (seec-singleton x)
  #;(-> bonsai? seec-list?)
  (seec-cons x seec-empty))
(define (list->seec l)
  #;(-> (listof bonsai?) seec-list?)
  (cond
    [(empty? l) seec-empty]
    [else (seec-cons (first l) (list->seec (rest l)))]
    ))
(define (seec->list l)
  #;(-> seec-list? (listof bonsai?))
  (cond
    [(seec-empty? l) (list )]
    [(seec-cons? l)
     (cons (seec-head l) (seec->list (seec-tail l)))]
    ))

(define (seec-list-of? tp? tree)
  (andmap tp? (seec->list tree)))

(define (seec-length tree)
  #;(-> seec-list? integer?)
  (cond
    [(seec-empty? tree) 0]
    [(seec-cons? tree)
     (+ 1 (seec-length (seec-tail tree)))]
    ))
(define (seec-append tree1 tree2)
  #;(-> seec-list? seec-list? seec-list?)
  (cond
    [(seec-empty? tree1) tree2]
    [else (seec-cons (seec-head tree1)
                     (seec-append (seec-tail tree1) tree2))]
    ))


;;;;;;;;;;;;;;;;;;;;;;;
;; Solver interfaces ;;
;;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;;
;; Terminal symbols ;;
;;;;;;;;;;;;;;;;;;;;;;

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


;;;;;;;;;;;;;;;;;;;;;
;; Pretty printing ;;
;;;;;;;;;;;;;;;;;;;;;


(define (bonsai-display b out)
  (cond
    [(bonsai-terminal? b)
     (out (enum->symbol (bonsai-terminal-value b)))]
    [(bonsai-null? b)
     (out "*null*")]
    [(bonsai-list? b)
     (out "(")
     (let ([nodes (filter (lambda (n) (not (bonsai-null? n))) (bonsai-list-nodes b))])
       (unless (empty? nodes)
         (out (first nodes))
         (map (λ (n) (out " ") (out n)) (rest nodes))))
     (out ")")]
    [else (out b)]
    ))

(define (bonsai-print b out recur)
  (cond
    [(bonsai-terminal? b)
     (out "(bonsai-terminal ")
     (recur (enum->symbol (bonsai-terminal-value b)))
     (out ")")]
    [(bonsai-null? b)
     (out "(bonsai-null)")]
    [(bonsai-list? b)
     (out "(bonsai-list (list ")
     (let ([nodes (bonsai-list-nodes b)])
       (unless (empty? nodes)
         (recur (first nodes))
         (map (λ (n) (out " ") (recur n)) (rest nodes))))
     (out "))")]
    [else (recur b)]
    ))


;;;;;;;;;;;
;; Tests ;;
;;;;;;;;;;;

(module* test rosette/safe
  (require rackunit)
  (require (submod ".."))
  (require seec/private/match)
  (require "string.rkt")
  (require racket/contract)

  (define null (bonsai-null))
  (define term (bonsai-terminal (bv 2 32)))
  (define bool #t)
  (define bv+  (integer->bv 4))
  (define int  5)
  (define chr  (char #\c))
  (define str  (string "hello"))
  (define blst (bonsai-list (list term null)))

  (test-case
      "Predicate matches"
    (check-equal? null (match null [(? bonsai-null? x) x]))
    (check-equal? term (match term [(? bonsai-terminal? x) x]))
    (check-equal? bool (match bool [(? (and/c bonsai? boolean?) x) x]))
    (check-equal? bv+  (match bv+  [(? (and/c bonsai? bv?) x) x]))
    (check-equal? int  (match int  [(? (and/c bonsai? integer?) x) x]))
    (check-equal? chr  (match chr  [(? (and/c bonsai? char?) x) x]))
    (check-equal? str  (match str  [(? (and/c bonsai? string?) x) x]))
    (check-equal? blst (match blst [(? bonsai-list? x) x]))
    )

  (define ll (list->seec (list str bool)))
  (test-case
      "linked list"
    (check-equal? #t (seec-list? ll))
    (check-equal? 2 (seec-length ll))
    )

  (test-case
    "Match expanders"
  (check-equal? #t
                (match null
                  [(bonsai-null) #t]
                  [_ #f]))
  (check-equal? (bonsai-terminal-value term)
                (match term
                  [(bonsai-terminal v) v]))
  )


  (define test0 (bonsai-null))
  (define test1 (seec-cons #t test0))
  (define test2 (seec-cons (string "hi") test1))
  (test-case "seec-list operations"

    (check-equal? (seec-list? test2)
                  #t
                  "seec-list? failure")

    (check-equal? (seec-list-of? boolean? test1)
                  #t
                  "seec-list-of? failure")

    (check-equal? (seec-list-of? boolean? test2)
                  #f
                  "seec-list-of? failure")

    (check-equal? test2
                  (list->seec (list (string "hi") #t))
                  "list->seec failure")

    (check-equal? (seec->list test2)
                  (list (string "hi") #t)
                  "seec->list failure")

    (check-equal? (seec-append test2 test2)
                  (list->seec (list (string "hi") #t (string "hi") #t))
                  "seec-append failure")

    (check-equal? (seec-length test2)
                  2
                  "seec-length failure")
    )


)

