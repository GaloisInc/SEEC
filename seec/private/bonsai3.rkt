#lang rosette/safe

; A version of bonsai that doesn't use structs

(require (for-syntax syntax/parse)
         (only-in racket/base
                  make-parameter
                  parameterize
                  write-string
                  values))
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
         (rename-out [match-bonsai-null bonsai-null]
                     [match-bonsai-terminal bonsai-terminal]
                     )

         bonsai-depth
         bonsai-leaves
         bonsai->racket
         make-tree!

         ; nondeterminism
         nondet!
         capture-nondeterminism

         ; bitvectors
         integer->bv
         set-bitwidth

         ; seec-lists
         seec-list?
         seec-list-of?
         seec-cons
         seec-singleton
         list->seec
         seec->list
         seec-length
         seec-append

         ; solver interfaces
         concretize
         instantiate
         concretize+
         expand-solution

         ; utilities
         enum->symbol
         symbol->enum
         register-enum
         )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bonsai data structures ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (bonsai-write b port mode)
  (case mode
    [(#f) (bonsai-display b (λ (v) (display v port)))]
    [(#t) (bonsai-print b (λ (v) (display v port)) (lambda (v) (write v port)))]
    [else (bonsai-print b (λ (v) (display v port)) (lambda (v) (print v port)))]))

(struct bonsai-terminal (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])
(struct bonsai-null ()
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)])

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
      (and (list? b)
           (andmap bonsai? b))
      ))

(define (bonsai-depth b)
  (cond
    [(list? b)
     (let ([children (map bonsai-depth b)])
       (+ 1 (apply max children)))]
    [(bonsai-null? b) 0]
    [else 1]))

; Count the number of leaves in a bonsai tree
(define (bonsai-leaves b)
  (cond
    [(list? b) (foldl + 0 (map bonsai-leaves b))]
    [(bonsai-null? b) 0]
    [else 1]
    ))

(define (bonsai->racket b)
  (cond
    [(bonsai-null? b) #f]
    [(bonsai-terminal? b) (enum->symbol (bonsai-terminal-value b))]
    [(list? b)
     (map bonsai->racket (filter (λ (b) (not (bonsai-null? b)))
                                 b))]
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
    [(_ body ...)
     #'(parameterize ([nondeterminism (list)])
         (define result
           body ...)
         (values result (nondeterminism)))]))

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
  (define char-val (new-symbolic-char))
  char-val)

(define (new-string! max-length)
  (assert (>= max-length 0))
  (if (havoc!)
      (new-symbolic-string max-length)
      (new-string! (- max-length 1))))

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
; positive integers
(define (make-tree! depth width)
  (cond
    [(havoc!) (make-list width (λ () (make-tree! (- depth 1) width)))]
    [(havoc!) (new-term!)]
    [(havoc!) (new-integer!)]
    [(havoc!) (new-natural!)]
    [(havoc!) (new-boolean!)]
    [(havoc!) (new-bv!)]
    [(havoc!) (new-char!)]
    [(havoc!) (new-string! depth)]
    [else     (bonsai-null)]
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


(define (bonsai-head tree)
  (first tree))
(define (bonsai-tail tree)
  (second tree))

; The given tree a seec-list/bonsai-linked-list of the shape
; (list<ty> ::= nil (x:ty l:list<ty>))
; that is, it is a bonsai tree that is either null, or has the shape
; (x xs y1 .. yn)
; where:
;   - x matches the pattern a 
;   - xs matches the pattern as
;   - each yi is null
(define (bonsai-cons-match? syntax-match-a? syntax-match-as? tree)
  (and (list? tree)
       (andmap-indexed
        (λ (i tree-i) (cond
                        [(= i 0) (syntax-match-a? tree-i)]
                        [(= i 1) (syntax-match-as? tree-i)]
                        [else (bonsai-null? tree-i)]))
        tree)))
(define (bonsai-linked-list-match? syntax-match-lang? a tree)
  (or (bonsai-null? tree)
      (bonsai-cons-match? (curry syntax-match-lang? a)
                          (curry bonsai-linked-list-match? syntax-match-lang? a)
                          tree)))

(define (bonsai-cons? tree)
  (bonsai-cons-match? bonsai? (λ (x) (bonsai? x)) tree))
(define (seec-list? tree)
  (or (bonsai-null? tree)
      (and (bonsai-cons? tree)
           (seec-list? (bonsai-tail tree)))))


(define/contract (seec-cons x xs)
  (-> bonsai? seec-list? seec-list?)
  (list x xs))
(define/contract (seec-singleton x)
  (-> bonsai? seec-list?)
  (seec-cons x (bonsai-null)))
(define/contract (list->seec l)
  (-> (listof bonsai?) seec-list?)
  (cond
    [(empty? l) (bonsai-null)]
    [else (seec-cons (first l) (list->seec (rest l)))]
    ))
(define/contract (seec->list l)
  (-> seec-list? (listof bonsai?))
  (cond
    [(bonsai-null? l) (list )]
    [(bonsai-cons? l)
     (cons (bonsai-head l) (seec->list (bonsai-tail l)))]
    ))

(define (seec-list-of? tp? tree)
  (cond
    [(bonsai-null? tree) #t]
    [(bonsai-cons? tree)
     (and (tp? (bonsai-head tree))
          (seec-list-of? tp? (bonsai-tail tree)))]
    ))

(define (seec-length tree)
  (cond
    [(bonsai-null? tree) 0]
    [(bonsai-cons? tree)
     (+ 1 (seec-length (bonsai-tail tree)))]
    ))
(define (seec-append tree1 tree2)
  (cond
    [(bonsai-null? tree1) tree2]
    [(bonsai-cons? tree1)
     (seec-cons (bonsai-head tree1)
                (seec-append (bonsai-tail tree1) tree2))]
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
    [(integer? b)       (out b)]
    [(boolean? b)       (out b)]
    [(bv? b)            (out b)]
    [(list? b)          (out "(")
                        (let ([nodes (filter (lambda (n) (not (bonsai-null? n))) b)])
                          (unless (empty? nodes)
                            (bonsai-display (first nodes) out)
                            (map (λ (n) (out " ") (bonsai-display n out)) (rest nodes))))
                        (out ")")]
    [(char? b)   (out b)]
    [(string? b) (out b)]
    ))

(define (bonsai-print b out recur)
  (cond
    [(bonsai-terminal? b)
     (out "(bonsai-terminal ")
     (recur (bonsai-terminal-value b))
     (out ")")]
    [(bonsai-null? b)
     (out "(bonsai-null)")]
    [(list? b)
     (out "(list ")
     (unless (empty? b)
       (recur (first b))
       (map (λ (n) (out " ") (recur n)) (rest b)))
     (out ")")]
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
  (define blst (list term null))

  (test-case
      "Predicate matches"
    (check-equal? null (match null [(? bonsai-null? x) x]))
    (check-equal? term (match term [(? bonsai-terminal? x) x]))
    (check-equal? bool (match bool [(? (and/c bonsai? boolean?) x) x]))
    (check-equal? bv+  (match bv+  [(? (and/c bonsai? bv?) x) x]))
    (check-equal? int  (match int  [(? (and/c bonsai? integer?) x) x]))
    (check-equal? chr  (match chr  [(? (and/c bonsai? char?) x) x]))
    (check-equal? str  (match str  [(? (and/c bonsai? string?) x) x]))
    (check-equal? blst (match blst [(? (and/c bonsai? list?) x) x]))
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

