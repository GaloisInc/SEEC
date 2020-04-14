#lang rosette/safe

(provide (struct-out bonsai)
         (struct-out bonsai-null)
         (struct-out bonsai-terminal)
         (struct-out bonsai-boolean)
         (struct-out bonsai-integer)
         (struct-out bonsai-string+)
         bonsai-string?
         bonsai-string-value
         (struct-out bonsai-char+)
         bonsai-char?
         bonsai-char-value
         (struct-out bonsai-list)
         bonsai-depth
         bonsai-leaves
         enum->symbol
         symbol->enum
         register-enum
         make-tree!
         nondet!
         capture-nondeterminism
         concretize
         instantiate)

(require (for-syntax syntax/parse)
         (only-in racket/base
                  make-parameter
                  parameterize
                  values))
(require "string.rkt")

(define bonsai-width 32)

(define (bonsai-write b port mode)
  (case mode
    [(#f) (bonsai-display b (λ (v) (display v port)))]
    [(#t) (bonsai-print b (λ (v) (display v port)))]
    [else (bonsai-print b (λ (v) (display v port)))]))

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
(struct bonsai-char+ bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)]
  )
(define bonsai-char? bonsai-char+?)
(define bonsai-char-value bonsai-char+-value)
(struct bonsai-string+ bonsai (value)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc bonsai-write)]
  )
(define bonsai-string? bonsai-string+?)
(define bonsai-string-value bonsai-string+-value)
(struct bonsai-boolean bonsai (value)
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
    [(bonsai-null? b)
     (out "*null*")]
    [(bonsai-list? b)
     (out "(")
     (let ([nodes (bonsai-list-nodes b)])
       (unless (empty? nodes)
         (out (first nodes))
         (map (λ (n) (out " ") (out n)) (rest nodes))))
     (out ")")]))

(define (bonsai-print b out)
  (cond
    [(bonsai-terminal? b)
     (out "(bonsai-terminal (")
     (out (bonsai-terminal-value b))
     (out "))")]
    [(bonsai-integer? b)
     (out "(bonsai-integer (")
     (out (bonsai-integer-value b))
     (out "))")]
    [(bonsai-char? b)
     (out "(bonsai-char (")
     (out (print-char (bonsai-char-value b)))
     (out "))")]
    [(bonsai-string? b)
     (out "(bonsai-string (")
     (out (print-string (bonsai-string-value b)))
     (out "))")]
    [(bonsai-boolean? b)
     (out "(bonsai-boolean (")
     (out (bonsai-boolean-value b))
     (out "))")]
    [(bonsai-null? b)
     (out "(bonsai-null)")]
    [(bonsai-list? b)
     (out "(bonsai-list (")
     (map out (add-between (bonsai-list-nodes b) " "))
     (out "))")]))

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

(define (havoc!)
  (define-symbolic* havoc boolean?)
  havoc)

(define (new-boolean!)
  (define-symbolic* bool-val boolean?)
  (bonsai-boolean bool-val))

(define (new-integer!)
  (define-symbolic* int-val integer?)
  (bonsai-integer int-val))

; we do not provide new-string! because strings are not primitive types

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
    [(havoc!) (new-natural!)]
    [else *null*]))

(define (concretize v sol)
  (evaluate v (complete-solution sol (symbolics v))))

(define (instantiate v)
  (let ([sol (solve v)])
    (if (unsat? sol)
        sol
        (concretize v sol))))
