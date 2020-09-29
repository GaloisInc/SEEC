#lang seec

(require rackunit)
(require rackunit/text-ui)
(require (prefix-in set:
                    (combine-in
                     (file "set/set.rkt")
                     (file "set/query.rkt"))))
(require (prefix-in linked-list:
                    (combine-in
                     (file "list/query.rkt")
                     (file "list/alist-lang.rkt"))))

(require (prefix-in simp+nat:
                    (file "unit/simp+natural.rkt")))

(require (prefix-in printf:
                    (combine-in
                     (file "printf/unit-tests.rkt")
                     (file "printf/framework.rkt")
                     )))

;; Test suites
; unit tests
;; define-language
;; base types
;;; integer
;;; natural
;;; char
;;; string
;;; #:size at language
;;; #:where at language
;; refine-languagr
;; define-compiler
;; queries
;;; find-changed-behavior
;;; find-changed-component
;;; find-weird-behavior
;;; find-weird-component
;;; #:count at query
;;; #:size at query
;;; #:where at query

(define find-changed-component-tests
  (test-suite "find-changed-component"
               (test-case "testing query"
                   (apply check-pred simp+nat:test-cc-nat-to-integer))
               (test-case "testing arguments to query"
                 (apply check-pred simp+nat:test-cc-arg-count-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-source-exp-bound-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-source-exp-where-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-source-context-bound-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-source-context-where-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-target-context-bound-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-target-context-where-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-source-behavior-where-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-arg-target-behavior-where-nat-to-integer)
                 (apply check-pred simp+nat:test-cc-all-args-nat-to-integer))))

(define find-weird-component-tests
  (test-suite "find-weird-component"
               (test-case "testing query"
                   (apply check-pred simp+nat:test-wc-nat-to-integer))
               (test-case "testing arguments to query"
                 (apply check-pred simp+nat:test-wc-arg-count-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-source-exp-bound-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-source-exp-where-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-source-context-bound-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-source-context-where-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-target-context-bound-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-target-context-where-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-target-context-where-fail-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-source-behavior-where-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-arg-target-behavior-where-nat-to-integer)
                 (apply check-pred simp+nat:test-wc-all-args-nat-to-integer))))

; n-to-z


; set
(define set-tests
  (test-suite "Set"
              (test-case "find-changed-component, testing #:count argument"
                  (check-pred (lambda (l) (equal? (length l) 3)) (set:ex1) "Expected 3 witnesses returned"))
              (test-case "find-weird-component, testing -bound arguments"
                  (check-not-false (set:ex2) "Behaviors can be introduced by buggy concrete implementation")
                  (check-false (set:ex3) "Behaviors should be preserved through abstract->concrete compilation"))
              (test-case "find-gadget"                 
                  (check-pred (lambda (lw)
                                (let* ([uw (unpack-language-witness (first lw))]
                                       [prog (third uw)]
                                       [res (fourth uw)])
                                  (set:add1-concrete? prog res))) (set:ex4) "Returned gadget should respect provided predicate"))))

; linked list
(define ll-tests 
  (test-suite "Linked and association lists"
              (test-case "Working compiler"
                (check-false (linked-list:ex1) "Behaviors should be preserved through alist->ll compilation"))
              (test-case "Attacked compiler (free-pointer modification)"
                (check-not-false (linked-list:ex2) "Behaviors can be introduced by changing the free pointer")
                (let* ([ll3 (linked-list:ex3)]
                       [ll3-s (unpack-language-witness (first ll3))]
                       [ll3-t (unpack-language-witness (second ll3))])
                  (check-pred (lambda (v) (linked-list:alist-in (first ll3-s) v)) (fourth ll3-t) "Behaviors found respect the predicates provided at query")))))

; printf
; (currently only unit tests, not query testing)

(define printf-unit-tests-safe-correct
  printf:safe-correct)
(define printf-unit-tests-unsafe-correct
  printf:unsafe-correct)
(define printf-unit-tests-safe-unsafe-consistent
  printf:safe-unsafe-consistent)
