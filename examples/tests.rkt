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

;; Test suites
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
