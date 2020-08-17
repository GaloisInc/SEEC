#lang seec

(require rackunit)
(require rackunit/text-ui)
(require (prefix-in set:
                    (file "set/set.rkt")))
(require (prefix-in linked-list:
                    (combine-in
                     (file "list/query.rkt")
                     (file "list/alist-lang.rkt"))))

;; Test suites
; n-to-z

; set
(define set-tests
  (test-suite "Set"
              (test-case "Working compiler"
                )
              (test-case "Buggy concrete language"
                )))

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
