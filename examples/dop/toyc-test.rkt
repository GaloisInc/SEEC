#lang seec
(require "toyc.rkt")

(module+ test (require rackunit
                       rackunit/text-ui))

(module+ test
  (define seec-utils-tests (test-suite "seec-utils"

    (test-suite "seec-ith"
                (check-equal? (seec-ith 2 (list->seec (list 100 101 102)))
                              102)
                (check-equal? (seec-ith 0 (list->seec (list 100 101 102)))
                              100)
                (check-equal? (seec-ith 3 (list->seec (list 100 101 102)))
                              #f)
                (check-equal? (seec-ith -1 (list->seec (list 100 101 102)))
                              #f)
                )

    (test-suite "seec-set-ith"
                (check-equal? (seec-set-ith 2 202 (list->seec (list 100 101 102)))
                              (list->seec (list 100 101 202)))
                )

    (test-suite "seec-build-list"
                (check-equal? (seec-build-list 3 #f)
                              (list->seec (list #f #f #f)))
                )
    ))
  (run-tests seec-utils-tests)


  (define mem-example (list->seec (list (toyc (100 0))
                                        (toyc (101 1))
                                        (toyc (102 2))
                                        )))
  (define (mk-loc x o) (toyc (,x ,o)))


  (define mem-tests
    (test-suite "mem tests"
       (test-suite "lookup-mem"
                (check-equal? (lookup-mem-mapping 100 mem-example)
                              0)
                (check-equal? (lookup-mem (toyc (102 0)) mem-example)
                              2)
                (check-equal? (lookup-mem (toyc (102 2)) mem-example)
                              #f)
                )

       (test-suite "update-object-at-offset"
                   (check-equal? (update-object-at-offset 2 0 20)
                                 20))
       (test-suite "store-mem"
                   ; l does occur in m
                   (check-equal? (store-mem (mk-loc 100 0) 20 mem-example)
                                 (list->seec (list (toyc (100 20))
                                                   (toyc (101 1))
                                                   (toyc (102 2)))))
                   ; l doesn't occur in m
                   (check-equal? (store-mem (mk-loc 103 0) 20 mem-example)
                                 #f)
                   )
       ))
  (run-tests mem-tests)
  )
