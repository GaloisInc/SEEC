#lang seec
(require "toyc.rkt")

(module+ test (require rackunit
                       rackunit/text-ui
                       racket/contract
                       ))

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
                                        (toyc (103 (102 0)))
                                        )))


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
                   (check-equal? (store-mem (lid->loc 100) 20 mem-example)
                                 (list->seec (list (toyc (100 20))
                                                   (toyc (101 1))
                                                   (toyc (102 2))
                                                   (toyc (103 (102 0)))
                                                   )))
                   ; l doesn't occur in m
                   (check-equal? (store-mem (lid->loc 104) 20 mem-example)
                                 #f)
                   )
       ))
  (run-tests mem-tests)

  (define/contract F-example toyc-frame?
    (list->seec (list (toyc ((VAR 0) (100 0)))
                      (toyc ((VAR 1) (103 0))))))
  (define F2-example
    (list->seec (list (toyc ((VAR 2) (100 0)))
                      (toyc ((VAR 1) (101 0))))))

  (define/contract S-example toyc-stack?
    (seec-singleton F2-example))
  (define context-example (toyc ((,F-example ,S-example) ,mem-example)))
  (define state-example (init-state context-example))


  (define eval-tests
    (test-suite "eval-tests"
       (test-suite "eval-binop"

                   (check-equal? (eval-binop (toyc *) 3 4)
                                 12)

                   ; pointer arithmetic
                   (check-equal? (eval-binop (toyc +)
                                             (toyc (100 0))
                                             42)
                                 (toyc (100 42)))
                   ; failing pointer arithmetic
                   (check-equal? (eval-binop (toyc +)
                                             42
                                             (toyc (100 0)))
                                 #f)
                   )
       (test-suite
        "eval-expr"
        ; F contains Var 0 ↦ (100 0)
        ; m contains 100   ↦ 0
        (test-case "Var"
          (check-equal? (eval-expr (toyc (VAR 0)) F-example mem-example)
                        0))

        ; F contains Var 1 ↦ 103
        ; m contains 103   ↦ (102 0)
        ;            102   ↦ 2
        (test-case "*"
          (check-equal? (eval-expr (toyc (* (VAR 1))) F-example mem-example)
                        2))

        ; F contains Var 1 ↦ (103,0)
        (test-case "&"
          (check-equal? (eval-expr (toyc (& (VAR 1))) F-example mem-example)
                        (toyc (103 0))))

        (test-case "op"
          ; Check that multiplication can be distinguished from unary * operation
          (check-equal? (eval-expr (toyc (* (VAR 0) (VAR 0))) F-example mem-example)
                        0)
          ; Var 1 ↦ (100,0)
          (check-equal? (eval-expr (toyc (+ (& (VAR 0)) 3)) F-example mem-example)
                        (toyc (100,3)))
          )
        )
       (test-suite "eval-exprs"
          (check-equal? (eval-exprs (list (toyc (* (VAR 1)))
                                          (toyc (& (VAR 1))))
                                    context-example
                                    )
                        (list (toyc 2)
                              (toyc (103 0)))))
       ))
  (run-tests eval-tests)

  (define/contract (make-declaration name params locals statements)
    (-> string? (listof toyc-param-decl?)
                (listof toyc-local-decl?)
                (listof toyc-statement?)
                toyc-declaration?)
    (toyc (,name ,(list->seec params) ,(list->seec locals) ,(list->seec statements))))
  (define main-example (make-declaration (string "main")
                                         (list (toyc ((VAR 0) int)))
                                         (list (toyc ((VAR 1) (* int))))
                                         (list (toyc (ASSIGN (VAR 1) (& (VAR 0)))))))
  (define g-example (seec-singleton main-example))

  (define/contract (check-lookup-context? ctx l obj)
    (-> toyc-context? toyc-loc? toyc-object? void?)
    (check-equal? (lookup-mem l (context->memory ctx))
                  obj))


  (define step-tests (test-suite "step-tests"

     (test-suite "set-lval"
        (check-lookup-context? (set-lval (toyc (100 0)) -1 context-example)
                               (toyc (100 0))
                               -1))

     (test-suite "pop-stack"
        (test-case "drop-loc-ident"
          (check-equal? (drop-loc-ident 100 mem-example)
                        (list->seec (list (toyc (101 1))
                                          (toyc (102 2))
                                          (toyc (103 (102 0)))
                                          ))))


        (test-case "pop-stack"
          (check-equal? (pop-stack F-example mem-example)
                        (list->seec (list (toyc (101 1))
                                          (toyc (102 2))
                                          ))))
        )

    (test-suite "alloc"

       (test-suite "fresh-var"
          (let* ([x-st+ (fresh-var state-example)]
                 [x     (car x-st+)]
                 [st+   (cdr x-st+)])
            (check-equal? (state-fresh-var st+)
                          (+ 1 (state-fresh-var state-example)))
            ))

       (test-case "alloc+int"
         (let* ([x-st+ (alloc 40 state-example)]
                [st+   (cdr x-st+)]
                [l     (lid->loc (car x-st+))]
                [l-st++ (alloc-object (toyc int) 40 state-example)]
                )
           (check-equal? (lookup-mem l (context->memory (state->context state-example)))
                         #f)
           (check-lookup-context? (state->context st+)
                                  l
                                  40)
           (check-equal? l (car l-st++))
           (check-equal? st+ (cdr l-st++))
           ))
       ; TODO: add alloc+array test case


        (test-case "alloc-declarations"
          (let* ([F-st+ (alloc-declarations (list (list (toyc (VAR 4)) (toyc int) 40))
                                            state-example)]
                 [F+    (car F-st+)]
                 [st+   (cdr F-st+)]
                 [the-new-x (- (state-fresh-var st+) 1)]
                 [the-new-l (lid->loc the-new-x)]
                 )
            (check-lookup-context? (state->context st+)
                                   the-new-l
                                   40)
            ))

        (test-case "alloc-frame"
          (let* ([st+ (alloc-frame main-example (list 1) state-example)]
                 [ctx+ (state->context st+)]
                 [F+   (context->top-frame ctx+)]
                 [m+   (context->memory ctx+)]
                 )

            (check-equal? (rest (context->non-empty-stack (state->context st+)))
                          (context->non-empty-stack (state->context state-example)))

            (check-equal? (eval-expr (toyc (VAR 0)) F+ m+)
                          1)
            (check-equal? (eval-expr (toyc (VAR 1)) F+ m+)
                          #f) ; Should evaluate to undef

            ))
        )


     (test-suite "eval-statement-1"
        (test-suite "ASSIGN"
          ; VAR 0 ↦ (100,0)
          (let ([st+ (eval-statement-1 g-example
                                       (update-state state-example
                                                     #:statement (toyc (ASSIGN (VAR 0) -1))
                                                     ))])
            (check-lookup-context? (state->context st+)
                                   (toyc (100 0))
                                   -1)
            (check-equal? (context->non-empty-stack (state->context st+))
                          (context->non-empty-stack (state->context state-example)))

            (check-equal? (state->statement st+) (toyc SKIP))

            (check-equal? (state->trace st+) (toyc nil))
            ))

        (test-suite "OUTPUT"
           (let ([st+ (eval-statement-1 g-example
                                        (update-state state-example
                                                      #:statement (toyc (OUTPUT (VAR 0)))
                                                      ))])
             (check-equal? (state->trace st+) (seec-singleton 0))
             (check-equal? (state->statement st+) (toyc SKIP))
             (check-equal? (state->context st+) (state->context state-example))
             ))

        (test-suite "CALL"
           (let ([st+ (eval-statement-1 g-example
                                        (update-state state-example
                                                      #:statement (toyc (CALL "main"
                                                                              (cons 3 nil)))
                                                      ))])
             (test-case "stack"
               (check-equal? (rest (context->non-empty-stack (state->context st+)))
                           (list F-example F2-example)))
             ; Other cases are tested by alloc-frame above
             ))

        (test-suite "RETURN"
           (let ([st+ (eval-statement-1 g-example
                                        (update-state state-example
                                                      #:statement (toyc RETURN))
                                        )])
             (check-equal? (state->trace st+) (toyc nil))
             (check-equal? (context->non-empty-stack (state->context st+))
                           (list F2-example))
             (check-equal? (context->memory (state->context st+))
                           (list->seec (list (toyc (101 1))
                                             (toyc (102 2))
                                             )))
             ))

        (test-suite "SEQ-SKIP"
           (let ([st+ (eval-statement-1 g-example
                                        (update-state state-example
                                                      #:statement (toyc (SEQ SKIP RETURN))
                                                      ))])
             (check-equal? (state->statement st+) (toyc RETURN))
             (check-equal? (state->context st+)   (state->context state-example))
             ))

        (test-suite "SEQ"
           (let* ([stmt0 (toyc (ASSIGN (VAR 1) (VAR 0)))]
                  [st0   (eval-statement-1 g-example
                                           (update-state state-example
                                                         #:statement stmt0))]
                  [st+   (eval-statement-1 g-example
                                           (update-state state-example
                                                         #:statement (toyc (SEQ ,stmt0 RETURN))))]
                  )
             (check-equal? (state->statement st+)
                           (toyc (SEQ ,(state->statement st0) RETURN)))
             (check-equal? (state->context st+)
                           (state->context st0))
             ))


        )

     ))
  (run-tests step-tests)

  (define (evaluation-tests)


    (define n (toyc (VAR 0)))
    (define o (toyc (VAR 1)))
    (define prev (toyc (VAR 2)))
    (define i (toyc (VAR 3)))
    (define result (toyc (VAR 4)))

    (define fac (make-declaration
                 (string "fac")
                 (list (toyc (,n int))
                       (toyc (,o (* int)))
                       )
                 (list (toyc (,prev int)))
                 (list (toyc (IF (= ,n 0)
                                 (ASSIGN (* ,o) 1)
                                 (SEQ (CALL "fac" (cons (- ,n 1)
                                                        (cons (& ,prev) nil)))
                                      (ASSIGN (* ,o) (* ,n ,prev))
                                      ))))
                 ))
    (define main (make-declaration
                  (string "main")
                  (list (toyc (,n int)))
                  (list (toyc (,result int)))
                  (list (toyc (CALL "fac" (cons ,i
                                          (cons (& ,result)
                                          nil))))
                        (toyc (OUTPUT ,result))
                        )))

    (define run-fac (run (list main fac)
                         (list 3)))
    (displayln run-fac)
    #;(display-state run-fac)
    (printf "hi~n")
    )
  (evaluation-tests)
  )
