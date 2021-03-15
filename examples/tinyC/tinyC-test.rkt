#lang seec

(require seec/private/util)
(require seec/private/monad)
(require "tinyC.rkt")

(provide factorial
         assign-output-example
         assign-output-decl
         simple-call-example
         password-checker
         password-checker-with-arg
         )

(module+ test (require rackunit
                       rackunit/text-ui
                       racket/contract
                       ))

(define/contract (make-declaration name params locals statements)
    (-> string? (listof tinyC-param-decl?)
                (listof tinyC-local-decl?)
                (listof tinyC-statement?)
                tinyC-declaration?)
    (tinyC (,name ,(list->seec params) ,(list->seec locals) ,(list->seec statements))))


;;;;;;;;;;;;;;;;;;;
; Simple programs ;
;;;;;;;;;;;;;;;;;;;

(define assign-output-decl (make-declaration (string "main")
                                         (list (tinyC ("x0" int)))
                                         (list (tinyC ("x1" (* int))))
                                         (list (tinyC (ASSIGN "x1" (& "x0")))
                                               (tinyC (OUTPUT "x1"))
                                               )))
(define assign-output-example (list assign-output-decl))


;;

(define simple-call-example
  (list (make-declaration (string "main")
                          (list (tinyC ("x" int)))
                          (list )
                          (list (tinyC (CALL "foo" (cons "x" nil)))))
        (make-declaration (string "foo")
                          (list (tinyC ("y" int)))
                          (list )
                          (list (tinyC (OUTPUT "y"))))
        ))

#;(parameterize ([debug? #f])
  (tinyC:display-program (list->seec simple-call-example)))


;;;;;;;;;;;;;
; Factorial ;
;;;;;;;;;;;;;

(define fac (make-declaration
                 (string "fac")
                 (list (tinyC ("n" int))
                       (tinyC ("o" (* int)))
                       )
                 (list (tinyC ("prev" int)))
                 (list (tinyC (IF (= "n" 0)
                                 (ASSIGN (* "o") 1)
                                 (SEQ (CALL "fac" (cons (- "n" 1)
                                                        (cons (& "prev") nil)))
                                      (ASSIGN (* "o") (* "n" "prev"))
                                      ))))
                 ))
(define fac-main (make-declaration
                  (string "main")
                  (list (tinyC ("i" int)))
                  (list (tinyC ("result" int)))
                  (list (tinyC (CALL "fac" (cons "i"
                                          (cons (& "result")
                                          nil))))
                        (tinyC (OUTPUT "result"))
                        )))

(define factorial (list fac-main fac))

;;;;;;;;
; Loop ;
;;;;;;;;

    (define loop (make-declaration
                  (string "main")
                  (list )
                  (list (tinyC ("i"   int))
                        (tinyC ("p"   (array int 10)))
                        (tinyC ("c"   (* int)))
                        (tinyC ("sum" int))
                        )
                  (list (tinyC (ASSIGN "i" 0))
                        (tinyC (ASSIGN "c" "p"))
                        (tinyC (WHILE (< "i" 10)
                                     (SEQ (ASSIGN (* "c") 2)
                                     (SEQ (ASSIGN "c" (+ "c" 1))
                                          (ASSIGN "i" (+ "i" 1))
                                          ))))
                        (tinyC (ASSIGN "i" 0))
                        (tinyC (ASSIGN "sum" 0))
                        (tinyC (WHILE (< "i" 10)
                                     (SEQ (ASSIGN "sum" (+ "sum" (* (+ "p" "i"))))
                                          (ASSIGN "i"   (+ "i" 1))
                                          )))
                        (tinyC (OUTPUT "sum")))
                  ))


    (define run-loop
      (parameterize ([max-fuel 200])
        (tinyC:run (list loop)
                   (list )
                   (list ))))

;;;;;;;;;
; INPUT ;
;;;;;;;;;

#|
void main() {
  int password=42;
  int* input-buffer;
  bool auth = false;

  INPUT(input-buffer);
  if (*input-buffer = *password) {
    auth = true;
  }
  guarded_fun(auth);
}

void guarded_fun(int auth) {
  OUTPUT(auth);
  ... other stuff
}
|#
(define password-checker-main
  (make-declaration (string "main")
                    (list) ; No input to main
                    (list (tinyC ("candidate" int)) ; If 'candidate' is first in
                                                    ; the list, we can overwrite
                                                    ; the variables that come after.
                          (tinyC ("password" int))
                          (tinyC ("auth" int))
                          )
                    (list (tinyC (ASSIGN "auth" 0))
                          (tinyC (ASSIGN "password" 42))
                          (tinyC (INPUT (& "candidate")))
                          (tinyC (IF (= "candidate" "password")
                                     (ASSIGN "auth" 1)
                                     SKIP))
                          (tinyC (CALL "guarded-fun"
                                       (cons "auth" nil)))
                          )))
(define password-checker-body
  (make-declaration (string "guarded-fun")
                    (list (tinyC ("auth" int)))
                    (list )
                    (list (tinyC (OUTPUT "auth"))) ; ...
                    ))

(define password-checker (list password-checker-main
                               password-checker-body))

(define password-checker-main-with-arg
  (make-declaration (string "main")
                    (list (tinyC ("password" int))) ; The password is an input to main, instead of being hard-coded
                    (list (tinyC ("candidate" int)) ; If 'candidate' is first in
                                                    ; the list, we can overwrite
                                                    ; the variables that come after.
                          (tinyC ("auth" int))
                          )
                    (list (tinyC (ASSIGN "auth" 0))
                          (tinyC (INPUT (& "candidate")))
                          (tinyC (IF (= "candidate" "password")
                                     (ASSIGN "auth" 1)
                                     SKIP))
                          (tinyC (CALL "guarded-fun"
                                       (cons "auth" nil)))
                          )))

(define password-checker-with-arg (list password-checker-main-with-arg
                                        password-checker-body))



;;;;;;;;;;;;;;;;;
; Running tests ;
;;;;;;;;;;;;;;;;;


(module+ test
  (define seec-utils-tests (test-suite "seec-utils"

    (test-suite "seec-ith"
                (check-equal? (seec-ith 2 (list->seec (list 100 101 102)))
                              102)
                (check-equal? (seec-ith 0 (list->seec (list 100 101 102)))
                              100)
                (check-equal? (seec-ith 3 (list->seec (list 100 101 102)))
                              *fail*)
                (check-equal? (seec-ith -1 (list->seec (list 100 101 102)))
                              *fail*)
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
  (parameterize ([debug? #t])
    (run-tests seec-utils-tests))


  (define mem-example (list->seec (list (tinyC (100 0))
                                        (tinyC (101 1))
                                        (tinyC (102 2))
                                        (tinyC (103 (102 0)))
                                        )))


  (define mem-tests
    (test-suite "mem tests"
       (test-suite "lookup-mem"
                (check-equal? (tinyC:lookup-mem-mapping 100 mem-example)
                              0)
                (check-equal? (tinyC:lookup-mem (tinyC (102 0)) mem-example)
                              2)
                (check-equal? (tinyC:lookup-mem (tinyC (102 2)) mem-example)
                              *fail*)
                )

       (test-suite "update-object-at-offset"
                   (check-equal? (tinyC:update-object-at-offset 2 0 20)
                                 20))
       (test-suite "store-mem"
                   ; l does occur in m
                   (check-equal? (tinyC:store-mem (lid->loc 100) 20 mem-example)
                                 (list->seec (list (tinyC (100 20))
                                                   (tinyC (101 1))
                                                   (tinyC (102 2))
                                                   (tinyC (103 (102 0)))
                                                   )))
                   ; l doesn't occur in m
                   (check-equal? (tinyC:store-mem (lid->loc 104) 20 mem-example)
                                 *fail*)
                   )
       ))
  (run-tests mem-tests)

  (define/contract F-example tinyC-frame?
    (list->seec (list (tinyC ("x0" (100 0)))
                      (tinyC ("x1" (103 0))))))
  (define F2-example
    (list->seec (list (tinyC ("x2" (100 0)))
                      (tinyC ("x1" (101 0))))))

  (define/contract S-example tinyC-stack?
    (seec-singleton F2-example))
  (define context-example (tinyC ((,F-example ,S-example) ,mem-example)))
  (define state-example (tinyC:init-state context-example))


  (define eval-tests
    (test-suite "eval-tests"
       (test-suite "eval-binop"

                   (check-equal? (tinyC:eval-binop (tinyC *) 3 4)
                                 12)

                   ; pointer arithmetic
                   (check-equal? (tinyC:eval-binop (tinyC +)
                                                   (tinyC (100 0))
                                                   42)
                                 (tinyC (100 42)))
                   ; failing pointer arithmetic
                   (check-equal? (tinyC:eval-binop (tinyC +)
                                                   42
                                                   (tinyC (100 0)))
                                 *fail*)
                   )
       (test-suite
        "eval-expr"
        ; F contains Var 0 ↦ (100 0)
        ; m contains 100   ↦ 0
        (test-case "Var"
          (check-equal? (tinyC:eval-expr (tinyC "x0") F-example mem-example)
                        0))

        ; F contains Var 1 ↦ 103
        ; m contains 103   ↦ (102 0)
        ;            102   ↦ 2
        (test-case "*"
          (check-equal? (tinyC:eval-expr (tinyC (* "x1")) F-example mem-example)
                        2))

        ; F contains Var 1 ↦ (103,0)
        (test-case "&"
          (check-equal? (tinyC:eval-expr (tinyC (& "x1")) F-example mem-example)
                        (tinyC (103 0))))

        (test-case "op"
          ; Check that multiplication can be distinguished from unary * operation
          (check-equal? (tinyC:eval-expr (tinyC (* "x0" "x0")) F-example mem-example)
                        0)
          ; Var 1 ↦ (100,0)
          (check-equal? (tinyC:eval-expr (tinyC (+ (& "x0") 3)) F-example mem-example)
                        (tinyC (100,3)))
          )
        )
       (test-suite "eval-exprs"
          (check-equal? (tinyC:eval-exprs (list (tinyC (* "x1"))
                                          (tinyC (& "x1")))
                                    context-example
                                    )
                        (list (tinyC 2)
                              (tinyC (103 0)))))
       ))
  (run-tests eval-tests)


  (define/contract (check-lookup-context? ctx l obj)
    (-> tinyC-context? tinyC-loc? tinyC-object? void?)
    (check-equal? (tinyC:lookup-mem l (tinyC:context->memory ctx))
                  obj))


  (define step-tests (test-suite "step-tests"

     (test-suite "set-lval"
        (check-lookup-context? (tinyC:set-lval (tinyC (100 0)) -1 context-example)
                               (tinyC (100 0))
                               -1))

     (test-suite "pop-stack"
        (test-case "drop-loc-ident"
          (check-equal? (tinyC:drop-loc-ident 100 mem-example)
                        (list->seec (list (tinyC (101 1))
                                          (tinyC (102 2))
                                          (tinyC (103 (102 0)))
                                          ))))


        (test-case "pop-stack"
          (check-equal? (tinyC:pop-stack F-example mem-example)
                        (list->seec (list (tinyC (101 1))
                                          (tinyC (102 2))
                                          ))))
        )

    (test-suite "alloc"

       (test-suite "fresh-var"
          (let* ([x-st+ (tinyC:fresh-var state-example)]
                 [x     (car x-st+)]
                 [st+   (cdr x-st+)])
            (check-equal? (tinyC:state-fresh-var st+)
                          (+ 1 (tinyC:state-fresh-var state-example)))
            ))

       (test-case "alloc+int"
         (let* ([x-st+ (tinyC:alloc 40 state-example)]
                [st+   (cdr x-st+)]
                [l     (lid->loc (car x-st+))]
                [l-st++ (tinyC:alloc-object (tinyC int) 40 state-example)]
                )
           (check-equal? (tinyC:lookup-mem
                           l
                           (tinyC:context->memory (tinyC:state->context state-example)))
                         *fail*)
           (check-lookup-context? (tinyC:state->context st+)
                                  l
                                  40)
           (check-equal? l (car l-st++))
           (check-equal? st+ (cdr l-st++))
           ))
       ; TODO: add alloc+array test case


        (test-case "alloc-declarations"
          (let* ([F-st+ (tinyC:alloc-declarations (list (list (tinyC "x4") (tinyC int) 40))
                                                  state-example)]
                 [F+        (car F-st+)]
                 [st+       (cdr F-st+)]
                 [the-new-x (- (tinyC:state-fresh-var st+) 1)]
                 [the-new-l (lid->loc the-new-x)]
                 )
            (check-lookup-context? (tinyC:state->context st+)
                                   the-new-l
                                   40)
            ))

        (test-case "alloc-frame"
          (let* ([st+  (tinyC:alloc-frame assign-output-decl (list 1) state-example)]
                 [ctx+ (tinyC:state->context st+)]
                 [F+   (tinyC:context->top-frame ctx+)]
                 [m+   (tinyC:context->memory ctx+)]
                 )

            (check-equal? (rest (tinyC:context->non-empty-stack (tinyC:state->context st+)))
                          (tinyC:context->non-empty-stack (tinyC:state->context state-example)))

            (check-equal? (tinyC:eval-expr (tinyC "x0") F+ m+)
                          1)
            (check-equal? (tinyC:eval-expr (tinyC "x1") F+ m+)
                          *fail*) ; Should evaluate to undef

            ))
        )


     (test-suite "eval-statement-1"
        (test-suite "ASSIGN"
          ; x0 ↦ (100,0)
          (let ([st+ (tinyC:eval-statement-1
                        (list->seec assign-output-example)
                        (tinyC (ASSIGN "x0" -1))
                        (tinyC:update-state state-example
                                            #:statement (tinyC (ASSIGN "x0" -1))
                                                           ))])
            (check-lookup-context? (tinyC:state->context st+)
                                   (tinyC (100 0))
                                   -1)
            (check-equal?
             (tinyC:context->non-empty-stack (tinyC:state->context st+))
             (tinyC:context->non-empty-stack (tinyC:state->context state-example)))

            (check-equal? (tinyC:state->statement st+) (tinyC SKIP))

            (check-equal? (tinyC:state->trace st+) (tinyC nil))
            ))

        (test-suite "OUTPUT"
           (let ([st+ (tinyC:eval-statement-1 (list->seec assign-output-example)
                                              (tinyC (OUTPUT "x0"))
                        (tinyC:update-state state-example
                                            #:statement (tinyC (OUTPUT "x0"))
                                            ))])
             (check-equal? (tinyC:state->trace st+)     (seec-singleton 0))
             (check-equal? (tinyC:state->statement st+) (tinyC SKIP))
             (check-equal? (tinyC:state->context st+)   (tinyC:state->context state-example))
             ))

        (test-suite "CALL"
           (let ([st+ (tinyC:eval-statement-1 (list->seec assign-output-example)
                                              (tinyC (CALL "main" (cons 3 nil)))
                         (tinyC:update-state state-example
                                             #:statement (tinyC (CALL "main"
                                                                      (cons 3 nil)))
                                             ))])
             (test-case "stack"
               (check-equal? (rest (tinyC:context->non-empty-stack (tinyC:state->context st+)))
                             (list F-example F2-example)))
             ; Other cases are tested by alloc-frame above
             ))

        (test-suite "RETURN"
           (let ([st+ (tinyC:eval-statement-1 (list->seec assign-output-example)
                                              (tinyC RETURN)
                         (tinyC:update-state state-example
                                             #:statement (tinyC RETURN))
                         )])
             (check-equal? (tinyC:state->trace st+) (tinyC nil))
             (check-equal? (tinyC:context->non-empty-stack (tinyC:state->context st+))
                           (list F2-example))
             (check-equal? (tinyC:context->memory (tinyC:state->context st+))
                           (list->seec (list (tinyC (101 1))
                                             (tinyC (102 2))
                                             )))
             ))

        (test-suite "SEQ-SKIP"
           (let ([st+ (tinyC:eval-statement-1 (list->seec assign-output-example)
                                              (tinyC (SEQ SKIP RETURN))
                         (tinyC:update-state state-example
                                             #:statement (tinyC (SEQ SKIP RETURN))
                                             ))])
             (check-equal? (tinyC:state->statement st+) (tinyC RETURN))
             (check-equal? (tinyC:state->context st+)   (tinyC:state->context state-example))
             ))

        (test-suite "SEQ"
           (let* ([stmt0 (tinyC (ASSIGN "x1" "x0"))]
                  [st0   (tinyC:eval-statement-1 (list->seec assign-output-example)
                                                 stmt0
                            (tinyC:update-state state-example
                                                #:statement stmt0))]
                  [st+   (tinyC:eval-statement-1 (list->seec assign-output-example)
                                                 (tinyC (SEQ ,stmt0 RETURN))
                            (tinyC:update-state state-example
                                                #:statement (tinyC (SEQ ,stmt0 RETURN))))]
                  )
             (check-equal? (tinyC:state->statement st+)
                           (tinyC (SEQ ,(tinyC:state->statement st0) RETURN)))
             (check-equal? (tinyC:state->context st+)
                           (tinyC:state->context st0))
             ))


        )

     ))
  (run-tests step-tests)

  (define (evaluation-tests)

    (define run-fac (tinyC:run factorial
                               (list 3)
                               (list )))
    (check-equal? (tinyC:state->trace run-fac)
                  (seec-singleton 6))

    (check-equal? (tinyC:state->trace run-loop)
                  (seec-singleton 20))

    (define (run-password-checker guess)
      (tinyC:run password-checker
                 (list)
                 (list (seec-singleton guess))))

    (check-equal? (tinyC:state->trace (run-password-checker 42))
                  (seec-singleton 1))
    (check-equal? (tinyC:state->trace (run-password-checker 0))
                  (seec-singleton 0))

    (define/contract (run-password-checker-multiple guesses)
      (-> (listof integer?) any/c)
      (tinyC:run password-checker
                 (list)
                 (list (list->seec guesses))))

    ; In tinyC, only the first element matters
    (check-equal? (tinyC:state->trace (run-password-checker-multiple (list 42 32 1)))
                  (seec-singleton 1))
    (check-equal? (tinyC:state->trace (run-password-checker-multiple (list 33 25 0)))
                  (seec-singleton 0))


    ; Redo run-fac using language features
    (check-equal? ((language-evaluate tinyC-lang)
                   ((language-link tinyC-lang) (tinyC ((cons 3 nil)
                                                       nil))
                                               (list->seec factorial)))
                  (seec-singleton 6))

    (parameterize ([max-fuel 140])
      (check-equal? ((language-evaluate tinyC-lang)
                     ((language-link tinyC-lang) (tinyC (nil nil))
                                                 (seec-singleton loop)))
                    (seec-singleton 20)))


    )
  (evaluation-tests)
  )
