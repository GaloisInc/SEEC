#lang seec
(require seec/private/util)
(require seec/private/monad)
(require "tinyC.rkt"
         "tinyC-test.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt"
         "dispatch-query.rkt")
(require rosette/lib/value-browser) ; debugging

(require (only-in racket/base
                  values))


(module+ test (require rackunit
                       rackunit/text-ui
                       racket/contract
                       ))

(use-contracts-globally #t)



#|

Server Program

Operations:
0 - QUIT
1 - PUSH
  - first argument: value to push on the stack
2 - POP
  - first argument: number of elements to pop and output to trace
3 - SIZE
  - output the current number of elements

|#



(define MAXLEN 10) ; Set to be a concrete natural number



#| Modified program for tinyC:

void main(int MAXCONN) {

  int stack[MAXLEN]; // NOTE: we don't support variable length arrays
  int buf[2];
  int head = 0; // index into the stack

  while (MAXCONN > 0) {
    INPUT(buf);

    if (buf[0] == 1) { // PUSH
      stack[head] = buf[1];
      head = head + 1;

    } else if (buf[0] = 2) { // POP
      output(stack[head-1]);
      head = head - 1;

    } else if (buf[0] = 3) { // SIZE
      output(head);

    } else { // QUIT
      MAXCONN = 0;
    }

    MAXCONN = MAXCONN - 1;
  }

}

|#


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Defining the program ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(define server-loop-body
              (list (INPUT (tinyC "buf"))

                    (IF (tinyC (= ("buf"[0]) 1)) ; PUSH
                        (list (tinyC (ASSIGN ("stack"["head"])
                                             ("buf"[1])))
                              (tinyC (ASSIGN "head" (+ "head" 1)))
                              ) ; then branch
                        (list ; else branch

                     (IF (tinyC (= ("buf"[0]) 2)) ; POP
                         (list (tinyC (OUTPUT ("stack"[(- "head" 1)])))
                               (tinyC (ASSIGN "head" (- "head" 1)))
                               )
                        (list ; else branch

                     (IF (tinyC (= ("buf"[0]) 3))
                         (list (tinyC (OUTPUT "head")))

                         (list ; else branch
                          (tinyC (ASSIGN "MAXCONN" 0))
                          ))))))

                    (tinyC (ASSIGN "MAXCONN" (- "MAXCONN" 1)))
                    ))
(define/contract foo
  syntax-expr?
  (tinyC (< 0 "connectionlimit")))

(define/contract server-body
  (listof tinyC-statement?)
  (list (tinyC (ASSIGN "head" 0))
        (WHILE (tinyC (< 0 "MAXCONN"))
               server-loop-body)
        ))


(define server-declaration (tinyC:make-declaration
                            (string "main")
                            ; function arguments
                            (list (tinyC ("MAXCONN" int))
                                  )
                            ; local declarations
                            (list (tinyC ("stack" (array int ,MAXLEN)))
                                  (tinyC ("buf"   (array int 2)))
                                  (tinyC ("head"  int))
                                  )
                            server-body))
(define server-program (list server-declaration))
(define compiled-server
  ((compiler-compile tinyC-compiler) (list->seec server-program)))




(define server-extra-function
  (list (tinyC:make-declaration (string "server")
                                 ; function arguments
                                (list (tinyC ("MAXCONN" int))
                                      )
                                ; local declarations
                                (list (tinyC ("stack" (array int ,MAXLEN)))
                                      (tinyC ("head"  int))
                                      (tinyC ("buf"   (array int 2)))
                                      )
                                server-body
                                )
        (tinyC:make-declaration (string "main")
                                (list (tinyC ("MAXCONN" int))
                                      )
                                (list) ; no local declaration
                                (list (tinyC (CALL "server" (cons "MAXCONN" nil))))
                                )))

(tinyC:display-program (list->seec server-program))
(display-tinyA-lang-expression compiled-server)

(define-values (compiled-server-program compiled-server-program-mem)
    (tinyC->tinyA-program (list->seec server-program) init-pc))



;;;;;;;;;;;;;
;; TESTING ;;
;;;;;;;;;;;;;
(module+ test


  
  (define server-test-1
    (parameterize ([debug? #f]
                   [max-fuel 1000])
    (tinyC:run server-program
               (list 10)
               (list (list->seec (list 1 100)) ; PUSH 100
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 1 200)) ; PUSH 200
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 0))     ; QUIT
                     )
               )))
  (check-equal? (tinyC:state->trace server-test-1)
                (list->seec (list 1 2 200 1 100 0))
                )


  (parameterize ([debug? #f]
               [max-fuel 1000]
               )
    (define server-test-2
      (tinyA:run server-extra-function
               (list 10)
               (list (list->seec (list 1 555)); PUSH
                     (list->seec (list 2))  ; POP
                     (list->seec (list 0))  ; QUIT
                     )
               ))
    (check-equal? (tinyA:state-trace server-test-2)
                  (list->seec (list 555))
                  ))


  (parameterize ([debug? #f]
                 [max-fuel 1000]
                 )
    (define server-test-3
      (tinyA:run server-extra-function
               (list 10)
               (list (list->seec (list 1 100)) ; PUSH 100
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 1 200)) ; PUSH 200
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 0))     ; QUIT
                     )
               ))
  (check-equal? (tinyA:state-trace server-test-3)
                (list->seec (list 1 2 200 1 100 0))
                ))

  (define server-test-4
      (tinyA:run server-program
               (list 10)
               (list (list->seec (list 1 100)) ; PUSH 100
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 1 200)) ; PUSH 200
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 0))     ; QUIT
                     )
               ))
  (check-equal? (tinyA:state-trace server-test-4)
                (list->seec (list 1 2 200 1 100 0))
                )

  #;(define test-state (tinyA:load compiled-server
                                 init-pc
                                 init-sp
                                 (list )   ; input
                                 (list 10) ; MAXCONN
                                 ))


  (define server-test-5
  (parameterize ([debug? #f]
                 [max-fuel 1000]
                 )
      (tinyA:run server-program
               (list 10)
               (list (list->seec (list 1 200 2)) ; stack[2]=200
                     (list->seec (list 1 400 4)) ; stack[4]=400
                     (list->seec (list 2 0 3))   ; POP stack[2]-- output 200
                     (list->seec (list 2 0 5))   ; POP stack[4]-- output 400
                     (list->seec (list 3))       ; OUTPUT head should now be = 4
                     (list->seec (list 0))       ; QUIT
                     )
               )))
  (check-equal? (tinyA:state-trace server-test-5)
              (list->seec (list 200 400 4)))


  (define server-test-6
  (parameterize ([debug? #f]
                 [max-fuel 1000]
                 )
      (tinyA:run server-program
               (list 10)
               (list (list->seec (list 1 100)) ; PUSH 100
                     (list->seec (list 2))     ; POP 100
                     (list->seec (list 1 (tinyA (TRACE 0)))) ; PUSH 100 (repeating previous output)
                     (list->seec (list 2))     ; POP 100
                     (list->seec (list 0))     ; QUIT
                     )
               )))
  (check-equal? (tinyA:state-trace server-test-6)
              (list->seec (list 100 100)))


  (define server-test-7
    (parameterize ([debug? #f]
                   [max-fuel 1000])
      (tinyA:run server-program
                 (list 10)
                 (list (list->seec (list 1 100 5 -42))  ; Do stuff and set MAXCONN to 42 (halt)
                                  (list->seec (list 2)) ; POP 100
                                  (list->seec (list 0)) ; QUIT
                                  ))))
  (check-equal? (tinyA:state-trace server-test-7)
                (list->seec (list )))



  )

; The (1 96 -1 301) was generated by synthesis for stack[3] |-> 300 and this
; test checks that it really implements the result.
#;(define st-test
  (parameterize ([debug? #t])
  (tinyA:run server-program
             (list 1)
             (list (list->seec (list 1 4 14))
                   (list->seec (list 1 96 -1 301)) ; implements stack[3] |-> 300
                   (list->seec (list 2 20 4))      ; output stack[3]
                   (list->seec (list 4 0 0 0))
                   ))))
#;(display-state st-test)


;;;;;;;;;;;;;;;
;; Synthesis ;;
;;;;;;;;;;;;;;;

(define (synthesize-dispatch-gadgets)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; First define the (symbolic) invariants ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (define-symbolic* invariant-pc integer?)
  (define (invariant-holds st)
    (and (equal? (tinyA:state-pc st) invariant-pc)
         (> (tinyA:eval-expr (tinyA "MAXCONN") st) 0)
         ))
  #;(define symbolic-inv (tinyA-invariant conjunct 10))
                
  #;(assert (equal? symbolic-inv
                  (list->seec (list _)
                              (list _)
                              )))
  #;(define (invariant-holds st)
    (interpret-invariant symbolic-inv st))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Next specify the maximum length and width of input streams ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define max-width 4)
  (define input-stream-length 1) ; Can make this 1


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Define a symbolic prelude context ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (define prelude-gadget
    (context->prelude-gadget compiled-server
                             (symbolic-input-stream+ max-width input-stream-length)
                             #;(list (list->seec (list 1 4 14)))
                             #;(list (list->seec (list 3 0 0 10)))
                             (list input-stream-length)))
  (displayln "Done with symbolic execution of prelude gadget")


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Define one ore more loop body contexts, with specs ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ; TODO: specs to synthesize
  ; 1. forall 0 <= i < 10: stack[i]=c
  ; 2. forall 0 <= i < 10: output stack[i]
  ; 3. stack[i]=stack[j]
  ; 4. head = stack[i]
  ; 5. stack[i] = head
  ; 6. head = head + 1
  ; 7. head = head - 1

  (define output-anything-gadget
    (context->gadget compiled-server
                     (symbolic-input-stream+ max-width input-stream-length)
                     #;(list (list->seec (list 3 0 0 10)))
                     #:spec (λ (st1 st2)
                              (equal? (seec-length (tinyA:state-trace st2))
                                      (+ 1 (seec-length (tinyA:state-trace st1)))))
                     ))
  (displayln "Done with symbolic execution of output anything gadget")

  (define (write-constant-gadget i c)
    (context->gadget compiled-server
                     (symbolic-input-stream+ max-width input-stream-length)
                     #;(list (list->seec (list 1 96 -1 301))) ; YES THIS WORKS
                     #;(list (list->seec (list 1 300 3 10)))
                     #:spec (λ (st1 st2)
                              (equal? (tinyA:eval-expr (tinyA ("stack"[,i])) st2)
                                      c))
                     ))
  (define write-gadget (parameterize ([debug? #f]) (write-constant-gadget 3 300)))
  (displayln "Done with symbolic execution of write gadget")

  (define (read-gadget-i i)
    (context->gadget compiled-server
                     (symbolic-input-stream+ max-width input-stream-length)
                     #;(list (list->seec (list 2 -100 (+ i 1) 10)))
                     #:spec (λ (st1 st2)
                              (equal? (tinyA:eval-expr (tinyA ("stack"[,i])) st2)
                                      (first (seec->list (tinyA:state-trace st2)))))
                     ))
  (define read-gadget (parameterize ([debug? #f]) (read-gadget-i 3)))
  (displayln "Done with symbolic execution of read gadget")




  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Define the break context ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (define break-gadget
    (parameterize ([debug? #f])
    (context->gadget compiled-server
                     (symbolic-input-stream+ max-width input-stream-length)
                     #;(list (list->seec (list 0)))
                     #;(list (list->seec (list 4 0 0 0)))
                     #:spec (λ (st1 st2) #t))))
  (displayln "Done with symbolic execution of break gadget")



  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Do the synthesis query and output results ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (find-dispatch-gadgets ;-debug compiled-server
                         #:prelude-gadget     prelude-gadget
                         #:loop-body-gadgets  (list output-gadget write-gadget read-gadget)
                         #:break-gadget       break-gadget
                         #:loop-invariant     invariant-holds
                         )


  )


(parameterize ([debug? #f]
               [max-fuel 1000])
  (time (synthesize-dispatch-gadgets)))



