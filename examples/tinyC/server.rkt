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


  )


;;;;;;;;;;;;;;;;;;;;;;;;
;; Added a structure to better treat dispatch gadgets uniformly, moving towards
;; a framework query
;;;;;;;;;;;;;;;;;;;;;;;;

(struct dispatch-gadget (context spec before after))

(define (dispatch-spec-holds g)
  ((dispatch-gadget-spec g) (dispatch-gadget-before g) (dispatch-gadget-after g)))

(define context->gadget
  (λ (compiled-prog
      ctx
      #:spec spec
      #:state-before [state-before (prepare-invariant-state compiled-prog)]
      )

    (debug-display "(context->gadget ~a)" ctx)
    (define state-after (do st <- state-before
                            (evaluate-prepared-state st ctx)))

    (dispatch-gadget ctx
                     spec
                     state-before
                     state-after
                     )))

;;;;;;;;;;;;;;;
;; Synthesis ;;
;;;;;;;;;;;;;;;

(define (synthesize-dispatch-gadgets)

    
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; First define the invariant ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define-symbolic* invariant-pc integer?)
  #;(define invariant-pc 102)
  (define (invariant-holds st)
    (and (equal? (tinyA:state-pc st) invariant-pc)
         ))
  (define (invariant-requires st)
    (> (tinyA:eval-expr (tinyA "MAXCONN") st)
       2))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Next specify the maximum length and width of input streams ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define max-width 3)
  (define input-stream-length 1) ; Can make this 1


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Define a symbolic prelude context ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (define prelude-gadget

    #;(define prelude-context (symbolic-input-stream+ max-width input-stream-length))
    (let ([prelude-context (list )])

    (context->gadget compiled-server
                 prelude-context
                 #:spec (λ (st1 st2) #t)
                 #:state-before (tinyA:load-compiled-program
                                 compiled-server-program
                                 compiled-server-program-mem
                                 (tinyA nil) ; mem
                                 init-sp
                                 prelude-context
                                 ; max number of iterations below--is this
                                 ; symbolic? This number doesn't matter as long
                                 ; as it doesn't disallow any of the input
                                 ; stream
                                 (list input-stream-length)
                                 )
                 )))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Define one ore more loop body contexts, with specs ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  


  ; Basic loop spec: output any trace
  #;(define (loop-body-spec st1 st2)
    (equal? (seec-length (tinyA:state-trace st2))
            (+ 1 (seec-length (tinyA:state-trace st1)))
            ))

  ; TODO: specs to synthesize
  ; 1. forall 0 <= i < 10: stack[i]=c
  ; 2. forall 0 <= i < 10: output stack[i]
  ; 3. stack[i]=stack[j]
  ; 4. head = stack[i]
  ; 5. stack[i] = head
  ; 6. head = head + 1
  ; 7. head = head - 1


  (define/contract (write-constant-gadget i c) ; Write constant c to index i in the stack
    (-> integer? integer? dispatch-gadget?)

    (define loop-body-context-concrete (list (list->seec (list 1 c i))))
    #;(define loop-body-context (symbolic-input-stream+ 3 input-stream-length))
    (define-symbolic* symbolic-cmd integer?)
    (define-symbolic* symbolic-c integer?)
    (define-symbolic* symbolic-i integer?)
    ; This is not currently working properly...
    (define loop-body-context 
      (cond
        [(havoc!) (list (list->seec (list symbolic-cmd symbolic-c symbolic-i)))]
        #;[(havoc!) (list (list->seec (list symbolic-cmd)))]
        #;[(havoc!) (list (list->seec (list symbolic-cmd symbolic-c )))]
        [else (list)]
        ))
    #;(define loop-body-context loop-body-context-concrete)
    (assert (equal? loop-body-context loop-body-context-concrete))

    (define (loop-body-spec st1 st2)
      (equal? (tinyA:eval-expr (tinyA ("stack"[,i])) st2)
              c))
    (context->gadget compiled-server
                     loop-body-context
                     #:spec loop-body-spec
                     )
    )
  (define write-gadget (write-constant-gadget 3 300))




  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ; Define the break context ;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (define break-gadget

    (let ([break-context (list (list->seec (list 0)))
                         #;(seec->list (symbolic-input-stream max-width input-stream-length))
                         ])

      (context->gadget compiled-server
                       break-context
                       #:spec (λ (st1 st2) #t)
                       )))



  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Do the synthesis query and output results ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ; TODO: generalize state-before-break/state-before-body into a list that each
  ; has specs and this query can take any number of them
  (define (test-simultaneously)
    (define sol
      ; Add symbolic-i and symbolic-c to forall quantifier list (symbolic-vars)
      (synthesize #:forall (list (dispatch-gadget-before write-gadget)
                                 (dispatch-gadget-before break-gadget)
                                 )
                  #:assume (assert (and (invariant-holds    (dispatch-gadget-before write-gadget))
                                        ; In addition to the generic invariant, we also need to add 
                                        (invariant-requires (dispatch-gadget-before write-gadget))
                                        (invariant-holds    (dispatch-gadget-before break-gadget))
                                        (invariant-requires (dispatch-gadget-before break-gadget))
                                        ))
                  #:guarantee (assert (and (invariant-holds (dispatch-gadget-after prelude-gadget))
                                           (invariant-holds (dispatch-gadget-after write-gadget))
                                           (dispatch-spec-holds write-gadget)
                                           (not (invariant-holds (dispatch-gadget-after break-gadget)))
                                      ))
                  ))

    ;; Debugging version (for body context only)
    #;(define sol (synthesize #:forall (list)
;                            #:assume (assert (invariant-holds state-before-body)
;                                             (> (tinyA:eval-expr (tinyA "MAXCONN") state-before-body) 2)
;                                             )
                            #:guarantee
                            (assert (and (invariant-holds (dispatch-gadget-before write-gadget))
                                           ; In addition to the generic invariant, we also need to add 
                                           (invariant-requires (dispatch-gadget-before write-gadget))
                                           (invariant-holds state-before-break)
                                           (> (tinyA:eval-expr (tinyA "MAXCONN") state-before-break)
                                              2)
                                           (not (and (invariant-holds (dispatch-gadget-after write-gadget))
                                                     (dispatch-spec-holds write-gadget)))
                                           ))
                            ))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")

          (define-values (prelude-context-concrete
                          loop-context-concrete
                          break-context-concrete)
            (let ([contexts (concretize (list (dispatch-gadget-context prelude-gadget)
                                              (dispatch-gadget-context write-gadget)
                                              (dispatch-gadget-context break-gadget)
                                              )
                                        sol)])
              (values (first contexts)
                      (second contexts)
                      (third contexts)
                      )))
          (displayln (format "Prelude context: ~a" prelude-context-concrete))
          (displayln (format "Loop context: ~a" loop-context-concrete))
          (displayln (format "Break context: ~a" break-context-concrete))


          ))
    )
    
  (test-simultaneously)


  )

(parameterize ([debug? #t]
               [max-fuel 1000])
  (time (synthesize-dispatch-gadgets)))
















;;; SCRATCH ;;;;


#|

  ; Create a symbolic boolean invariant in CNF (language of SMT solvers)
  (define (symbolic-invariant)
    (symbolic-CNF))

  (define (symbolic-conjunct width len)
    (cond
      [(<= len 0) #t]
      [else       (and (symbolic-disjunct width) (symbolic-conjunct width (- len 1)))]
      ))
  (define (symbolic-disjunct width)
    (cond
      [(<= len 0) #f]
      [else       (or (symbolic-literal) (symbolic-disjunct (- width 1)))]
      ))

  (define (symbolic-literal)
    (let ([expr1 (symbolic-expression)]
          [expr2 (symbolic-expression)])
      (cond
        [(havoc!) (equal? expr1 expr2)]
        [(havoc!) (not (equal? expr1 expr2))]
        [(havoc!) (< expr1 expr2)]
        [else     ; constant boolean
         (define-symbolic* b boolean?)
         b]
        )))
  (define (symbolic-expression st)
    (cond
      [(havoc!) ; variable name
       _]
      [(havoc!) ; constant integer
       (define-symbolic* const integer?)
       const]
      [else     ; array indexing
  ]))
|#
