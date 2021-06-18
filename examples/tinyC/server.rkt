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


; server program
; Inspired by Data-Oriented Programming by Hu et al

#| Original program:

struct server {int *cur_max, total, typ;} *srv;
int connect_limit = MAXCONN;
int *size, *type;
char buf[MAXLEN];

size = &buf[8];
type = &buf[12];

...
while (connect_limit--) {
  readData(sockfd, buf);
  if (*type == NONE)    break;
  if (*type == STREAM)  *size = *(srv->cur_max); // truncating the stream?
  else {
    srv->typ = *type;
    srv->total += *size;
  }
  ... [use size to determine how long to look ahead at the buffer] ...
}

|#


#| Modified program for tinyC:

void main(int MAXCONN, int MAXLEN) {

  int** srv_cur_max;
  int* srv_total srv_typ;
  int connection_limit = MAXCONN;
  int *size;
  int *type;

  int buf[MAXLEN];
  size = &buf[8];
  type = &buf[12];

  ...

  while (connection_limit > 0) {
    input(buf);
    if (*type == 0) { // indicating NONE
      connection_limit = 0; // CHANGE: we don't have break statements
    } else if (*type == 1) { // indicating STREAM
      *size = *srv_cur_max;
    } else {
      *srv_typ = *type;
      *srv_total = *srv_total + *size;
    }
    ...
    connection_limit = connection_limit - 1; 
  }
}

|#






#|

Alternative server

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

(define (INPUT arg)
  (tinyC (INPUT ,arg)))
(define (& arg)
  (tinyC (& ,arg)))
(define (IF b ls1 ls2)
  (tinyC (IF ,b
             ,(tinyC:list->statement ls1)
             ,(tinyC:list->statement ls2))))
(define (WHILE b ls)
  (tinyC (WHILE ,b
                ,(tinyC:list->statement ls))))
(define (OUTPUT arg)
  (tinyC (OUTPUT ,arg)))
(define (CALL p args)
  (tinyC (CALL ,p ,(list->seec args))))
(define (ASSIGN x v)
  (tinyC (ASSIGN ,x ,v)))
(define (INDEX arr i)
  (tinyC (,arr[,i])))


#| Modified program for tinyC:

void main(int MAXCONN) {

  int stack[MAXLEN]; // NOTE: we don't support variable length arrays
  int head = 0; // index into the stack
  int buf[2];

  while (MAXCONN > 0) {
    INPUT(buf);

    if (buf[0] == 1) { // PUSH
      stack[head] = buf[1];
      head = head + 1;

    } else if (buf[0] = 2) { // POP
      output(stack[head]);
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
                                  (tinyC ("head"  int))
                                  (tinyC ("buf"   (array int 2)))
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



(module+ test

#;(parameterize ([debug? #t])
  (define server-test-quit
    (tinyA:run server-program
               (list 3)
               (list (seec-singleton 0)
                     )
               ))
  (display-state server-test-quit)
  )

 

  
  (define server-test-1
    (parameterize ([debug? #t]
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


  (parameterize ([debug? #t]
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


  (parameterize ([debug? #t]
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

  (debug? #t)
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

  )

(define (synthesize-dispatch-gadgets)

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
    

  (define-symbolic* invariant-pc integer?)
  #;(define invariant-pc 102)
  (define (invariant-holds st)
    (and (equal? (tinyA:state-pc st) invariant-pc)
         ))

  (define max-width 2)
  (define input-stream-length 2) ; Can make this 1
  #;(define prelude-context   (seec->list (symbolic-input-stream max-width input-stream-length)))
  (define prelude-context (list))
  (define loop-body-context (symbolic-input-stream+ max-width input-stream-length))
  #;(define loop-body-context (list (list->seec (list 1 100)) ; PUSH
                                  (list->seec (list 2))     ; POP
                                  ))
  #;(define break-context     (seec->list (symbolic-input-stream max-width input-stream-length)))
  (define break-context (list (list->seec (list 0))))

  (define-values (compiled-server-program compiled-server-program-mem)
    (tinyC->tinyA-program (list->seec server-program) init-pc))


  (define state-after-prelude
    (let ([init-st (tinyA:load-compiled-program compiled-server-program
                                                compiled-server-program-mem
                                                (tinyA nil) ; mem
                                                init-sp
                                                prelude-context
                                                (list input-stream-length) ; max number of iterations--is this symbolic? This number doesn't matter as long as it doesn't disallow any of the input stream
                                                )
                   ])
      (eval-statement-wait (max-fuel) init-st)))

  #;(displayln "Got state after prelude:")
  #;(display-state state-after-prelude)



  ; Current loop spec: output any trace
  (define (loop-body-spec st1 st2)
    (equal? (seec-length (tinyA:state-trace st2))
            (+ 1 (seec-length (tinyA:state-trace st1)))
            ))


  (define state-before-body (prepare-invariant-state compiled-server))
  #;(define state-before-body state-after-prelude)
  (debug-display "state before body:")
  (debug (thunk (for/all ([st state-before-body])
                  (display-state st))))
  #;(debug-display "invariant holds? ~a" (invariant-holds state-before-body))
  #;(debug-display "MAXCONN: ~a" (tinyA:eval-expr (tinyA "MAXCONN") state-before-body))

  (define state-after-body (parameterize ([debug? #t])
                             (do st <- state-before-body
                               (evaluate-prepared-state st loop-body-context))))
  #;(debug-display "state after body:")
  #;(display-state state-after-body)
  #;(debug-display "invariant holds? ~a" (invariant-holds state-after-body))
  #;(debug-display "MAXCONN: ~a" (tinyA:eval-expr (tinyA "MAXCONN") state-after-body))
  #;(debug-display "loop-body-spec: ~a" (loop-body-spec state-before-body state-after-body))


  (define state-before-break (prepare-invariant-state compiled-server))
  #;(define state-before-break state-after-prelude)
  (define state-after-break (do st <- state-before-break
                               (evaluate-prepared-state st break-context)))

  (define (test-simultaneously)
    (define sol
      (synthesize #:forall (list state-before-body state-before-break)
                  #:assume (assert (and (invariant-holds state-before-body)
                                        (> (tinyA:eval-expr (tinyA "MAXCONN") state-before-body)
                                           2)
                                        (invariant-holds state-before-break)
                                        (> (tinyA:eval-expr (tinyA "MAXCONN") state-before-break)
                                           2)
                                        ))
                  #:guarantee (assert (and (invariant-holds state-after-prelude)
                                           (invariant-holds state-after-body)
                                           (loop-body-spec state-before-body state-after-body)
                                           (not (invariant-holds state-after-break))
                                      ))
                  ))

    ;; Debugging version
    #;(define sol (synthesize #:forall (list)
;                            #:assume (assert (invariant-holds state-before-body)
;                                             (> (tinyA:eval-expr (tinyA "MAXCONN") state-before-body) 2)
;                                             )
                            #:guarantee
                            (assert (and
                               (invariant-holds state-before-body)
                               (> (tinyA:eval-expr (tinyA "MAXCONN") state-before-body)
                                  2)
                               (not (<= (tinyA:eval-expr (tinyA (& ("buf"[0]))) state-before-body)
                                        (tinyA:eval-expr (tinyA "buf") state-before-body)
                                        (tinyA:eval-expr (tinyA (& ("buf"[9]))) state-before-body)))
                               (not (and (invariant-holds state-after-body)
                                         (loop-body-spec state-before-body state-after-body)))))
                            ))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")

          (define-values (prelude-context-concrete
                          loop-context-concrete
                          break-context-concrete
                          #;state-before-loop
                          #;state-after-loop)
            (let ([contexts (concretize (list prelude-context loop-body-context break-context #;state-before-body #;state-after-body)
                                        sol)])
              (values (first contexts)
                      (second contexts)
                      (third contexts)
                      #;(fourth contexts)
                      #;(fifth contexts))))
          (displayln (format "Prelude context: ~a" prelude-context-concrete))
          (displayln (format "Loop context: ~a" loop-context-concrete))
          (displayln (format "Break context: ~a" break-context-concrete))

          #;(displayln "State before loop:")
          #;(display-state state-before-loop)

          #;(displayln (format "MAXCONN before loop: ~a" (tinyA:eval-expr (tinyA "MAXCONN") state-before-loop)))
          #;(displayln "")

          #;(displayln "Got state after loop:")
          #;(display-state state-after-loop)

          ))
    )
    
  (test-simultaneously)


  )

(parameterize ([debug? #f]
               [max-fuel 1000])
  (time (synthesize-dispatch-gadgets)))
