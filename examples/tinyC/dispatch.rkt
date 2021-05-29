#lang seec
(require seec/private/util)
(require seec/private/monad)
(require "tinyC.rkt"
         "tinyC-test.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt")
(require (only-in racket/base
                  values))

(require rosette/lib/value-browser) ; debugging

(module+ test (require rackunit
                       rackunit/text-ui
                       racket/contract
                       ))
(require (only-in racket/string ; formatting
                  string-join
                  ))
(require rosette/lib/value-browser) ; debugging



(use-contracts-globally #t)

#|
    100 |-> ("main" (ASSIGN "max-iterations" 3))
    101 |-> ("main" (JMPZ (< 0 "max-iterations") 106))
    102 |-> ("main" (INPUT (& "x")))
    103 |-> ("main" (OUTPUT "x"))
    104 |-> ("main" (ASSIGN "max-iterations" (- "max-iterations" 1)))
    105 |-> ("main" (JMPZ 0 101))
    106 |-> ("main" HALT)
|#



; This differs from tinyA-lang in that the behavior is a (failure/c state?)
; instead of a trace.
(define-language tinyA-lang-st
  #:grammar tinyA+
  #:expression expr #:size 5
  #:context ctx #:size 3 ; The trace acts as as the argument list
  ; A whole program is a (failure/c state?)
  #:link (λ (ctx expr)
           (match (cons ctx expr)
             [(cons (tinyA+ (args:vallist input:list<vallist>))
                    (tinyA (g:global-store sp:stack-pointer m:memory)))
              (tinyA:load-compiled-program g m sp (seec->list input) (seec->list args))]
             ))
  #:evaluate (λ (p) (do st <- p
                        (tinyA:eval-statement (max-fuel) st)))
  )

(define synthesize-tinyA-gadget
  (λ (prog
      #:spec       spec
      #:args       args
      #:input      [input (list)] ; list of lists of integers
      #:seec-input [seec-input (list->seec (map list->seec input))]
      #:forall     [vars (list)]
      )
    (let ([g (find-ctx-gadget tinyA-lang-st
                              spec
                              #:expr ((compiler-compile tinyC-compiler) (list->seec prog))
                              #:context (tinyA (,(list->seec args)
                                                ,seec-input nil))
                              #:forall vars
                              )])
      (display-gadget g #:display-expression display-tinyA-lang-expression
                        #:display-context    display-tinyA-lang-context
                        #:display-behavior   display-state
                        ))))


; Echo program:
;
; void main() {
;   int x;
;   int max-iterations = 3;
;   while (max-iterations > 0) {
;     input (&x);
;     output (x);
;     max-iterations--;
;   }
; }

(define echo-body (list (tinyC (ASSIGN "max-iterations" 3))
                        (tinyC (WHILE (< 0 "max-iterations")
                                      (SEQ (INPUT (& "x"))
                                      (SEQ (OUTPUT "x")
                                      (ASSIGN "max-iterations" (- "max-iterations" 1))))))
                        ))
(define echo-declaration (tinyC:make-declaration
                          (string "main")
                          (list)
                          (list (tinyC ("x" int))
                                (tinyC ("max-iterations" int))
                                )
                          ; ^ local declarations
                          echo-body))
(define echo-program (list echo-declaration))
(define compiled-echo
  ((compiler-compile tinyC-compiler) (list->seec echo-program)))


(module+ test
  (define (test-123)
    (define echo-test-123
      (tinyC:run echo-program (list)
                 (list (seec-singleton 1)
                       (seec-singleton 2)
                       (seec-singleton 3))))
    (check-equal? (tinyC:state->trace echo-test-123)
                  (list->seec (list 1 2 3)))
    )



  #;(tinyC:display-program (list->seec echo-program))
  #;(display-tinyA-lang-expression compiled-echo)

  (define (compiled-test-123)
    (define compiled-echo-test-123
      (tinyA:run echo-program
                 (list)
                 (list (seec-singleton 1)
                       (seec-singleton 2)
                       (seec-singleton 3))))
    (check-equal? (tinyA:state-trace compiled-echo-test-123)
                  (list->seec (list 1 2 3)))
    )
 
  (define (exploit-test-0)
    ; This will fail in tinyC because of an illegal buffer overflow
    (define echo-exploit-0
      (tinyC:run echo-program (list)
                 (list (list->seec (list 1 0))
                       (list->seec (list 2))
                       (list->seec (list 3)))
                 ))
    (check-equal? echo-exploit-0
                  *fail*)

    (define compiled-echo-exploit-0
      (parameterize ([debug? #f])
        (tinyA:run echo-program
                 (list)
                 (list (list->seec (list 1 0))
                       (list->seec (list 2))
                       (list->seec (list 3)))
                 )))
    (check-equal? (tinyA:state-trace compiled-echo-exploit-0)
                  (list->seec (list 1))
                  )
    )
  (exploit-test-0)

  (define (exploit-test-5)

    (define compiled-echo-exploit-5
      (parameterize ([debug? #f])
        (tinyA:run echo-program
                 (list)
                 (list (list->seec (list 1 2))
                       (list->seec (list 2 2))
                       (list->seec (list 3 2))
                       (list->seec (list 4 2))
                       (list->seec (list 5 0))
                       )
                 )))
    (check-equal? (tinyA:state-trace compiled-echo-exploit-5)
                  (list->seec (list 1 2 3 4 5))
                  )
    )
  (exploit-test-5)

  )

(define (null-input-test)
    (define compiled-echo-null-input
      (parameterize ([debug? #t])
        (tinyA:run echo-program
                   (list)
                   (list (list->seec (list)))
                   )))
  (display-state compiled-echo-null-input))
#;(null-input-test)

(define (symbolic-arglist n)
  (tinyA list<integer> (+ 1 n)))
; Produce a symbolic list<list<integer>> where the length is 'length' and each
; internal list has length 'width'
(define (symbolic-input-stream width length)
  (cond
    [(or (<= length 0)
         (havoc!))
     (tinyA nil)]
    [else (seec-cons (symbolic-arglist width)
                     (symbolic-input-stream width (- length 1)))
          ]
    ))

; Synthesize an input to produce a specific trace
; tr should be a racket list of integers
(define (synthesize-trace input-len tr)

  (define (prelude-spec target-pc init-st result-st)
    (and (tinyA:state? result-st)
         (equal? (tinyA:state-pc result-st) target-pc)))
  (define (body-spec target-pc init-st result-st)
    ; A whole program is a (failure/c state?)
    (and (tinyA:state? init-st)
         (tinyA:state? result-st)
         (equal? (tinyA:state-pc init-st)  target-pc)
         (equal? (tinyA:state-pc result-st) target-pc)))

  ; Fuel bound = size of program. OR: don't execute the target PC along the way?
  ; Do we need to synthesize loop invariant?

  (synthesize-tinyA-gadget echo-program
                           #:spec (λ (init-state result-state)
                                    (and (tinyA:state? result-state)
                                         (equal? (seec->list (tinyA:state-trace result-state))
                                                 tr)))
                           #:args (list)
                           #:seec-input (symbolic-input-stream 2 input-len)
                           )


  )

#;(time (parameterize ([debug? #t])
        (synthesize-trace 3 (list 3))))
; Synthesizes ((3,0) (0,0) (0,0)) in 3 min
#;(time (parameterize ([debug? #f])
        (synthesize-trace 1 (list 3))))
; Synthesizes ((3,0)) in 4 sec
#;(time (parameterize ([debug? #f])
        (synthesize-trace 3 (list 1 2 3))))
; Synthesizes ((1, 3) (2) (3)) in 2.5 min
#;(time (parameterize ([debug? #f])
        (synthesize-trace 4 (list 1 2 3 4))))
; Synthesizes ((1,2) (2,6286) (3) (4,0)) in 30 min



; NEXT STEP: how to track program fragments, e.g. a loop?
;

; OR: just execute until you expect an input and it's not provided by the context
; Specify by a relational spec, e.g. you should be able to
; The goal of the loop body:
;   1. produce the behavioral goal of a loop iteration [e.g. print something, in this case]
;   2. control either terminate or you're in a state where you can run the spec again
; 
; You could imagine changing the behavioral goal to print 2 things, which should do 2 iterations of the loop

; Define a function that evaluates a state until either (1) HALT is reached; or
; (2) an INPUT is reached where no input is provided via the context.
(define/contract (eval-statement-wait fuel st)
  (-> (or/c #f integer?) tinyA:state? (failure/c tinyA:state?))
  (debug-display "(eval-statement-wait ~a)" fuel)

  (for*/all ([st st]
             [pc (tinyA:state-pc st) #:exhaustive]
             [insn (tinyA:pc->instruction pc (tinyA:state-memory st))]
             [input (tinyA:state-input-buffer st)]
             )

  (debug-display "eval-statement-wait pc: ~a [~a]" pc insn)

  (cond
    [(not (list? input))
     *fail*]

    ; execution halted safely
    [(tinyA:HALT? insn)
     (debug-display "halted on HALT")
     st]

    ; execution paused waiting for input
    [(and (tinyA:INPUT? insn)
          (empty? input))
     (debug-display "halted on INPUT")
     st]
    ; fuel ran out
    [(<= fuel 0)
     (debug-display "fuel ran out")
     *fail*]

    ; otherwise, take a step and continue
    [else 
     (do st+ <- (tinyA:eval-statement-1 st)
         (eval-statement-wait (decrement-fuel fuel) st+))]
    )))

#;(define/contract (eval-statement-wait fuel st)
  (-> (or/c #f integer?) tinyA:state? (failure/c tinyA:state?))
  (debug-display "(eval-statement-wait ~a)" fuel)
  )



; I'm using find-gadget rather than find-ctx-gadget here because we want to
; quantify over all states/contexts

; An expression/gadget is an input stream
; A context is an (failure/c state?)
; A whole program is a (failure/c state?)
; Linking appends the input stream of the context with the gadget
; Behaviors are states (not necessarily in a HALT state)
; Evaluate takes steps until no more input is availbable

;(define-language tinyA-lang-wait
;  #:grammar tinyA+
;  #:expression vallistlist #:size 5
;  #:context state? #:size 5 ; Can't have a state because it's not a bonsai structure
;  ; A whole program is a (failure/c state?)
;  ; A behavior is also a (failure/c state?)
;  #:link (λ (ctx expr)
;           (do st <- ctx
;               (tinyA:update-state st
;                                   #:input-buffer (append (tinyA:state-input-buffer st)
;                                                          (seec->list expr)))))
               
;           (match (cons ctx expr)
;             [(cons (tinyA+ (args:vallist input:list<vallist>))
;                    (tinyA (g:global-store sp:stack-pointer m:memory)))
;              (tinyA:load-compiled-program g m sp (seec->list input) (seec->list args))])
             
;  #:evaluate (λ (p) (do st <- p
;                        (eval-statement-wait (max-fuel) st)))
;  )


#;(define (synthesize-loop-dispatch-gadgets)
  (define prelude-context   (tinyA ctx 3))
  (define loop-body-context (tinyA ctx 3))
  (define loop-end-context  (tinyA ctx 3))

  (define (loop-invariant st)
    (or (equal? st (evaluate-prelude st))
        (forall st+ (implies (and (loop-invariant st+)
                                  (equal? (evaluate-body-context st+) st))
                             (loop-invariant st)))))

  )

(define-grammar invariant-syntax #:extends syntax
  (bexp ::= boolean
            (b-unop bexp)
            (b-binop bexp bexp)
            (= expr expr)
            )
  (b-unop ::= not)
  (b-binop ::= &&
               ||
               =>
               =
               )
  )

(define (interpret-bexp b st)
  (match b
    [(invariant-syntax b+:boolean) b+]
    [(invariant-syntax (not b+:bexp))
     (not (interpret-bexp b+))]
    [(invariant-syntax (&& b1:bexp b2:bexp))
     (and (interpret-bexp b1)
          (interpret-bexp b2))]
    [(invariant-syntax (|| b1:bexp b2:bexp))
     (or (interpret-bexp b1)
         (interpret-bexp b2))]
    [(invariant-syntax (=> b1:bexp b2:bexp))
     (implies (interpret-bexp b1)
              (interpret-bexp b2))]
    [(invariant-syntax (= b1:bexp b2:bexp))
     (equal? (interpret-bexp b1)
             (interpret-bexp b2))]
    [(invariant-syntax (= e1:expr e2:expr))
     (equal? (tinyA:eval-expr e1 st)
             (tinyA:eval-expr e2 st))]
    ))

  (define/contract (state->pc-declaration st)
    (-> tinyA:state? (failure/c tinyA-declaration?))
    (match (tinyA:lookup-mem (tinyA:state-pc st) (tinyA:state-memory st))
      [(tinyA (f:proc-name _:statement))
       (tinyA:proc-name->declaration f (tinyA:state-global-store st))]
      [_ *fail*]
      ))


  ; Push 'count' symbolic arguments onto memory at locations `l`, `l+1`, ..., `l+count-1`
  (define (push-objs-symbolic l count mem)
    (cond
      [(> count 0)
       (let ([symbolic-obj (tinyA object 2)])
         #;(for/all ([obj symbolic-obj])
           (debug-display "Adding mapping ~a |-> ~a" l obj))
         (seec-cons (tinyA (,l ,symbolic-obj))
                    (push-objs-symbolic (+ 1 l) (- count 1) mem)))]
      [else mem]
      ))


  (define (append-input-stream st new-input)
    (tinyA:update-state st
                        #:input-buffer (append (tinyA:state-input-buffer st)
                                               new-input)))

  ; new-input should be a racket list of seec-lists (the input stream)
  (define/contract (evaluate-prepared-state st new-input)
    (-> tinyA:state? (listof (curry seec-list-of? integer?)) (failure/c tinyA:state?))
    (eval-statement-wait (max-fuel)
                         (append-input-stream st new-input)
                         ))



  ; The pc is a symbolic union of the initial pc, the pc of any HALT
  ; instructions, and the pc of any INPUT instructions
  (define/contract (potential-pc-from-memory prog)
    (-> tinyA-memory? (failure/c tinyA-program-counter?))
    (match prog
      [(tinyA (cons (l:loc (f:proc-name HALT)) m+:memory))
       (if (havoc!)
           l
           (potential-pc-from-memory m+))]
      [(tinyA (cons (l:loc (f:proc-name (INPUT _:expr))) m+:memory))
       (if (havoc!)
           l
           (potential-pc-from-memory m+))]
      [(tinyA (cons (l:loc (f:proc-name _:statement)) m+:memory))
       (potential-pc-from-memory m+)]
      [_ *fail*]
      ))


  (define pc0 100)
  (define sp0 100)



  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; 3. create a symbolic state based on the structure of the state-after-prelude+ ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ; TODO: look at induction hypothesis generation
  ; Also: constraint Horne clause verification?
  ; Separate program from stack memory, might make this easier

  ; Not sure this is the right approach...
  #;(define (prepare-invariant-state)
    (do st <- state-after-prelude+
        sp <- (tinyA:state-sp st)
        decl <- (state->pc-declaration st)
        fsize <- (tinyA:frame-size (tinyA:declaration->frame decl))
        ; Want to find out what function the prelude terminates in, so we can
        ; try to loop from that spot

        ; Make the current stack frame symbolic. If the loop involves function
        ; calls and returns, will need to amend this to deal with additional symbolic stack frames.
        mem <- (push-objs-symbolic (- sp fsize) fsize (tinyA:state-memory st))
        (tinyA:update-state st #:memory mem)
        ))


  ; If you do prepare-invariant-state with the symbolic state-after-prelude, it
  ; takes more than an hour; with the concrete state-after-prelude+, 4 min
  #;(define (prepare-invariant-state)
    (do st <- state-after-prelude+ ; TODO
        #;(for/all ([st st]) (cond
                             [(tinyA:state? st) (debug-display "pc: ~a" (tinyA:state-pc st))
                                                (debug-display "sp: ~a~n" (tinyA:state-sp st))]
                             [else (displayln st)]))
        (for/all ([pc (tinyA:state-pc st) #:exhaustive])
          (debug-display "pc: ~a" pc))
        (for/all ([sp (tinyA:state-sp st) #:exhaustive]) ; this might not be
                                                         ; necessary because the
                                                         ; sp shouldn't change
                                                         ; for this program

          #;(displayln "Preparing an invariant state from the following state:")
          #;(display-state st)
          ; The sp now should be concrete. If not, fail
          (cond
            [(symbolic? sp)
             (displayln "Got a symbolic stack pointer")
             *fail*]
            [else
             ; Get the program memory from compiled-echo; get the stack pointer
             ; and program counter from state-after-prelude
             (match compiled-echo
               [(tinyA (_:global-store _:stack-pointer echo-prog-in-memory:memory))
                (do mem <- (push-objs-symbolic sp (- sp0 sp) echo-prog-in-memory)
                    #;(displayln "Prepared symbolic memory")
                    (tinyA:update-state st #:memory mem))]
               )
             ]
            ))))
  ;
  ; The sp should be the same as the the initial state assuming that INPUT can't
  ; reach it and there are no calls or returns.
  ;
  ; If the sp can become symbolic through calls to input and/or other DOP
  ; attacks, what then?
  ;
  ; If the sp is symbolic and there are calls/returns, may be a control flow problem
  (define (prepare-invariant-state)
    (match compiled-echo
      [(tinyA (g:global-store sp:stack-pointer echo-prog-in-memory:memory))

       (do pc+ <- (potential-pc-from-memory echo-prog-in-memory)
           ; We don't have to add the initial pc back in because unless it's an
           ; INPUT or HALT, we won't halt on it
           pc <- pc+
           ;pc  <- (if (havoc!) pc0 pc+) ; make sure to add the initial pc back in
           ;pc   <- 102
           
           ; How many symbolic variables do we need? Currently just ones in the
           ; current stack frame. Might need to be extended if (1) we have a
           ; call stack with calls and returns; or (2) if the prelude needs to
           ; write additional objects to memory
           fsize <- (tinyA:frame-size (tinyA:pc->frame pc echo-prog-in-memory g))
           #;(debug-display "fsize: ~a" fsize)
           mem+  <- (push-objs-symbolic (- sp fsize) fsize echo-prog-in-memory)

           #;(display-memory mem+)

#|
           (debug-display "~nTesting")
           (displayln mem+)
           (debug-display "Local display-memory")
           (local-display-memory mem+)
           (debug-display "pp-memory")
           (displayln (pp-memory mem+))
           (debug-display "pp-map")
           (displayln (pp-map mem+))
           (debug-display "map without pp-mapping")
           (displayln (map (λ (x) x) (seec->list mem+)))
|#
           #;(debug-display "Regular display-memory")
           #;(display-memory mem+)

           (tinyA:initial-state #:global-store g
                                #:pc pc
                                #:sp (- sp fsize)
                                #:memory mem+
                                )
           )]
      ))

#;(define (test-bugs)
  (define foo (tinyA object 1))
  (render-value/window foo)

  #;(define mem (list->seec (list (tinyA (1 ,foo)))))
  #;(define should-be-foo (tinyA:lookup-mem 1 mem))
  #;(render-value/window should-be-foo)
  #;(displayln (equal? foo should-be-foo))
  
  (define st (prepare-invariant-state))
  (for/all ([val (tinyA:lookup-mem 98 (tinyA:state-memory st))])
    (displayln val))
  (displayln "Done")
  )
#;(parameterize ([debug? #t])
  (time (test-bugs)))


(define (pp-mapping pair)
  #;(format "~a" pair)
  (match pair
    [(tinyC (x:any y:any))
     #;(render-value/window x)
     (for/all ([x x])
     #;(format "~a" pair)
     (format "    ~a  ~a" x y))]
    ))
(define (pp-map m)
  (map pp-mapping (seec->list m)))

(define (pp-memory m)
    (string-join (pp-map m)
                 (format "~n")))
(define (local-display-memory m)
  (for/all ([m m]) (displayln (pp-memory m))))





(define (synthesize-dispatch-gadgets)


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; 1. Current invariant is concrete; later we hope to synthesize it ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  #;(define (invariant-holds st)
    (for/all ([current-max-iterations
               (tinyA:eval-expr (tinyA "max-iterations") st)
               #:exhaustive]) ; We need this for/all otherwise we will have a contradictory assumption??
      
    (> current-max-iterations 0)
         )) ; Change to be more abstract

  ; This version of invariant-holds can be derived automatically from
  ; conditional jump statements in the program. In this program there is only one,
  ; namely [JMPZ (< 0 "max-iterations") 106]
  (define-symbolic* invariant-pc integer?)
  (define (invariant-holds st)
    (and #;(equal? (tinyA:eval-expr (tinyA (< 0 "max-iterations")) st)
                 1)
         (equal? (tinyA:state-pc st)
                 invariant-pc
                 #;102))
    #;(for/all ([guard (tinyA:eval-expr (tinyA (< 0 "max-iterations")) st)
                     #:exhaustive])
      (equal? guard 1)))

  ; We make this more concrete because we know this function doesn't take any
  ; arguments
  (define max-width 2)
  (define input-stream-length 2)
  (define prelude-context   (seec->list (symbolic-input-stream max-width input-stream-length)))
  (define loop-body-context (seec->list (symbolic-input-stream max-width input-stream-length)))
  (define break-context     (seec->list (symbolic-input-stream max-width input-stream-length)))

  (define-values (compiled-echo-program compiled-echo-program-mem)
    (tinyC->tinyA-program (list->seec echo-program) pc0))
  

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; 2. (symbolic) prelude context with no input ;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  (define state-after-prelude
    (let ([init-st (tinyA:load-compiled-program compiled-echo-program
                                                compiled-echo-program-mem
                                                sp0
                                                prelude-context
                                                (list)
                                                )
                   ])
      (eval-statement-wait (max-fuel) init-st)))


  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; 4. synthesize loop-body-context such that, for all (symbolic)
  ;; state-before-body that satisfy the invariant, the state-after-body
  ;; also satisfies the invariant, and further makes progress (loop-body-spec)
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  ; Is state-before-body a big union? or a big symbolic term?
  (define state-before-body (prepare-invariant-state))
  (debug-display "state before body:")
  (display-state state-before-body)
  (define state-after-body (do st <- state-before-body
                               (evaluate-prepared-state st loop-body-context)))


  ; Try changing to 2+length(trace st1) instead of 1+length(trace st1)
  (define (loop-body-spec st1 st2)
    (equal? (seec-length (tinyA:state-trace st2))
            (+ 1 (seec-length (tinyA:state-trace st1)))
            ))





  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; 5. synthesize break-context such that, for all (symbolic)
  ;; state-before-break that satisfy the invariant, the state-after-body
  ;; no longer satisfies the invariant
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define state-before-break (prepare-invariant-state))
  (define state-after-break (do st <- state-before-break
                               (evaluate-prepared-state st break-context)))



  ;; synthesize a prelude-context such that the invariant holds
  (define (test-prelude)
    (define sol
      (synthesize #:forall (list)
                  #:assume (assert #t)
                  #:guarantee (assert (invariant-holds state-after-prelude)
                  )))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")

          (define prelude-context-concrete (concretize prelude-context sol))
          (displayln (format "Prelude context: ~a" prelude-context-concrete))
          (concretize state-after-prelude sol)
          ))
    )
  #;(define state-after-prelude+ (test-prelude))
  #;(display-state state-after-prelude+)

  
#|
Produced prelude context ((0,2))

state-after-prelude+:

== PC: 102
== SP: 98
== Trace: (0)
== Input stream: ()

==Memory==
    99 |-> 1
    98 |-> 0
    99 |-> 2
    99 |-> 3
    100 |-> ("main" (ASSIGN "max-iterations" 3))
    101 |-> ("main" (JMPZ (< 0 "max-iterations") 106))
    102 |-> ("main" (INPUT (& "x")))
    103 |-> ("main" (OUTPUT "x"))
    104 |-> ("main" (ASSIGN "max-iterations" (- "max-iterations" 1)))
    105 |-> ("main" (JMPZ 0 101))
    106 |-> ("main" HALT)
|#

  #;(define (test-body)
    (define sol
      (synthesize #:forall    (list state-before-body)
                  #:assume    (assert (invariant-holds state-before-body))
                  #:guarantee (assert (and (invariant-holds state-after-body)
                                           (loop-body-spec state-before-body
                                                           state-after-body)
                                           ))
                  ))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")

          (define loop-context-concrete (concretize loop-body-context sol))
          (displayln "Loop context:")
          (displayln loop-context-concrete)
          (cond
            [(not (list? loop-context-concrete))
             (displayln "Something went wrong... There must be some kind of inconsistency")
             ]
            [else
             ; instead of concretizing state-after-body, instead run
             ; eval-statement-wait with the concretized context and state-after-prelude+
             #;(concretize state-after-body sol)
             (eval-statement-wait (max-fuel)
                                  (append-input-stream state-after-prelude+
                                                       loop-context-concrete))
             ]
             ))))

  #;(define state-after-body+ (test-body))
  #;(displayln "State after body:")
  #;(display-state state-after-body+)



#|
Produced looop context ((0,2))

state-after-prelude+:

== PC: 102
== SP: 98
== Trace: (0 (0))
== Input stream: ()

==Memory==
    99 |-> 1
    98 |-> 0
    99 |-> 2
    99 |-> 1
    98 |-> 0
    99 |-> 2
    99 |-> 3
    100 |-> ("main" (ASSIGN "max-iterations" 3))
    101 |-> ("main" (JMPZ (< 0 "max-iterations") 106))
    102 |-> ("main" (INPUT (& "x")))
    103 |-> ("main" (OUTPUT "x"))
    104 |-> ("main" (ASSIGN "max-iterations" (- "max-iterations" 1)))
    105 |-> ("main" (JMPZ 0 101))
    106 |-> ("main" HALT)
|#


  #;(define (test-break)
    (define sol
      (synthesize #:forall    (list state-before-break)
                  #:assume    (assert (invariant-holds state-before-break))
                  #:guarantee (assert (not (invariant-holds state-after-break)
                                           ))
                  ))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")

          (define break-context-concrete (concretize break-context sol))
          (displayln "Break context:")
          (displayln break-context-concrete)
             ; instead of concretizing state-after-break, instead run
             ; eval-statement-wait with the concretized context and state-after-prelude+
             #;(concretize state-after-break sol)
             (eval-statement-wait (max-fuel)
                                  (append-input-stream state-after-prelude+
                                                       break-context-concrete))
             )))

  #;(define state-after-break+ (test-break))
  #;(displayln "State after break:")
  #;(display-state state-after-break+)

#|
Produced break context (*null* (0,0))

state after break:

== PC: 106
== SP: 98
== Trace: (0 (0))
== Input stream: ((0 (0))) ; not empty?? This is because the *null* context
lowered max-iterations enough [which was 1 previously] but if it were in a
different context, the (0 0) input would have clinched it...

==Memory==
    99 |-> 0
    99 |-> 1
    98 |-> 0
    99 |-> 2
    99 |-> 3
    100 |-> ("main" (ASSIGN "max-iterations" 3))
    101 |-> ("main" (JMPZ (< 0 "max-iterations") 106))
    102 |-> ("main" (INPUT (& "x")))
    103 |-> ("main" (OUTPUT "x"))
    104 |-> ("main" (ASSIGN "max-iterations" (- "max-iterations" 1)))
    105 |-> ("main" (JMPZ 0 101))
    106 |-> ("main" HALT)

|#

  (define (test-simultaneously)
    (define sol
      (synthesize #:forall (list state-before-body state-before-break)
                  #:assume (assert (and (invariant-holds state-before-body)
                                        (invariant-holds state-before-break)
                                        ))
                  #:guarantee (assert (and (invariant-holds state-after-prelude)
                                           (invariant-holds state-after-body)
                                           (loop-body-spec state-before-body state-after-body)
                                           (not (invariant-holds state-after-break))
                                      ))
                  ))
    (if (unsat? sol)
        (displayln "Synthesis failed")
        (begin
          (displayln "Synthesis succeeded")

          (define-values (prelude-context-concrete
                          loop-context-concrete
                          break-context-concrete)
            (let ([contexts (concretize (list prelude-context loop-body-context break-context)
                                        sol)])
              (values (first contexts)
                      (second contexts)
                      (third contexts))))
          (displayln (format "Prelude context: ~a" prelude-context-concrete))
          (displayln (format "Loop context: ~a" loop-context-concrete))
          (displayln (format "Break context: ~a" break-context-concrete))

          ))
    )
  (test-simultaneously)





  )
(parameterize ([debug? #t])
  (time (synthesize-dispatch-gadgets)))
; Took around 4 minutes to synthesize all 3



;;;;;;;;;;;
;; Notes ;;
;;;;;;;;;;;

; Normal runtime: 3.6 min
; - invariant = loop guard = [max-iterations > 0]
; - loop body spec = [length (trace st2) = 1+length (trace st1)]
; - symbolic state created by first synthesizing preamble, then synthesizing
;   the symbolic invariant state based on the pc and sp of that synthesized preamble context,
;   with symbolic variables in the stack

; Variant with 2 iterations: 3.6 min
; - invariant = loop guard = [max-iterations > 0]
; - loop body spec = [length (trace st2) = **2**+length (trace st1)]
; - symbolic state created by first synthesizing preamble, then synthesizing
;   the symbolic invariant state based on the pc and sp of that synthesized preamble context,
;   with symbolic variables in the stack

; Variant with symbolic symbolic state: 2 hours
; - context max width = 2
; - invariant = loop guard = [max-iterations > 0 && pc = 201]
; - loop body spec = [length (trace st2) = 1+length (trace st1)]
; - symbolic state created by adding the appropriate number of symbolic
;   variables to the concrete program context produced by compile-echo
;
; This blows up the symbolic execution time because the contexts have max width
; 2, and we're starting from multiple possible pc states...

; Variant with symbolic symbolic state and max width 1: 4 min
; - context max width = 1
; - invariant = loop guard = [max-iterations > 0 && pc = 201]
; - loop body spec = [length (trace st2) = 1+length (trace st1)]
; - symbolic state created by adding the appropriate number of symbolic
;   variables to the concrete program context produced by compile-echo


; Variant where all 3 queries are synthesized in a single query: 3 min
; - context max width = 1

; Variant with symbolic invariant (invariant-holds(st) iff pc(st)=? as opposed to 82): 3 min
; - context max width = 1

; Variant with symbolic invariant (invariant-holds(st) iff pc(st)=? as opposed to 82): 4.5 hours
; - context max width = 2


; Variant with symbolic invariant (invariant-holds(st) iff pc(st)=? as opposed to 82): 10 min
; - context max width = 2
; - starting with only INPUT and HALT instructions, not including initial PC as well
; Prelude context: ((0 (2)) (0 (2284)))
; Loop context: ((0 (8367)))
; Break context: ((0 (0)))