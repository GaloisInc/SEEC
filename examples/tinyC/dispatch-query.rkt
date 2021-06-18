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

(provide eval-statement-wait
         potential-pc-from-memory
         push-objs-symbolic
         evaluate-prepared-state
         prepare-invariant-state
         )

(use-contracts-globally #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluation variant used for loop dispatch gadgets ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define/contract (eval-statement-wait fuel st)
  (-> (or/c #f integer?) tinyA:state? (failure/c tinyA:state?))
  (debug-display "========================")
  (debug-display "(eval-statement-wait ~a)" fuel)

  (for*/all ([st st]
             [pc (tinyA:state-pc st) #:exhaustive]
             [insn (tinyA:pc->instruction pc (tinyA:state-instructions st))]
             [input (tinyA:state-input-buffer st)]
             )

  (debug-display "==eval-statement-wait pc: ~a [~a]==" pc insn)

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

  ; Push 'count' symbolic arguments onto memory at locations `l`, `l+1`, ..., `l+count-1`
  (define (push-objs-symbolic l count mem)
    (cond
      [(> count 0)
       (define-symbolic* symbolic-obj integer?)
       (seec-cons (tinyA (,l ,symbolic-obj))
                  (push-objs-symbolic (+ 1 l) (- count 1) mem))
       #;(let ([symbolic-obj (tinyA val 1)])
         #;(for/all ([obj symbolic-obj])
           (debug-display "Adding mapping ~a |-> ~a" l obj))
         (seec-cons (tinyA (,l ,symbolic-obj))
                    (push-objs-symbolic (+ 1 l) (- count 1) mem)))]
      [else mem]
      ))


  (define (push-objs-symbolic-from-frame sp F mem)
    (match F
      [(tinyA nil) mem]
      [(tinyA (cons (_:var o:offset) F+:frame))
       ; For regular variables, add a symbolic value
       (define-symbolic* symbolic-obj integer?)
       (seec-cons (tinyA (,(+ sp o) ,symbolic-obj))
                  (push-objs-symbolic-from-frame sp F+ mem))]
      [(tinyA (cons (_:var o:offset len:natural) F+:frame))
       ; For array variables, add a concrete pointer for the array, then
       ; symbolic values for values of the array

       (tinyA:store-mem (+ sp o) (+ 1 sp o)
                        (push-objs-symbolic (+ 1 sp o) len
                        (push-objs-symbolic-from-frame sp F+ mem)))]
      ))


  ; Append an input stream to that of an existing state
  (define (append-input-stream st new-input)
    (tinyA:update-state st
                        #:input-buffer (append (tinyA:state-input-buffer st)
                                               new-input)))


  ; new-input should be a racket list of seec-lists (the input stream)
  (define/contract (evaluate-prepared-state st new-input)
    (-> tinyA:state? (listof (curry seec-list-of? integer?)) (failure/c tinyA:state?))
    
    (do st <- (eval-statement-wait (max-fuel)
                         (append-input-stream st new-input)
                         )
        (debug-display "Done with eval-statement-wait")
        st))


  ; The pc is a symbolic union of the pc of any HALT
  ; instructions, and the pc of any INPUT instructions
  ; Modification: only include INPUT instructions, as HALT instructions will not
  ; be invariants in general
  (define/contract (potential-pc-from-memory prog)
    (-> tinyA-insn-store? (failure/c tinyA-program-counter?))
    (match prog
      ; For now, only consider INPUT PCs.
      #;[(tinyA (cons (l:loc (f:proc-name HALT)) m+:insn-store))
       (if (havoc!)
           l
           (potential-pc-from-memory m+))]
      [(tinyA (cons (l:loc (f:proc-name (INPUT _:expr))) m+:insn-store))
       (if (havoc!)
           l
           (potential-pc-from-memory m+))]
      [(tinyA (cons (l:loc (f:proc-name _:statement)) m+:insn-store))
       (potential-pc-from-memory m+)]
      [_ *fail*]
      ))

  ; The compiled program should be the result tinyC-compiler compilation
  ; 
  ; Note that the sp should be the same as the the initial state assuming that
  ; there are no calls or returns and the INPUT command can't reach the return sp.
  ;
  ; If the sp can become symbolic through calls to input and/or other DOP
  ; attacks, what then?
  ;
  ; If the sp is symbolic and there are calls/returns, may be a control flow problem
  (define (prepare-invariant-state compiled-program)
    (match compiled-program
      [(tinyA (g:global-store sp:stack-pointer mem:memory echo-prog-in-memory:insn-store))

       (do pc+ <- (potential-pc-from-memory echo-prog-in-memory)
           ; We don't have to add the initial pc back in because unless it's an
           ; INPUT or HALT, we won't halt on it
           pc <- pc+
           ;pc  <- (if (havoc!) init-pc pc+) ; make sure to add the initial pc back in
           
           ; How many symbolic variables do we need? Currently just ones in the
           ; current stack frame. Might need to be extended if (1) we have a
           ; call stack with calls and returns; or (2) if the prelude needs to
           ; write additional objects to memory
           F     <- (tinyA:pc->frame pc echo-prog-in-memory g)
           (debug-display "Got frame ~a" F)
           fsize <- (tinyA:frame-size F)
           sp+   <- (- sp fsize)
           (debug-display "sp+: ~a" sp+)
           (debug-display "fsize: ~a" fsize)
           ;mem+  <- (push-objs-symbolic (- sp fsize) fsize mem)
           mem+  <- (push-objs-symbolic-from-frame sp+ F mem)

           (display-memory mem+)

           (tinyA:initial-state #:global-store g
                                #:pc pc
                                #:sp sp+
                                #:memory mem+
                                #:instructions echo-prog-in-memory
                                )
           )]
      ))

