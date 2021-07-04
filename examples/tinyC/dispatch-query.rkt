#lang seec
(require seec/private/util)
(require seec/private/monad)
(require "tinyC.rkt"
         "tinyC-test.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt")
(require (only-in racket/base
                  values
                  for))


(require rosette/lib/value-browser) ; debugging

(provide eval-statement-wait
         potential-pc-from-memory
         push-objs-symbolic
         evaluate-prepared-state
         prepare-invariant-state

         (struct-out dispatch-gadget)
         dispatch-spec-holds
         context->gadget
         context->prelude-gadget
         find-dispatch-gadgets
         find-dispatch-gadgets-debug

         tinyA-invariant
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

           (debug (thunk (display-memory mem+)))

           (tinyA:initial-state #:global-store g
                                #:pc pc
                                #:sp sp+
                                #:memory mem+
                                #:instructions echo-prog-in-memory
                                )
           )]
      ))



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

(define context->prelude-gadget
  (λ (compiled-prog
      ctx
      args
      )
    (match compiled-prog
      [(tinyA (g:global-store sp:stack-pointer mem:memory insns:insn-store))
    (context->gadget compiled-prog
                     ctx
                     #:spec (λ (st1 st2) #t)
                     #:state-before (tinyA:load-compiled-program
                                     g
                                     insns
                                     mem
                                     sp
                                     (list) ; Start out with empty input, ctx gets added later
                                     ; max number of iterations below--is this
                                     ; symbolic? This number doesn't matter as long
                                     ; as it doesn't disallow any of the input
                                     ; stream
                                     args
                                     ))])))

(define find-dispatch-gadgets
  (λ (#:prelude-gadget    prelude-gadget
      #:loop-body-gadgets body-gadgets
;      #:loop-body-gadget  body-gadget
      #:break-gadget      break-gadget
      #:loop-invariant    invariant-holds
      #:invariant-requires [invariant-requires (λ (st) #t)]
      )
    (define (invariant-holds-before g)
      (invariant-holds (dispatch-gadget-before g)))
    (define (invariant-requires-before g)
      (invariant-requires (dispatch-gadget-before g)))
    (define (invariant-holds-after g)
      (invariant-holds (dispatch-gadget-after g)))

    (define sol (synthesize
                 #:forall (cons (dispatch-gadget-before break-gadget)
                                (map dispatch-gadget-before body-gadgets)
                                )
                 #:assume (assert (and (andmap invariant-holds-before body-gadgets)
                                       (andmap invariant-requires-before body-gadgets)
                                       (invariant-holds-before break-gadget)
                                       (invariant-requires-before break-gadget)
                                       ))
                 #:guarantee (assert (and (invariant-holds-after prelude-gadget)
                                          (andmap invariant-holds-after body-gadgets)
                                          (andmap dispatch-spec-holds body-gadgets)
                                          (not (invariant-holds-after break-gadget))
                                          ))
                 ))
    (if (unsat? sol)
        (displayln "Dispatch gadget synthesis failed")
        (begin
          (displayln "Dispatch gadget synthesis succeeded")
          (define-values (prelude-context-concrete
                          loop-contexts-concrete
                          break-context-concrete)
            (let ([contexts (concretize (list (dispatch-gadget-context prelude-gadget)
                                              (map dispatch-gadget-context body-gadgets)
                                              (dispatch-gadget-context break-gadget)
                                              )
                                        sol)])
              (values (first contexts)
                      (second contexts)
                      (third contexts)
                      )))
          (displayln (format "Prelude context: ~a" prelude-context-concrete))
          (for ([ctx loop-contexts-concrete])
            (displayln (format "Loop context: ~a" ctx)))
          (displayln (format "Break context: ~a" break-context-concrete))
          ))))


(define find-dispatch-gadgets-debug
  (λ (compiled-prog
      #:prelude-gadget    prelude-gadget
      #:loop-body-gadgets body-gadgets
;      #:loop-body-gadget  body-gadget
      #:break-gadget      break-gadget
      #:loop-invariant    invariant-holds
      #:invariant-requires [invariant-requires (λ (st) #t)]
      )
    (define (invariant-holds-before g)
      (invariant-holds (dispatch-gadget-before g)))
    (define (invariant-requires-before g)
      (invariant-requires (dispatch-gadget-before g)))
    (define (invariant-holds-after g)
      (invariant-holds (dispatch-gadget-after g)))

    (define sol (synthesize
                 #:forall (list )
                 #:assume (assert #t)
                 #:guarantee (assert (and (andmap invariant-holds-before body-gadgets)
                                       (andmap invariant-requires-before body-gadgets)
                                       (invariant-holds-before break-gadget)
                                       (invariant-requires-before break-gadget)
                                       (not (and (invariant-holds-after prelude-gadget)
                                                 (andmap invariant-holds-after body-gadgets)
                                                 (andmap dispatch-spec-holds body-gadgets)
                                                 (not (invariant-holds-after break-gadget))
                                                 ))))
                 ))
    (if (unsat? sol)
        (displayln "Dispatch gadget debugging failed")
        (begin
          (displayln "Dispatch gadget debugging succeeded")
          (define-values (prelude-concrete
                          loops-concrete
                          break-concrete
                          )
            (let ([contexts (concretize (list prelude-gadget
                                              body-gadgets
                                              break-gadget
                                              )
                                        sol)])
              (values (first contexts)
                      (second contexts)
                      (third contexts)
                      )))

          (displayln "=====================")
          (displayln (format "Prelude context: ~a" (dispatch-gadget-context prelude-concrete)))
          (displayln (format "Prelude gadget before:"))
          (display-state (dispatch-gadget-before prelude-concrete))
          (displayln (format "Prelude gadget after:"))
          (display-state (dispatch-gadget-after prelude-concrete))

          (displayln (format "invariant-holds-after prelude: ~a" (invariant-holds-after prelude-concrete)))
          (displayln "")

          (for ([g loops-concrete])
            (displayln "=====================")
            (displayln (format "Loop context: ~a" (dispatch-gadget-context g)))
            (displayln (format "Loop gadget before:"))
            (display-state (dispatch-gadget-before g))
            (displayln (format "Loop gadget after:"))
            (display-state (dispatch-gadget-after g))
            (displayln (format "invariant-holds-before loop: ~a" (invariant-holds-before g)))
            (displayln (format "invariant-requires-before loop: ~a" (invariant-requires-before g)))
            (displayln (format "invariant-holds-after loop: ~a" (invariant-holds-after g)))
            (displayln (format "dispatch-spec-holds for loop: ~a" (dispatch-spec-holds g)))
            (displayln "")
            )

          (displayln "=====================")
          (displayln (format "Break context: ~a" (dispatch-gadget-context break-concrete)))
          (displayln (format "Break gadget before:"))
          (display-state (dispatch-gadget-before break-concrete))
          (displayln (format "Break gadget after:"))
          (display-state (dispatch-gadget-after break-concrete))
          (displayln (format "invariant-holds-before break: ~a" (invariant-holds-before break-concrete)))
          (displayln (format "invariant-requires-before break: ~a" (invariant-requires-before break-concrete)))
          (displayln (format "invariant-holds-after break: ~a" (invariant-holds-after break-concrete)))
          (displayln "")
          

          ))))


;; synthesizing invariants ;;


  (define-grammar tinyA-invariant #:extends syntax
    (conjunct ::= list<disjunct>)
    (disjunct ::= list<literal>)
    (literal  ::= boolean
                  (expr = expr)
                  (expr <> expr)
                  (expr < expr)
                  (PC   = integer)
                  )
    )
  (define (interpret-conjunct conj st)
    (andmap (λ (disj) (interpret-disjunct disj st)) (seec->list conj)))
  (define (interpret-disjunct disj st)
    (ormap (λ (lit) (interpret-literal lit st)) (seec->list disj)))
  (define (interpret-literal lit st)
    (match lit
      [(tinyA-invariant b:boolean) b]
      [(tinyA-invariant (e1:expr = e2:expr))
       (do v1 <- (tinyA:eval-expr e1 st)
           v2 <- (tinyA:eval-expr e2 st)
           (equal? v1 v2))]
      [(tinyA-invariant (e1:expr <> e2:expr))
       (do v1 <- (tinyA:eval-expr e1 st)
           v2 <- (tinyA:eval-expr e2 st)
           (not (equal? v1 v2)))]
      [(tinyA-invariant (e1:expr < e2:expr))
       (do v1 <- (tinyA:eval-expr e1 st)
           v2 <- (tinyA:eval-expr e2 st)
           (< v1 v2))]
      [(tinyA-invariant (PC = x:integer))
       (equal? (tinyA:state-pc st) x)]
      ))



      

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

  (define (symbolic-var+ felem)
    (match felem
      [(tinyA (x:var o:offset) x)]
      [(tinyA 

  (define (symbolic-var F)
    (match F
      [(tinyA (cons (x:var o:offset) nil))

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
