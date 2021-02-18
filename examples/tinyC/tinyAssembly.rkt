#lang seec
(require racket/contract)
(require "monad.rkt")
(require (file "tinyC.rkt"))
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
(require (only-in racket/string ; foramtting
                  string-join
                  ))
(require rosette/lib/value-browser) ; debugging

(provide tinyA
         tinyA-statement?
         tinyA-val?
         tinyA-loc?
         tinyA-offset?
         tinyA-object?
         tinyA-program-counter?
         tinyA-stack-pointer?
         tinyA-frame?
         tinyA-frame-elem?
         tinyA-memory?
         tinyA-mem-mapping?
         tinyA-global-store?
         tinyA-declaration?
         tinyA-trace?

         ; For functions that could potentially overlap with tinyC, add a
         ; "tinyA:" prefix
         (prefix-out tinyA: (combine-out
            store-mem
            declaration->pc
            (struct-out state)
            load-compiled-program
            eval-statement
            ))
         )


(define-grammar tinyA #:extends syntax

  ; Statements
  (statement   ::= 
      ; Assign the result of evaluating 'ex' to the l-value of 'lv'
      (ASSIGN lval expr)
      ; Invoke 'm' with the results of evaluating 'ex ...' as arguments
      (CALL proc-name list<expr>)
      ; Return to the previous call frame
      RETURN
      ; Stop evaluation of the current program
      HALT
      ; Jump to the statement at memory location 'i' if 'e' is zero
      (JMPZ expr loc)
      ; Outputs the value of 'ex' to the output log
      (OUTPUT expr)
      ; A no-op
      SKIP)

  ;;;;;;;;;;;;;
  ; Semantics ;
  ;;;;;;;;;;;;;

  ; Values are integers, interpreted either as an integer constant or an address
  ; in memory
  (val    ::= integer)
  (loc    ::= natural) ; All locations are values
  (offset ::= natural)

  ; A memory object is either an integer or a statement tagged with it's
  ; containing procedure 'm'
  (object       ::= val (proc-name statement))
  ; The program counter 'pc' and stack pointer 'sp' are natural numbers
  (program-counter ::= loc)
  (stack-pointer   ::= loc)

  ; A stack frame 'F' is a mapping from variables to locations
  (frame        ::= list<frame-elem>)
  ; A stack frame element is either a local variable 'x' at offset 'i'
  ; within the current stack frame or an array 'x' at offset 'i' with length 'n'.
  (frame-elem ::= (var offset) (var offset natural))

  ; A memory 'M' is a map from locations to objects
  (memory       ::= list<mem-mapping>)
  (mem-mapping  ::= (loc object))

  ; The global store 'G' is a map from procedure names 'm' to the address
  ; of the procedure's first statement and the procedure's stack frame layout
  (global-store ::= list<declaration>)
  (declaration  ::= (proc-name program-counter frame))

  ; An output trace 't' is a sequence of values
  (trace        ::= list<val>)

  )

;;;;;;;;;;;
;; State ;;
;;;;;;;;;;;

(struct state (global-store pc sp memory trace)
  #:transparent)

(define update-state
  (λ (st #:increment-pc [inc-pc #f]
         #:pc           [pc (if inc-pc
                                (+ 1 (state-pc st))
                                (state-pc st))]
         #:sp         [sp (state-sp st)]
         #:memory     [mem (state-memory st)]
         #:cons-trace [v #f]
         #:trace      [tr  (if v
                               (seec-cons v (state-trace st))
                               (state-trace st))]
         )
    (state (state-global-store st) pc sp mem tr)))
(define initial-state
  (λ (#:global-store G
      #:pc           pc
      #:sp           sp
      #:memory       mem
      )
    (state G pc sp mem seec-empty)))

;;;;;;;;;;;;;;;;;;;;;
;; Pretty printing ;;
;;;;;;;;;;;;;;;;;;;;;


(define (display-state st)
  (printf "== PC: ~a~n" (state-pc st))
  (printf "== SP: ~a~n" (state-sp st))
  (printf "== Trace: ~a~n" (state-trace st))

  (printf "~n==Memory==~n")
  (tinyC:display-memory (state-memory st))
  )

#;(display-state (state (tinyA nil)
                      0
                      0
                      (list->seec (list (tinyA (100 1))
                                        (tinyA (200 2))))
                      (tinyA nil)))


;;;;;;;;;;;;;;;;;;;
;; Memory access ;;
;;;;;;;;;;;;;;;;;;;

; Lookup the object at address 'l' in memory 'M'. If 'l' is not recorded in
; 'M', return 0. (Assume all memory is initialized to 0.)
(define/contract (lookup-mem l mem)
  (-> tinyA-loc? tinyA-memory? tinyA-object?)
  (match mem
    [(tinyA nil) 0]
    [(tinyA (cons (l+:loc obj+:object) m+:memory))
     (if (equal? l l+)
         obj+
         (lookup-mem l m+))]
    ))

; If l↦v occurs in mem for a value v, return v, otherwise return #f
(define/contract (loc->val l mem)
  (-> tinyA-loc? tinyA-memory? (or/c #f tinyA-val?))
  (match (lookup-mem l mem)
    [(tinyA v:val) v]
    [_ #f]))


;;;;;;;;;;;;;;;
;; Accessors ;;
;;;;;;;;;;;;;;;

(define/contract (declaration->proc-name d)
  (-> tinyA-declaration? syntax-proc-name?)
  (match d
    [(tinyA (p:proc-name _:program-counter _:frame)) p]
    ))
(define/contract (declaration->pc d)
  (-> tinyA-declaration? tinyA-program-counter?)
  (match d
    [(tinyA (_:proc-name pc:program-counter _:frame)) pc]
    ))
(define/contract (declaration->frame d)
  (-> tinyA-declaration? tinyA-frame?)
  (match d
    [(tinyA (_:proc-name _:loc f:frame)) f]
    ))

; Lookup the declaration associated with the procedure name in the global store
(define/contract (proc-name->declaration p g)
  (-> syntax-proc-name? tinyA-global-store? (or/c #f tinyA-declaration?))
  (match g
    [(tinyA nil) #f]
    [(tinyA (cons d:declaration g+:global-store))
     (if (equal? (declaration->proc-name d) p)
         d
         (proc-name->declaration p g+))]
    ))


; Fetch the instruction at the current PC. If the PC does not point to an
; instruction in memory, return #f
(define/contract (pc->instruction pc mem)
  (-> tinyA-program-counter? tinyA-memory? (or/c #f tinyA-statement?))
  (match (lookup-mem pc mem)
    [(tinyA (_:proc-name stmt:statement)) stmt]
    [_ #f]))

(define (state->instruction st)
  (pc->instruction (state-pc st) (state-memory st)))


; Fetch the procedure name that encompasses the current PC. If the PC does not
; point to an instruction in memory, return #f
(define/contract (pc->proc-name pc mem)
  (-> tinyA-program-counter? tinyA-memory? (or/c #f syntax-proc-name?))
  (match (lookup-mem pc mem)
    [(tinyA (p:proc-name _:statement)) p]
    [_ #f]))


; Look up the stack frame layout of the procedure that includes the currently
; executing statement. If the PC does not point to an instruction in memory,
; return #f
(define/contract (pc->frame pc mem g)
  (-> tinyA-program-counter? tinyA-memory? tinyA-global-store? (or/c #f tinyA-frame?))
  (do (<- p (pc->proc-name pc mem))
      (<- d (proc-name->declaration p g))
      (declaration->frame d)))
(define/contract (state->frame st)
  (-> state? (or/c #f tinyA-frame?))
  (pc->frame (state-pc st) (state-memory st) (state-global-store st)))


; Compute the size of a stack frame layout
(define/contract (frame-size F)
  (-> tinyA-frame? integer?)
  (match F
    [(tinyA nil) 0]
    [(tinyA (cons (y:var o:offset) F+:frame))
     (+ 1 (frame-size F+))]
    [(tinyA (cons (y:var o:offset len:natural) F+:frame))
     (+ 1 len (frame-size F+))]
    ))

;;;;;;;;;;;;;;;;;;;;;;;
;; Writing to memory ;;
;;;;;;;;;;;;;;;;;;;;;;;

; Store the sequence of values 'vs' at addresses 'l', 'l+1', ...
; If 'l' does not already occur in 'mem', insert it.
;
; Invariant: if 'mem' is sorted by key, then '(push-objs l vs mem)' should also be sorted by key.
;
; Note: the sorting aspect might be less than ideal for symbolic analysis
(define/contract (push-objs l objs mem)
  (-> tinyA-loc? (listof tinyA-object?) tinyA-memory? tinyA-memory?)
  (cond
    [(empty? objs) mem]
    [else
     (let ([obj   (first objs)]
           [objs+ (rest  objs)])
       (match mem
         [(tinyA nil) (seec-cons (tinyA (,l ,obj))
                                (push-objs (+ l 1) objs+ mem))]

         [(tinyA (cons (l+:loc obj+:object) mem+:memory))
          (cond
            ; Replace l↦obj+ with l↦obj
            [(= l l+) (seec-cons (tinyA (,l ,obj))
                                 (push-objs (+ 1 l) obj+ mem+))]
            ; Add l↦obj to beginning of the list and recurse with original mem,
            ; including l+↦obj+
            [(< l l+) (seec-cons (tinyA (,l ,obj))
                                 (push-objs (+ 1 l) objs+ mem))]
            ; Add l↦objs to mem+
            [else     (seec-cons (tinyA (,l+ ,obj+))
                                 (push-objs l objs mem+))]
          )]
       ))]
    ))

; Update the value at memory location 'l', returning the updated memory. If 'l'
; does not already occur in m, insert it.
;
; Invariant: If m is sorted by key, then (store-mem l obj m) is also sorted by key
;
; Note: the sorting factor might be less than ideal for symbolic analysis
(define/contract (store-mem l obj mem)
  (-> tinyA-loc? tinyA-object? tinyA-memory? tinyA-memory?)
  (push-objs l (list obj) mem))


; Initialize the locations in a stack frame that refer to arrays
(define/contract (init-frame-arrays F sp mem)
  (-> tinyA-frame? tinyA-stack-pointer? tinyA-memory? tinyA-memory?)
  (match F
    [(tinyA nil) mem]
    [(tinyA (cons (_:var _:offset) F+:frame))
     (init-frame-arrays F+ sp mem)]
    [(tinyA (cons (x:var o:offset len:natural) F+:frame))
     (store-mem (+ sp o) (+ 1 sp o) (init-frame-arrays F+ sp mem))]
    ))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluating expressions ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Compute the address of the variable 'x' from the stack frame layout and the
; current stack pointer
(define/contract (lookup-var x sp F)
  (-> syntax-var? tinyA-stack-pointer? tinyA-frame? (or/c #f tinyA-loc?))
  (match F
    [(tinyA nil) #f]
    [(tinyA (cons (y:var o:offset)             F+:frame))
     (if (equal? x y)
         (+ sp o)
         (lookup-var x sp F+))]
    [(tinyA (cons (y:var o:offset len:natural) F+:frame))
     (if (equal? x y)
         (+ sp o)
         (lookup-var x sp F+))]
    ))

(define/contract (eval-lval-F lv sp F mem)
  (-> syntax-lval? tinyA-stack-pointer? tinyA-frame? tinyA-memory?
      (or/c #f tinyA-val?))
  (match lv
    [(tinyA x:var)
     (lookup-var x sp F)]
    [(tinyA (* lv+:lval))
     (do (<- l (eval-lval-F lv+ sp F mem))
         (loc->val l mem))]
    ))
; Produce the value associated with the lvalue
(define/contract (eval-lval lv st)
  (-> syntax-lval? state? (or/c #f tinyA-val?))
  (do (<- F (state->frame st))
      (eval-lval-F lv (state-sp st) F (state-memory st))))


(define/contract (eval-expr-F e sp F mem)
  (-> syntax-expr? tinyA-stack-pointer? tinyA-frame? tinyA-memory?
      (or/c #f tinyA-val?))
  (match e
    [(tinyA n:integer) n]
    [(tinyA null)      0]
    [(tinyA (* e+:expr))
     (do (<- l (eval-expr-F e+ sp F mem))
         (loc->val l mem))]
    [(tinyA x:var)
     (do (<- l (lookup-var x sp F))
         (loc->val l mem))]
    [(tinyA (& lv:lval))
     (eval-lval-F lv sp F mem)]
    [(tinyA (op:binop e1:expr e2:expr))
     (do (<- v1 (eval-expr-F e1 sp F mem))
         (<- v2 (eval-expr-F e2 sp F mem))
       ((binop->racket op) v1 v2))]
    ))
; Note that the helper function eval-expr-F exists because (state->frame st)
; does a lookup to find the corresponding frame in the global store, and we
; don't want to have to replicate that lookup every time we encounter a variable
; in the expression. Same for eval-lval vs eval-lval-F.
(define (eval-expr e st)
  (do (<- F (state->frame st))
      (eval-expr-F e (state-sp st) F (state-memory st))))
(define/contract (eval-exprs es st)
  (-> (listof syntax-expr?) state? (or/c #f (listof tinyA-val?)))
  (let* ([vs-maybe (map (λ (e) (eval-expr e st))
                        es)])
    (if (andmap (λ (x) x) vs-maybe)
        vs-maybe
        #f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluation of statements ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/contract (eval-statement-1 g st)
  (-> tinyA-global-store? state? state?)

  (match (state->instruction st)
    [(tinyA SKIP)
     (update-state st #:increment-pc #t)]

    [(tinyA (OUTPUT e:expr))
     (do (<- v (eval-expr e st))
         (update-state st
                       #:increment-pc #t
                       #:cons-trace v)
       )]

    [(tinyA (JMPZ e:expr l:loc))
     (match (eval-expr e st)
       [(tinyA 0) (update-state st #:pc l)]
       [_         (update-state st #:increment-pc #t)]
       )]

    [(tinyA (ASSIGN lv:lval e:expr))
     (do (<- l (eval-lval lv st))
         (<- v (eval-expr e  st))
         (update-state st
                       #:increment-pc #t
                       #:memory (store-mem l v (state-memory st))
                       ))]

    [(tinyA HALT) #f] ; cannot take a step

    [(tinyA (CALL p:proc-name es:list<expr>))
         ; Evaluate the arguments
     (do (<- vs (eval-exprs (seec->list es) st))
         ; lookup the target procedure's address and layout
         (<- d2 (proc-name->declaration p g))
         (let* ([sp1 (state-sp st)]
                [pc1 (state-pc st)]
                [m1  (state-memory st)]
                [F2  (declaration->frame d2)]
                [pc2 (declaration->pc d2)]
                ; Compute the new stack pointer by subtracting the size of the
                ; frame F2 from the current stack pointer, with two additional
                ; slots for return address and saved (current) stack pointer
                [sp2 (- sp1 (frame-size F2) 2)]
                ; Set up the new stack frame by initializing the local variables and pushing
                ; call arguments, return address, and stack pointer into the new frame
                [m2+  (push-objs (- sp1 (length vs) 2)
                                 (append vs (list sp1 (+ 1 pc1)))
                                 (state-memory st))]
                [m2   (init-frame-arrays F2 sp2 m2+)]
                )
           (update-state st
                         #:pc pc2
                         #:sp sp2
                         #:memory m2)))]

    [(tinyA RETURN)
         ; Get the current frame layout
     (do (<- F1 (state->frame st))
         ; Locate the return address on the stack by adding the frame size to
         ; the current stack pointer and adding 1
         (<- pc2 (lookup-mem (+ (state-sp st) (frame-size F1) 1) (state-memory st)))
         ; Locate the old stack pointer value by adding the frame size of the
         ; current stack pointer
         (<- sp2 (lookup-mem (+ (state-sp st) (frame-size F1)) (state-memory st)))
         ; No garbage collection
         (update-state st
                       #:pc pc2
                       #:sp sp2))]

    ))

; Take some number of states bounded by the amount of fuel given
(define/contract (eval-statement fuel st)
  (-> (or/c #f integer?) state? (or/c #f state?))
  (cond
    [(equal? (state->instruction st)
             (tinyA HALT))
     st] ; Evaluation has normalized before fuel ran out

    [(<= fuel 0) st] ; Fuel ran out. Return #f here instead?

    [else 
     (do (<- st+ (eval-statement-1 (state-global-store st) st))
         (eval-statement (decrement-fuel fuel) st+))]
    ))



; Given a memory with a compiled program, initialize the stack at 'i_s' and
; invoke 'main' with arguments 'v ...'
(define/contract (load-compiled-program G mem sp vals)
  (-> tinyA-global-store? tinyA-memory? tinyA-stack-pointer? (listof tinyA-val?)
      (or/c #f state?)
      )
  (do (<- decl (proc-name->declaration (string "main") G))
      (<- mem+ (push-objs (- sp (length vals)) vals mem))
      (<- sp+  (- sp (frame-size (declaration->frame decl))))
      (initial-state #:global-store G
                     #:pc           (declaration->pc decl)
                     #:sp           sp+
                     #:memory       mem+)
      ))

; Load a high-level program into memory at init-pc, initialize the stack at
; init-sp, and invoke main with arguments vs
#;(define/contract (load prog init-pc init-sp vs)
  (-> tinyC:tinyC-program? tinyA-program-counter? tinyA-stack-pointer?
      (listof tinyA-val?)
      program?)
  ())
  

#;(define run
  (λ #:fuel [fuel #f]
     ))
