#lang seec
(require seec/private/util)
(require seec/private/monad)
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
         tinyA+
         tinyA-lang

         tinyA-statement?
         tinyA-val?
         tinyA-loc?
         tinyA-offset?
         #;tinyA-object?
         tinyA-insn-store?
         tinyA-program-counter?
         tinyA-stack-pointer?
         tinyA-frame?
         tinyA-frame-elem?
         tinyA-memory?
         tinyA-mem-mapping?
         tinyA-global-store?
         tinyA-declaration?
         tinyA-trace?
         tinyA+-expr?
         tinyA+-ctx?


         ; pretty printing
         display-state
         (rename-out [tinyC:display-memory display-memory])
         display-tinyA-lang-expression
         display-tinyA-lang-context

         ; For functions that could potentially overlap with tinyC, add a
         ; "tinyA:" prefix
         (prefix-out tinyA: (combine-out
            store-mem
            store-insn-sorted
            lookup-mem
            #;naive-lookup-mem
            declaration->pc
            declaration->frame
            (struct-out state)
            update-state
            load-compiled-program
            eval-statement-1
            eval-statement
            eval-expr
            frame-size
            pc->instruction
            pc->frame
            proc-name->declaration
            initial-state

            HALT?
            INPUT?

            ))
         )

; Can turn off contracts for definitions defined in this module
(use-contracts-globally #t)

(define-grammar tinyA #:extends syntax

  ; Statements
  (statement   ::= 
      ; Assign the result of evaluating 'ex' to the l-value of 'lv'
      (ASSIGN expr expr)
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
      ; Given a pointer to a buffer in memory, accept input from the environment
      ; and write to the buffer
      (INPUT expr)
      ;A no-op
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
  #;(object       ::= val (proc-name statement))
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
  (mem-mapping  ::= (loc val #;object))

  (insn-store   ::= list<insn-mapping>)
  (insn-mapping ::= (loc insn-object))
  (insn-object  ::= (proc-name statement))

  ; The global store 'G' is a map from procedure names 'm' to the address
  ; of the procedure's first statement and the procedure's stack frame layout
  (global-store ::= list<declaration>)
  (declaration  ::= (proc-name program-counter frame))

  ; An output trace 't' is a sequence of values
  (trace        ::= list<val>)

  )


(define (pp-frame-elem elem)
  (match elem
    [(tinyA (x:var o:offset))
     (format "~a @ ~a" x o)]
    [(tinyA (x:var o:offset n:natural))
     (format "~a[~a] @ ~a" x n o)]
    ))
(define (pp-frame F)
  (map pp-frame-elem (seec->list F)))
; Produce a list of strings
(define (pp-declaration decl)
  (match decl
    [(tinyA (p:proc-name pc:program-counter F:frame))
     (append (list (format "~a [~a]: " pc (string->racket p)))
             (map indent-string (pp-frame F))
             )]
    ))
(define (display-declaration decl)
  (displayln (string-join (pp-declaration decl)
                          (format "~n"))))
(define (display-global-store g)
  (andmap display-declaration (seec->list g)))

;;;;;;;;;;;
;; State ;;
;;;;;;;;;;;

; The input-buffer is a (racket) list of 'input-list's that are fed to calls to
; INPUT. This is a simple interaction model that can react dynamically to the
; program execution in a simple way.
;
; Note: making this struct `transparent` leads to less reliable union splitting
; behavior.
;
; Adding a separate memory for instructions to keep them separate
(struct state (global-store pc sp memory instructions input-buffer trace))
(define/contract (state->memory st)
  (-> state? tinyA-memory?)
  (state-memory st))

(define update-state
  (λ (st #:increment-pc [inc-pc #f] ; If the pc has already been abstracted
                                    ; over, we don't want to use increment-pc
         #:pc           [pc (if inc-pc
                                (+ 1 (state-pc st))
                                (state-pc st))]
         #:sp           [sp (state-sp st)]
         #:memory       [mem (state-memory st)]
         #:instructions [insns (state-instructions st)]
         #:snoc-trace   [v #f]
         #:input-buffer [buf (state-input-buffer st)]
         #:trace        [tr  (if v
                                 (seec-append (state-trace st) (seec-singleton v))
                                 (state-trace st))]
         )
    (state (state-global-store st) pc sp mem  insns buf tr)))
(define initial-state
  (λ (#:global-store G
      #:pc           pc
      #:sp           sp
      #:instructions insns
      #:memory       mem
      #:input-buffer [buf (list )]
      )
    (state G pc sp mem insns buf seec-empty)))

;;;;;;;;;;;;;;;;;;;;;
;; Pretty printing ;;
;;;;;;;;;;;;;;;;;;;;;


(define/contract (display-state st)
  (-> state? any/c)
  (printf "== PC: ~a~n" (state-pc st))
  (printf "== SP: ~a~n" (state-sp st))
  (printf "== Trace: ~a~n" (state-trace st))

  (printf "== Input stream: ~a~n" (state-input-buffer st))

  (printf "~n==Global store==~n")
  (display-global-store (state-global-store st))

  (printf "~n==Memory==~n")
  (tinyC:display-memory (state-memory st))

  (printf "~n==Instructions==~n")
  (tinyC:display-memory (state-instructions st))

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

(define (lookup-in-map l mem default)
  (for*/all ([l l #:exhaustive]
             [mem mem]) ; Both these for/all clauses are important to make sure
                        ; the output of this function is a concise union, and not too large
    (match mem
    [(tinyA nil) default]
    [(tinyA (cons (l+:loc obj+:any) m+:any))
     (for/all ([l+ l+ #:exhaustive])
       (if (equal? l l+)
           obj+
           (lookup-in-map l m+ default)))]
     )))

; Lookup the object at address 'l' in memory 'M'. If 'l' is not recorded in
; 'M', return 0. (Assume all memory is initialized to 0.)
(define/contract (lookup-mem l mem)
  (-> tinyA-loc? tinyA-memory? tinyA-val?)
  (lookup-in-map l mem 0)
  )

; Produces a pair of a proc-name and statement
(define/contract (lookup-insn l mem)
  (-> tinyA-loc? tinyA-insn-store? (failure/c tinyA-insn-object?))
  (lookup-in-map l mem *fail*))

#;(define/contract (naive-lookup-mem l mem)
  (-> tinyA-loc? tinyA-memory? tinyA-object?)
    (match mem
    [(tinyA nil) 0]
    [(tinyA (cons (l+:loc obj+:object) m+:memory))
       (if (equal? l l+)
           obj+
           (naive-lookup-mem l m+))]
     ))


; If l↦v occurs in mem for a value v, return v, otherwise return *fail*
(define/contract (loc->val l mem)
  (-> tinyA-loc? tinyA-memory? (failure/c tinyA-val?))
  (match (lookup-mem l mem)
    [(tinyA v:val) v]
    [_ *fail*]))


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
  (-> syntax-proc-name? tinyA-global-store? (failure/c tinyA-declaration?))
  (match g
    [(tinyA nil) *fail*]
    [(tinyA (cons d:declaration g+:global-store))
     (if (equal? (declaration->proc-name d) p)
         d
         (proc-name->declaration p g+))]
    ))


; Fetch the instruction at the current PC. If the PC does not point to an
; instruction in memory, return *fail*
(define/contract (pc->instruction pc insn-store)
  (-> tinyA-program-counter? tinyA-insn-store? (failure/c tinyA-statement?))
  #;(debug-display "(pc->instruction ~a) in the following memory..." pc)
  #;(debug (thunk (tinyC:display-memory insn-store)))
  (match (lookup-insn pc insn-store)
    [(tinyA (_:proc-name stmt:statement)) stmt]
    [_ *fail*]))

(define/contract (state->instruction st)
  (-> state? (failure/c tinyA-statement?))
  (pc->instruction (state-pc st) (state-instructions st)))


(define/contract (state->pc-declaration st)
    (-> state? (failure/c tinyA-declaration?))
    (match (lookup-insn (state-pc st) (state-instructions st))
      [(tinyA (f:proc-name _:statement))
       (proc-name->declaration f (state-global-store st))]
      [_ *fail*]
      ))

; Fetch the procedure name that encompasses the current PC. If the PC does not
; point to an instruction in memory, return *fail*
(define/contract (pc->proc-name pc insn-store)
  (-> tinyA-program-counter? tinyA-insn-store? (failure/c syntax-proc-name?))
  (match (lookup-insn pc insn-store)
    [(tinyA (p:proc-name _:statement)) p]
    [_ *fail*]))


; Look up the stack frame layout of the procedure that includes the currently
; executing statement. If the PC does not point to an instruction in memory,
; return *fail*
(define/contract (pc->frame pc insn-store g)
  (-> tinyA-program-counter? tinyA-insn-store? tinyA-global-store? (failure/c tinyA-frame?))
  (do (<- p (pc->proc-name pc insn-store))
      (<- d (proc-name->declaration p g))
      (declaration->frame d)))
(define/contract (state->frame st)
  (-> state? (failure/c tinyA-frame?))
  (pc->frame (state-pc st) (state-instructions st) (state-global-store st)))


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


(define (HALT? insn)
  (equal? insn (tinyA HALT)))
(define (INPUT? insn)
  (match insn
    [(tinyA (INPUT expr)) #t]
    [_                    #f]))

;;;;;;;;;;;;;;;;;;;;;;;
;; Writing to memory ;;
;;;;;;;;;;;;;;;;;;;;;;;

; Store the sequence of values 'vs' at addresses 'l', 'l+1', ...
; If 'l' does not already occur in 'mem', insert it.
;
; Invariant: if 'mem' is sorted by key, then '(push-objs l vs mem)' should also be sorted by key.
;
; Note: the sorting aspect might be less than ideal for symbolic analysis
(define (push-objs-sorted l objs mem)
  ;(-> tinyA-loc? (listof tinyA-object?) tinyA-memory? tinyA-memory?)
  (cond
    [(empty? objs) mem]
    [else
     (let ([obj   (first objs)]
           [objs+ (rest  objs)])
       (match mem
         [(tinyA nil) (seec-cons (tinyA (,l ,obj))
                                (push-objs-sorted (+ l 1) objs+ mem))]

         [(tinyA (cons (l+:loc obj+:any) mem+:any))
          (cond
            ; Replace l↦obj+ with l↦obj
            [(= l l+) (seec-cons (tinyA (,l ,obj))
                                 (push-objs-sorted (+ 1 l) obj+ mem+))]
            ; Add l↦obj to beginning of the list and recurse with original mem,
            ; including l+↦obj+
            [(< l l+) (seec-cons (tinyA (,l ,obj))
                                 (push-objs-sorted (+ 1 l) objs+ mem))]
            ; Add l↦objs to mem+
            [else     (seec-cons (tinyA (,l+ ,obj+))
                                 (push-objs-sorted l objs mem+))]
          )]
       ))]
    ))

; Unsorted simpler version, possibly better for symbolic analysis
(define (push-objs l objs mem)
  (-> tinyA-loc? (listof tinyA-val?) tinyA-memory? tinyA-memory?)
  (for*/all ([l l #:exhaustive]
             [objs objs]
             [mem mem])
  #;(debug-display "(push-objs ~a ~a)" l objs)
  (cond
    [(empty? objs) mem]
    [else
     (let ([obj   (first objs)]
           [objs+ (rest  objs)])
       (seec-cons (tinyA (,l ,obj))
                  (push-objs (+ 1 l) objs+ mem))
       ; The sorted version below only works if the stack is in order, which is
       ; not true currently based on the stack. Maybe that can be fixed.
       #;(match mem
         [(tinyA nil) (seec-cons (tinyA (,l ,obj))
                                (push-objs (+ 1 l) objs+ mem))]

         [(tinyA (cons (l+:loc obj+:object) mem+:memory))
          (cond
            ; Replace l↦obj+ with l↦obj
            [(equal? l l+) (seec-cons (tinyA (,l ,obj))
                                      (push-objs (+ 1 l) objs+ mem+))]
            ; Add l↦obj to beginning of the list and recurse with original mem,
            ; including l+↦obj+
            ;
            ; NOTE: only do this if l+ has no symbolic variables
            #;[(and (not (symbolic? l+))
                  (< l l+))
             (seec-cons (tinyA (,l ,obj))
                        (push-objs (+ 1 l) objs+ mem))]

            ; Add l↦objs to mem+
            [else     (seec-cons (tinyA (,l+ ,obj+))
                                 (push-objs l objs mem+))]
          )]
       ))]
    )))


; Update the value at memory location 'l', returning the updated memory. If 'l'
; does not already occur in m, insert it.
;
; Invariant: If m is sorted by key, then (store-mem l obj m) is also sorted by key
;
; Note: the sorting factor might be less than ideal for symbolic analysis
(define/contract (store-mem l obj mem)
  (-> tinyA-loc? tinyA-val? tinyA-memory? tinyA-memory?)
  (push-objs l (list obj) mem))
(define (store-insn-sorted l obj mem)
  (-> tinyA-loc? tinyA-insn-object? tinyA-insn-store? tinyA-insn-store?)
  (push-objs-sorted l (list obj) mem))



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
  (-> syntax-var? tinyA-stack-pointer? tinyA-frame? (failure/c tinyA-loc?))
  (match F
    [(tinyA nil) *fail*]
    [(tinyA (cons (y:var o:offset)             F+:frame))
     (if (equal? x y)
         (+ sp o)
         (lookup-var x sp F+))]
    [(tinyA (cons (y:var o:offset len:natural) F+:frame))
     (if (equal? x y)
         (+ sp o)
         (lookup-var x sp F+))]
    ))

#;(define/contract (eval-lval-F lv sp F mem)
  (-> syntax-lval? tinyA-stack-pointer? tinyA-frame? tinyA-memory?
      (failure/c tinyA-val?))
  (match lv
    [(tinyA x:var)
     (lookup-var x sp F)]
    [(tinyA (* lv+:lval))
     (do (<- l (eval-lval-F lv+ sp F mem))
         (loc->val l mem))]
    ))
; Produce the value associated with the lvalue
#;(define/contract (eval-lval lv st)
  (-> syntax-lval? state? (failure/c tinyA-val?))
  (do (<- F (state->frame st))
      (eval-lval-F lv (state-sp st) F (state-memory st))))

(define/contract (eval-address-F e sp F mem)
  (-> syntax-expr? tinyA-stack-pointer? tinyA-frame? tinyA-memory?
      (failure/c tinyA-val?))
  (match e
    [(tinyA x:var)
     (lookup-var x sp F)]

    [(tinyA (* e+:expr))
     (do (<- l (eval-address-F e+ sp F mem))
         (loc->val l mem))]

    [(tinyA (arr:expr [idx:expr]))
     #;(match (cons (eval-address-F arr sp F mem)
                  (eval-expr-F idx sp F mem))
       [(cons (tinyA l:loc) (tinyA o:offset))
        (+ l o)]
       )
     (do arr-loc   <- (eval-address-F arr sp F mem)
        ; First look up the location of the array
         arr-start <- (lookup-mem arr-loc mem)
         offset    <- (eval-expr-F idx sp F mem)
        ; The modified address is the index of the offset into the array
         (+ arr-start offset)
         )
     ]

    [_ *fail*]

    ))
; Produce the value associated with the lvalue
(define/contract (eval-address e st)
  (-> syntax-expr? state? (failure/c tinyA-val?))
  (do (<- F (state->frame st))
      (eval-address-F e (state-sp st) F (state-memory st))))



(define/contract (eval-expr-F e sp F mem)
  (-> syntax-expr? tinyA-stack-pointer? tinyA-frame? tinyA-memory?
      (failure/c tinyA-val?))
  (match e
    [(tinyA n:integer) n]
    [(tinyA null)      0]
    [(tinyA (* e+:expr))
     (do (<- l (eval-expr-F e+ sp F mem))
         (loc->val l mem))]
    [(tinyA x:var)
     (do (<- l (lookup-var x sp F))
         (loc->val l mem))]
    [(tinyA (& e+:expr))
     (eval-address-F e+ sp F mem)]
    [(tinyA (op:binop e1:expr e2:expr))
     (do (<- v1 (eval-expr-F e1 sp F mem))
         (<- v2 (eval-expr-F e2 sp F mem))
       ((binop->racket op) v1 v2))]
    [(tinyA (arr:expr[idx:expr]))
     (do arr-loc   <- (eval-address-F arr sp F mem)
        ; First look up the location of the array
         arr-start <- (lookup-mem arr-loc mem)
         offset    <- (eval-expr-F idx sp F mem)
        ; Then look up the value at that address plus the offset
         (lookup-mem (+ arr-start offset) mem)
         )

     #;(match (cons (eval-address-F arr sp F mem)
                  (eval-expr-F idx sp F mem))
       [(cons (tinyA l:loc) (tinyA o:offset))
        ; First look up the location of the array
        ; Then look up the value at that address plus the offset
        (loc->val (+ l o) mem)]
       )]
    ))
; Note that the helper function eval-expr-F exists because (state->frame st)
; does a lookup to find the corresponding frame in the global store, and we
; don't want to have to replicate that lookup every time we encounter a variable
; in the expression. Same for eval-lval vs eval-lval-F.
(define/contract (eval-expr e st)
  (-> syntax-expr? state? (failure/c tinyA-val?))
  (do (<- F (state->frame st))
      (eval-expr-F e (state-sp st) F (state-memory st))))
(define/contract (eval-exprs es st)
  (-> (listof syntax-expr?) state? (failure/c (listof tinyA-val?)))

  (cond
    [(empty? es) (list)]
    [else (do v <- (eval-expr (first es) st)
              vs <- (eval-exprs (rest es) st)
              (cons v vs))]
    )
  #;(let* ([vs-maybe (map (λ (e) (eval-expr e st))
                        es)])
    (if (any-failure? vs-maybe)
        *fail*
        vs-maybe
        )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluation of statements ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define/contract (input-list->intlist vs output)
  (-> syntax-input-list? tinyA-trace? (listof integer?))
  (match vs
    [(tinyA nil) (list)]
    [(tinyA (cons i:integer vs+:input-list))
     (cons i (input-list->intlist vs+ output))]
    [(tinyA (cons (TRACE o:natural) vs+:input-list))
     (cons (seec-ith o output) (input-list->intlist vs+ output))]
    ))

; The true value represents a HALT
(define/contract (eval-statement-1 #;insn st)
  (-> #;tinyA-statement? state? (failure/c (or/c #t state?)))

  ; Use for/all here first abstracts the pc
  (for*/all ([pc (state-pc st) #:exhaustive]
             [insn (pc->instruction pc (state-instructions st))]
             )
  (debug-display "(eval-statement-1 ~a ~a)" pc insn)

  (match insn

    [(tinyA HALT) #t]

    [(tinyA SKIP)
     (update-state st ;#:increment-pc #t
                   #:pc (+ pc 1)
                   )]

    [(tinyA (OUTPUT e:expr))
     (do (<- v (eval-expr e st))
         (update-state st
;                       #:increment-pc #t
                       #:pc (+ pc 1)
                       #:snoc-trace v)
       )]

    [(tinyA (INPUT e:expr))
     (for/all ([input (state-input-buffer st)])
       #;(debug-display "=====================================")
       #;(debug-display "=====================================")
       (debug-display "=====================================")
       (debug-display "Got input: ~a" input)
       #;(debug (thunk (display-state st)))

       (cond
         [(and (list? input) (not (empty? input)))
          (do (<- l (eval-expr e st)) ; e should evaluate to a location
            #;(debug-display "~a evaluates to ~a" e l)
            #;(debug (thunk (display-state st)))
            (<- is (input-list->intlist (first input) (state-trace st)))
            (<- m+ (push-objs l is (state-memory st)))
            #;(debug-display "New memory:")
            #;(debug (thunk (tinyC:display-memory m+)))
            (update-state st
                            #:memory m+
                            #:input-buffer (rest input)
;                            #:increment-pc #t
                            #:pc (+ pc 1)
                            ))]
         [else *fail*]
         ))]

    [(tinyA (JMPZ e:expr l:loc))
     (match (eval-expr e st)
       [(tinyA 0) (update-state st #:pc l)]
       [_         (update-state st ;#:increment-pc #t
                                #:pc (+ pc 1)
                                )]
       )]

    [(tinyA (ASSIGN x:expr e:expr))
     (do (<- l (eval-address x st))
         (<- v (eval-expr e  st))
         (update-state st
;                       #:increment-pc #t
                       #:pc (+ pc 1)
                       #:memory (store-mem l v (state-memory st))
                       ))]

    #;[(tinyA HALT) *fail*] ; cannot take a step

    [(tinyA (CALL p:proc-name es:list<expr>))
     #;(render-value/window p)

         ; Evaluate the arguments
     (do (<- vs (eval-exprs (seec->list es) st))
         ; lookup the target procedure's address and layout
         (<- d2 (proc-name->declaration p (state-global-store st)))
         (debug-display "Got d2: ~a" d2)
         (let* ([sp1 (state-sp st)]
                [x   (debug-display "Got sp1: ~a" sp1)]
                [pc1 pc #;(state-pc st)]
                [x   (debug-display "Got pc1: ~a" pc1)]
                #;[m1  (state-memory st)]
                #;[x   (debug-display "m1: ~a" m1)]
                #;[x   (tinyC:display-memory m1)]
                [F2  (declaration->frame d2)]
                [x   (debug-display "Got F2: ~a" F2)]
                [pc2 (declaration->pc d2)]
                [x   (debug-display "Got pc2: ~a" pc2)]
                ; Compute the new stack pointer by subtracting the size of the
                ; frame F2 from the current stack pointer, with two additional
                ; slots for return address and saved (current) stack pointer
                [sp2 (- sp1 (frame-size F2) 2)]
                [x   (debug-display "Got sp2: ~a" sp2)]
                ; Set up the new stack frame by initializing the local variables and pushing
                ; call arguments, return address, and stack pointer into the new frame
                [m2+  (push-objs (- sp1 (length vs) 2)
                                 (append vs (list sp1 (+ 1 pc1)))
                                 (state->memory st))]
                [m2   (init-frame-arrays F2 sp2 m2+)]
                [x    (debug (thunk (tinyC:display-memory m2)))]
                )
           (update-state st
                         #:pc pc2
                         #:sp sp2
                         #:memory m2)))]

    [(tinyA RETURN)
     (for/all ([sp1 (state-sp st) #:exhaustive]) ; This for/all helps concretize
                                                ; pc2, which depends on sp
         #;(debug-display "Got sp1: ~a" sp1)
         ; Get the current frame layout
     (do (<- F1 (pc->frame pc (state-instructions st) (state-global-store st)))
         #;(debug-display "Got F1: ~a" F1)
         ; Locate the return address on the stack by adding the frame size to
         ; the current stack pointer and adding 1
         #;(debug-display "Looking for pc2 at location: ~a" (+ sp1 (frame-size F1) 1))
         (<- pc2 (lookup-mem (+ sp1 (frame-size F1) 1) (state-memory st)))
         #;(debug-display "Got pc2: ~a" pc2)
         ; Locate the old stack pointer value by adding the frame size of the
         ; current stack pointer
         #;(debug-display "Looking for sp2 at location: ~a" (+ sp1 (frame-size F1)))
         (<- sp2 (lookup-mem (+ sp1 (frame-size F1)) (state-memory st)))
         #;(debug-display "Got sp2: ~a" sp2)
         ; No garbage collection
         (update-state st
                       #:pc pc2
                       #:sp sp2)))]

    )))

(define (CALL? insn)
  (match insn
    [(tinyA (CALL any any)) #t]
    [_ #f]))


; Take some number of states bounded by the amount of fuel given
(define/contract (eval-statement fuel st)
  (-> (or/c #f integer?) state? (failure/c state?))
  (debug-display "(eval-statement ~a)" fuel)

  (for/all ([st st])

  (do st+   <- (eval-statement-1 st)
      (cond
        [(equal? st+ #t) ; This means the instruction halted with HALT
         st]
        [(<= fuel 0)
         *fail*] ; Fuel ran out. Return st here instead?
        [else
         (eval-statement (decrement-fuel fuel) st+)]
        ))))



; Given a memory with a compiled program, initialize the stack at 'i_s' and
; invoke 'main' with arguments 'v ...' and with an input buffer 'buf' (racket
; list of tinyA-list<integer>)
(define/contract (load-compiled-program G insns mem sp buf vals)
  (-> tinyA-global-store? tinyA-insn-store? tinyA-memory? tinyA-stack-pointer? list? (listof tinyA-val?)
      (failure/c state?)
      )
  (do (<- decl (proc-name->declaration (string "main") G))
      (<- mem+ (push-objs (- sp (length vals)) vals (tinyA nil)))
      (<- F    (declaration->frame decl))
      (<- sp+  (- sp (frame-size F)))
      (<- mem++ (init-frame-arrays F sp+ mem+))
      (initial-state #:global-store G
                     #:pc           (declaration->pc decl)
                     #:sp           sp+
                     #:memory       mem++
                     #:instructions insns
                     #:input-buffer buf)
      ))


(define-grammar tinyA+ #:extends tinyA
  (expr ::= (global-store stack-pointer memory insn-store)) ; the memory fragment associated with a compiled program
  #;(vallist ::= list<val>)
  #;(vallistlist ::= list<vallist>)
  ; The context consists of (1) the arguments to be passed to 'main'; and (2) a
  ; list of lists of values that provide input to the INPUT command
  (ctx  ::= (input-list list<input-list>))
  )

; For now, just print out the instructions in memory
(define (display-tinyA-lang-expression expr)
  (match expr
    [(tinyA (g:global-store sp:stack-pointer mem:memory insns:insn-store))
     (displayln "=global store=")
     (display-global-store g)
     (displayln "=stack pointer=")
     (displayln sp)
     (displayln "=memory=")
     (tinyC:display-memory mem)
     (displayln "=instruction store=")
     (tinyC:display-memory insns)
     ]
    ))

(define (display-tinyA-lang-context ctx)
  (tinyC:display-env ctx))
     


(define-language tinyA-lang
  #:grammar tinyA+
  #:expression expr #:size 5
  #:context ctx #:size 3 ; The trace acts as as the argument list
  ; A whole program is a (failure/c state?)
  #:link (λ (ctx expr)
           (match (cons ctx expr)
             [(cons (tinyA+ (args:input-list input:list<input-list>))
                    (tinyA (g:global-store sp:stack-pointer m:memory insns:insn-store)))
              (load-compiled-program g insns m sp (seec->list input) (seec->list args))]
             ))
  #:evaluate (λ (p) (do st <- p
                        st+ <- (eval-statement (max-fuel) st)
                        (state-trace st+)))
  )

