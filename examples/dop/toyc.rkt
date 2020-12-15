#lang seec
(require racket/contract)
(require "monad.rkt")
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
(require (only-in racket/string ; foramtting
                  string-join
                  ))
(require rosette/lib/value-browser) ; debugging

(provide (all-defined-out))

(define-grammar syntax

  ; A type 'ty' is either a simple type 'py' or an array type
  ; '(arr py integer)' is the type of an 'integer' length array of
  ; values of type 'py'.
  (type        ::= simple-type (array simple-type integer))
  ; A simple type is either an 'int' or a pointer type.
  (simple-type ::= int (* type))

  ; Expressions
  (expr ::=
      ; A constant integer
      integer
      ; The null pointer
      null
      ; Dereference the pointer that 'ex' evaluates to
      (* expr)
      ; A variable
      var
      ; Take the address of the l-value 'lv'
      (& lval)
      ; Apply a binary operation
      (binop expr expr)
      )
  (binop ::= + - * / = <)

  ; An l-value is either a variable 'x' or the location
  ; pointed to by another l-value 
  (lval  ::= var (* lval))
  (var   ::= (VAR integer))

  (proc-name ::= string)
  )

(define-grammar toyc #:extends syntax

  ; A program 'P' is a sequence of procedure declarations 'pd ...'.
  ; Execution starts by invoking the procedure named 'main'.
  (prog        ::= list<declaration>)

  ; A procedure declaration 'pd' is a procedure name 'm' followed by
  ; a sequence of parameter declarations '[x py]', a sequence of
  ; local variable declarations '[x ty]', and a sequence of statements.
  (declaration ::= (proc-name list<param-decl> list<local-decl> list<statement>))
  (param-decl  ::= (var simple-type))
  (local-decl  ::= (var type))

  ; Statements
  (statement   ::= 
      ; Assign the result of evaluating 'ex' to the l-value of 'lv'
      (ASSIGN lval expr)
      ; Invoke 'm' with the results of evaluating 'ex ...' as arguments
      (CALL proc-name list<expr>)
      ; Return to the previous call frame
      RETURN
      ; Evaluates the first statement if 'ex' evaluates to a non-zero
      ; value, otherwise evaluates the second statement
      (IF expr statement statement)
      ; Executes 'st' while 'ex' does not evaluate to 0
      (WHILE expr statement)
      ; Outputs the value of 'ex' to the output log
      (OUTPUT expr)
      ; Evaluates the sequence of statements 'st ...'
      (SEQ statement statement)
      ; A no-op
      SKIP)

  ;;;;;;;;;;;;;
  ; Semantics ;
  ;;;;;;;;;;;;;

  ; Values are either integers or a location with a unique
  ; label 'a' identifying an object and an offset within the object
  (val    ::= integer loc)
  (loc    ::= (loc-ident offset))
  (loc-ident ::= natural)
  (offset ::= natural)

  ; A memory 'object' is either a value, an array (list of objects), or undefined
  (object       ::= list<object> val undef)

  ; A stack frame 'F' is a mapping from variables to locations
  (frame        ::= list<loc-mapping>)
  (loc-mapping  ::= (var loc))

  ; A stack 'S' is a sequence of terms '(F st ...)' which record
  ; the stack frame and remaining instructions for each procedure
  ; on the call stack
  #;(stack        ::= list<stack-elem>)
  #;(stack-elem   ::= (frame list<statement>))
  (stack          ::= list<frame>)
  (non-empty-stack ::= (frame stack))

  ; A memory 'M' is a map from locations to objects
  (memory       ::= list<mem-mapping>)
  (mem-mapping  ::= (loc-ident object))

  ; A context ctx is a triple consisting of the top-most stack frame, the remainder
  ; of the stack, and memory
  (context      ::= (non-empty-stack memory))
  ; 
  #;(state        ::= (statement context))

  ; The global store 'G' is a sequence of procedure declarations
  (global-store ::= list<declaration>)

  ; An output trace 't' is a sequence of values
  (trace        ::= list<val>)

  )

(define/contract (list->statement l)
  (-> (listof toyc-statement?) toyc-statement?)
  (cond
    [(empty? l) (toyc SKIP)]
    [else       (let ([s1 (first l)]
                      [s2 (list->statement (rest l))])
                  (toyc (SEQ ,s1 ,s2)))]
    ))
    

;;;;;;;;;;;;
;; States ;;
;;;;;;;;;;;;

(struct state (statement context trace fresh-var)
  #:transparent)
(define state->context state-context)
(define state->statement state-statement)
(define state->trace state-trace)
(define/contract (fresh-var st)
  (-> state? (cons/c integer? state?))
  (let* ([x (state-fresh-var st)]
         [st+ (state (state-statement st)
                     (state-context st)
                     (state-trace st)
                     (+ 1 x))])
    (cons x st+)))


(define/contract (update-context-memory ctx m)
  (-> toyc-context? toyc-memory? toyc-context?)
  (match ctx
    [(toyc (S:non-empty-stack _:memory))
     (toyc (,S ,m))]
    ))

; The optional arguments of update-state default to trivial trace and statement,
; NOT the trace and statemnt of the previous state. The context argument DOES
; default to that of the previous state. The fresh variable argument is always
; preserved. To update the fresh variable argument, you must call `fresh-var`
; above.
(define update-state
  (λ (st
      #:trace      [tr   (state->trace st)]
      #:statements [stmts #f] ; (or/c #f (listof toyc-statement?))
      #:statement  [stmt (if stmts
                             (list->statement stmts)
                             (toyc SKIP))]
      #:memory     [m  #f] ; This option only works if ctx is not supplied
      #:context    [ctx (if m
                            (update-context-memory (state->context st) m)
                            (state->context st))]
      )
    (state stmt ctx tr (state-fresh-var st))
    ))

(define (max-loc ctx)
  (define (max-loc-in-mem m)
    (match m
      [(toyc nil) 0]
      [(toyc (cons (lid:loc-ident _:object) m+:memory))
       (max lid (max-loc-in-mem m+))]
      ))
  (match ctx
    [(toyc (_:non-empty-stack m:memory))
     (max-loc-in-mem m)]
    ))
(define (init-state ctx)
  (state (toyc SKIP)
         ctx
         seec-empty
         (+ 1 (max-loc ctx))))

;;;;;;;;;;;;;;;;;;;;;
;; Pretty printing ;;
;;;;;;;;;;;;;;;;;;;;;

; Return a list of map bindings e.g.
;
; x0 ↦ y0
; x1 ↦ y1
; ...
(define (pp-mapping pair)
  (match pair
    [(toyc (x:any y:any))
     (format "    ~a |-> ~a" x y)]
    ))
(define (pp-map m)
  (map pp-mapping (seec->list m)))

(define (pp-memory m)
  (string-join (pp-map m)
               (format "~n")))
(define (display-memory m)
  (displayln (pp-memory m)))

(define (pp-frame F)
  (string-join (pp-map F)
               (format "~n")
               #:before-first (format "[~n")
               #:after-last   (format "~n]")
               ))
(define (display-frame F)
  (displayln (pp-frame F)))
(define (pp-stack S)
  (let ([frames (map pp-frame
                     (seec->list S))])
    (string-join frames
                 (format "~n"))))
(define (display-stack S)
  (displayln (pp-stack S)))

(define (display-context ctx)
  (match ctx
    [(toyc ((F:frame S:stack) m:memory))
     (printf "==Top frame==~n")
     (display-frame F)
     (printf "==Stack==~n")
     (display-stack S)
     (printf "==Memory==~n")
     (display-memory m)
     ]))


(define (display-state st)
  (display-context (state->context st))

  (printf "==Next statement== ~a~n" (state->statement st)) 

  (printf "==Trace== ~a~n" (state->trace st))

  (printf "==Fresh Var== ~a~n~n" (state-fresh-var st))
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Testing pretty printing ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (pp-test)
  (define F1 (list->seec (list (toyc ((VAR 0) (100 0)))
                               (toyc ((VAR 1) (101 1)))
                               (toyc ((VAR 2) (102 0)))
                               )))
  (printf "~n==F1==~n")
  (display-frame F1)
  (define F2 (list->seec (list (toyc ((VAR -1) (200 0)))
                               )))
  (printf "~n==F2==~n")
  (display-frame F2)


  (define S (list->seec (list F2)))
  (printf "~n==S==~n")
  (display-stack S)

  (define m (list->seec (list (toyc (100 undef))
                              (toyc (101 (103 1)))
                              (toyc (102 undef))
                              (toyc (103 (cons undef (cons 42 nil))))
                              )))
  (printf "~n==m==~n")
  (display-memory m)

  (define ctx (toyc ((,F1 ,S) ,m)))
  (printf "~n==ctx==~n")
  (display-context ctx)

  (define st0 (init-state ctx))
  (printf "~n==st0==~n")
  (display-state st0)
  )
#;(pp-test)

;;;;;;;;;;;;;;;
;; Accessors ;;
;;;;;;;;;;;;;;;


(define lid->loc
  (λ (lid
      #:offset [o 0])
    (toyc (,lid ,o))))

(define/contract (declaration->name decl)
  (-> toyc-declaration? syntax-proc-name?)
  (match decl
    [(toyc (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     p]))
(define/contract (declaration->parameters decl)
  (-> toyc-declaration? ((curry seec-list-of?) toyc-param-decl?))
  (match decl
    [(toyc (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     params]))
(define/contract (declaration->locals decl)
  (-> toyc-declaration? ((curry seec-list-of?) toyc-local-decl?))
  (match decl
    [(toyc (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     locals]))
(define/contract (declaration->body decl)
  (-> toyc-declaration? toyc-statement?)
  (match decl
    [(toyc (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     (list->statement (seec->list body))]
    ))

(define/contract (context->top-frame ctx)
  (-> toyc-context? toyc-frame?)
  (match ctx
    [(toyc ((top-f:frame rest-s:stack) _:memory))
     top-f]
    ))
(define/contract (context->non-empty-stack ctx)
  (-> toyc-context? (listof toyc-frame?))
  (match ctx
    [(toyc ((top-f:frame rest-s:stack) _:memory))
     (cons top-f (seec->list rest-s))]
    ))
(define/contract (context->memory ctx)
  (-> toyc-context? toyc-memory?)
  (match ctx
    [(toyc (_:non-empty-stack m:memory))
     m]))

(define/contract (ctx->top-frame ctx)
  (-> toyc-context? toyc-frame?)
  (match ctx
    [(toyc ((F:frame _:stack) _:memory))
     F]
    ))
(define/contract (ctx->stack-tail ctx)
  (-> toyc-context? toyc-stack?)
  (match ctx
    [(toyc ((_:frame S:stack) _:memory))
     S]))
(define/contract (ctx->mem ctx)
  (-> toyc-context? toyc-memory?)
  (match ctx
    [(toyc (_:non-empty-stack m:memory))
     m]))





;;;;;;;;;;;;;;;;;;;;
;; SEEC Utilities ;;
;;;;;;;;;;;;;;;;;;;;

; Return `#f` value if not (0 <= i < length l), otherwise return the
; element at location i in the seec-list l
(define (seec-ith i l)
  (let ([l-list (seec->list l)])
    (cond
      [(< -1 i (length l-list))
       (list-ref l-list i)]
      [else #f]
      )))
(define (seec-set-ith i v l)
  (cond
    [(seec-empty? l) l]
    [(seec-cons? l)
     (let* ([h (seec-head l)]
            [t (seec-tail l)])
       (if (equal? i 0)
           (seec-cons v t)
           (seec-cons h (seec-set-ith (- i 1) v t))))]
    ))
(define (seec-build-list n default)
  (list->seec (build-list n (λ (i) default))))



;;;;;;;;;;;;;;;;;;;;;;
;; Memory utilities ;;
;;;;;;;;;;;;;;;;;;;;;;

; Return the object associated with the ident in memory. Returns `#f` if the
; ident does not occur in memory.
(define/contract (lookup-mem-mapping x m)
    (-> toyc-loc-ident? toyc-memory? (or/c #f toyc-object?))
    (match m
      [(toyc nil) #f] ; Should this be undef or not actually defined?
      [(toyc (cons (y:loc-ident obj:object) m+:memory))
       (if (equal? x y)
           obj
           (lookup-mem-mapping x m+))]
      ))

; Dereference a location by looking up the label in the memory
; and indexing the object at the appropriate offset
(define/contract (lookup-mem l m)
  (-> toyc-loc? toyc-memory? (or/c #f toyc-object?))

  (match l
    [(toyc (x:loc-ident o:offset))
     (match (lookup-mem-mapping x m)
       [(toyc arr:list<object>) (seec-ith o arr)]
       [(toyc obj:object)       ; either val or undef
                                (if (equal? o 0)
                                    obj
                                    #f)]
       [_                       #f]
       )]
    ))


; Update the offset into the object with the value v
;
; If obj is a value or undefined, the offset must be 0, or else the function
; will return #f. If obj is an array, o must be in the scope of the array, or
; else the function will return false
(define/contract (update-object-at-offset obj o v)
  (-> toyc-object? integer? toyc-val? (or/c #f toyc-object?))
  (match obj
    ; if the object is an array, update the array at that index
    [(toyc arr:list<object>)
     (seec-set-ith o v arr)]
    ; otherwise, the offset must be 0
    [(toyc _:object)
     (if (equal? o 0)
         v
         #f)]
    ))

; Update the value in memory at the specified location
; If (lookup-mem l m) is #f, store-mem is #f
(define/contract (store-mem l v m)
  (-> toyc-loc? toyc-val? toyc-memory? (or/c #f toyc-memory?))

  (match l
    [(toyc (x:loc-ident o:offset))

     (match m
       [(toyc nil) #f]
       [(toyc (cons (y:loc-ident obj:object) m+:memory))
        (cond
          [(= x y)
           ; if x occurs at the head of the memory list
           (do (<- obj+ (update-object-at-offset obj o v))
               (seec-cons (toyc (,y ,obj+))
                          m+))]

          [else
           ; if x does not occur at the head of the memory list,
           ; recurse
           (do (<- m++ (store-mem l v m+))
               (seec-cons (toyc (,y ,obj))
                          m++))
            ]
          )]
       )]))




;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluate expressions ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;


; Given a location and a value, update the memory in the input context
(define/contract (set-lval l v ctx)
  (-> toyc-val? toyc-val? toyc-context? (or/c #f toyc-context?))
  (cond
    [(toyc-loc? l)
     (match ctx
       [(toyc (S:non-empty-stack m:memory))
        (do (<- m+ (store-mem l v m))
            (toyc (,S ,m+))
          )])]

    [else #f]))
    

; Unitialized values are represented by 'undef' values
(define/contract (init-value ty)
  (-> syntax-type? toyc-object?)
  (match ty
    [(syntax simple-type)  (toyc undef)]
    [(syntax (array ty+:simple-type len:integer))
     (seec-build-list len (toyc undef))]
    ))

; Look up a variable in a frame.
(define/contract (lookup-var x F)
  (-> syntax-var? toyc-frame? (or/c #f toyc-loc?))
  (match F
    [(toyc nil) #f]
    [(toyc (cons (y:var l:loc) F+:frame))
     (if (equal? x y)
         l
         (lookup-var x F+))]
    ))

; Evaluate a binary operator on two values.
; Pointer arithmetic is possible for + and - if the first value is a pointer
; Equality comparison is allowed for any types
(define/contract (eval-binop op v1 v2)
  (-> syntax-binop? toyc-val? toyc-val? (or/c #f toyc-val?))
  (cond

    [(equal? op (syntax =))
     (if (equal? v1 v2) 1 0)]

    [(not (integer? v2))
     #f] ; Cannot call eval-binop when second argument is not an integer
                           
    [(not (integer? v1))
     (match (cons op v1)
       [(cons (syntax +) (toyc (x:loc-ident o:offset)))
        (toyc (,x ,(+ o v2)))]
       [(cons (syntax -) (toyc (x:loc-ident o:offset)))
        (toyc (,x ,(- o v2)))]
       [_ #f] ; Can only perform +/- pointer arithmetic
       )]

    ; Otherwise, both v1 and v2 are integers
    [(equal? op (syntax +)) (+ v1 v2)]
    [(equal? op (syntax -)) (- v1 v2)]
    [(equal? op (syntax *)) (* v1 v2)]
    [(equal? op (syntax /)) (/ v1 v2)]
    [(equal? op (syntax <)) (if (< v1 v2) 1 0)]
    ))


; Evalue an l-value
(define/contract (eval-lval lv F m)
  (-> syntax-lval? toyc-frame? toyc-memory? (or/c #f toyc-val?))
  (match lv
    [(toyc x:var) (lookup-var x F)]
    [(toyc (* lv+:lval))
     (match (eval-lval lv+ F m)
       ; eval-lval could produce any value, including an integer, in which case
       ; (*lv) is undefined
       [(toyc l:loc)
        (match (lookup-mem l m)
          ; lookup-mem could produce any object (including undef or an array
          ; object), in which case return #f
          [(toyc v:val) v]
          [_ #f]
          )]
       [_ #f]
       )]
    ))

; Evaluate an expression given a frame and memory
(define/contract (eval-expr e F m)
  (-> syntax-expr? toyc-frame? toyc-memory? (or/c #f toyc-val?))
  (match e
    [(toyc n:integer) n]
    [(toyc null)      #f] ; Should this return 0 or something else instead?
                          ; Allow possibiility of returning undef?
    [(toyc (* e+:expr))
     (match (eval-expr e+ F m)
       [(toyc l:loc)
        (match (lookup-mem l m)
          [(toyc v:val) v]
          )]
       [_ #f]
       )]

    [(toyc x:var)
     (match (lookup-var x F)
       [(toyc l:loc)
        (match (lookup-mem l m)
          [(toyc v:val) v]
          [_ #f]
          )]
       [_ #f])]

    [(toyc (& lv:lval)) ; Is this right?
     (eval-lval lv F m)
     ]

    [(toyc (op:binop e1:expr e2:expr))
     (do (<- v1 (eval-expr e1 F m))
         (<- v2 (eval-expr e2 F m))
         (eval-binop op v1 v2))
     ]
    ))


; Evaluate a list of expressions to produce a list of values
(define/contract (eval-exprs args ctx)
  (-> (listof syntax-expr?) toyc-context? (or/c #f (listof toyc-val?)))
  (let* ([F (context->top-frame ctx)]
         [m (context->memory ctx)]
         [ms-maybe (map (λ (e) (eval-expr e F m)) args)])
    (if (andmap (λ (x) x) ms-maybe)
        ms-maybe
        #f)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cleanup and stack management ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




; Remove a location from memory. Will return #f if x does not occur in m
(define/contract (drop-loc-ident x m)
  (-> toyc-loc-ident? toyc-memory? (or/c #f toyc-memory?))
  (match m
    [(toyc nil) #f]
    [(toyc (cons (y:loc-ident obj:object) m+:memory))
     (if (equal? x y)
         m+
         (do (<- m++ (drop-loc-ident x m+))
             (toyc (cons (,y ,obj) ,m++)))
         )]
    ))

; Free all the locations allocated in F.
; If any of those locations do not occur in m, return #f
(define/contract (pop-stack F m)
  (-> toyc-frame? toyc-memory? (or/c #f toyc-memory?))
  (match F
    [(toyc nil) m]
    [(toyc (cons (_:var (x:loc-ident _:object)) F+:frame))
     (do (<- m+ (drop-loc-ident x m))
         (pop-stack F+ m+))]
    ))


; Return the declaration associated with the name p in g
(define/contract (lookup-in-global-store g p)
  (-> toyc-global-store? syntax-proc-name? (or/c #f toyc-declaration?))
  (match g
    [(toyc nil) #f]
    [(toyc (cons decl:declaration g+:global-store))
     (if (equal? (declaration->name decl) p)
         decl
         (lookup-in-global-store g+ p)
         )]
    ))

; Check that a value v has a type ty, including pointers that might be included
; in m
(define/contract (check-type? ty obj m)
  (-> syntax-type? toyc-object? toyc-memory? boolean?)
  (or (equal? obj (toyc undef))
  (match ty
    [(toyc int) (integer? obj)]
    [(toyc (* ty+:type))
     (do (toyc-loc? obj)
         (<- obj+ (lookup-mem obj m))
         (check-type? ty+ obj+ m)
         )]
    [(toyc (array ty+:simple-type len:integer))
     (let ([objs (seec->list obj)])
       (and (= (length objs) len)
            (andmap (λ (obj+) (check-type? ty+ obj+ m))
                    objs)))]
    )))


; Allocate a fresh location identifier and bind it to the object obj in memory
(define/contract (alloc obj st)
  (-> toyc-object? state? (or/c #f (cons/c toyc-loc-ident? state?)))
  (match (fresh-var st)
    [(cons lid st+)
     (let* ([ctx (state->context st+)]
            [m  (context->memory ctx)]
            [m+ (toyc ((,lid ,obj) ,m))]
            [ctx+ (update-context-memory ctx m+)]
            )
       (cons lid (update-state st+ #:context ctx+)))]
     [_ #f]
     ))

; Take as input an object of type ty and allocate a memory location l↦obj in
; memory, returning l. If ty is an array type, instead allocate the array in
; memory with l2↦obj and generate a fresh memory location l1↦l2.
(define/contract (alloc-object ty obj st)
  (-> syntax-type?
      toyc-object?
      state?
      (or/c #f (cons/c toyc-loc? state?)))
  (match ty
    [(toyc simple-type)
     (do (<- l-st (alloc obj st))
         (<- l    (lid->loc (car l-st)))
       (cons l (cdr l-st))
       )]

    [(toyc (array ty+:simple-type len:integer))
     ; generate two fresh location ids, lid1 and lid2
     ; The frame with have x ↦ Loc lid1 0
     ; The memory will have lid1 ↦ Loc lid2 0
     ; and                  lid2 ↦ obj

     (do (<- l2-st (alloc obj st))
         (<- l2    (lid->loc (car l2-st)))
         (<- l1-st (alloc l2 (cdr l2-st)))
         (<- l1    (lid->loc (car l1-st)))
         (cons l1 (cdr l1-st))
         )]
    ))
; For each declaration tuple (x,ty,v), add a binding x ↦ l to the frame and add
; a binding l ↦ v to the state.
;
; It should be the case that v has the appropriate type.
(define/contract (alloc-declarations decls st)
  (-> (listof (list/c syntax-var? syntax-type? toyc-object?))
      state?
      (or/c #f (cons/c toyc-frame? state?)))

  (cond
    [(empty? decls) (cons seec-empty st)]

    [else (match (first decls)
            [(list x ty obj)
             (do (<- l-st+  (alloc-object ty obj st))
                 (<- l      (car l-st+))
                 (<- F-st++ (alloc-declarations (rest decls)
                                                (cdr l-st+)))
                 (<- F      (car F-st++))
                 (<- F+     (seec-cons (toyc (,x ,l))
                                       F))
                 (cons F+ (cdr F-st++)))]
            )]
    ))


(define/contract (alloc-param-declarations decls vs st)
  (-> (listof toyc-param-decl?)
      (listof toyc-val?)
      state?
      (or/c #f (cons/c toyc-frame? state?)))

  ; Check that the values have appropriate type and zip together the
  ; declarations and values to provide to alloc-declarations
  (let ([decl-vs (map (λ (decl v)
                        (match decl
                          [(toyc (x:var ty:simple-type))
                           (do (check-type? ty v (context->memory (state->context st)))
                               (list x ty v))]
                          ))
                      decls
                      vs)])
    (alloc-declarations decl-vs st)))

    
(define/contract (alloc-local-declarations decls st)
  (-> (listof toyc-param-decl?)
      state?
      (cons/c toyc-frame? state?))

  ; Construct an appropriate input to alloc-declarations by constructing initial
  ; values for each type
  (let ([decl-vs (map (λ (decl)
                        (match decl
                          [(toyc (x:var ty:type))
                           (list x ty (init-value ty))]
                          ))
                      decls)])
    (alloc-declarations decl-vs st)))

; Allocate a frame and update the memory associated with a particular function
; declaration
(define/contract (alloc-frame decl vs st)
  (-> toyc-declaration? (listof toyc-val?) state? (or/c #f state?))

  (let* ([p            (declaration->name decl)]
         [param-decls  (seec->list (declaration->parameters decl))]
         [local-decls  (seec->list (declaration->locals decl))]
         )
    (do (<- F-st-args  (alloc-param-declarations param-decls vs st))
        (<- F-st-local (alloc-local-declarations local-decls (cdr F-st-args)))
      (let* ([st+   (cdr F-st-local)]
             [ctx+  (state->context st+)]
             [F     (seec-append (car F-st-args) (car F-st-local))]
             [S     (list->seec (context->non-empty-stack ctx+))]
             [m     (context->memory ctx+)]
             [ctx++ (toyc ((,F ,S) ,m))]
             )
        ; We need to pass along the state here because of the fresh
        ; variable counter. Alternately, we could consider a version of toyc
        ; that uses symbolic variables and a fresh assertion constraint
        (update-state st+ #:context ctx++)
        ))))


;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluate statements ;;
;;;;;;;;;;;;;;;;;;;;;;;;;

; Take a single step
(define/contract (eval-statement-1 g st)
  (-> toyc-global-store? state? (or/c #f state?))
  (printf "(eval-statement-1 ~a)~n" (state->statement st))

  (match (state->statement st)

    [(toyc SKIP) ; SKIP cannot take a step
     #f]

    [(toyc (ASSIGN lv:lval e:expr))
     (let* ([ctx (state->context st)]
            [F (ctx->top-frame ctx)]
            [m (ctx->mem ctx)])
       (do (<- l    (eval-lval lv F m))
           (<- v    (eval-expr e F m))
           (<- ctx+ (set-lval l v ctx))
           (update-state st
                         #:statement (toyc SKIP)
                         #:context ctx+
                         )
           ))]


    [(toyc (OUTPUT e:expr))
     (do (<- ctx (state->context st))
         (<- v (eval-expr e (ctx->top-frame ctx) (ctx->mem ctx)))
         (update-state st #:trace (seec-singleton v)
                          #:statement (toyc SKIP))
       )]


    ;; Procedure calls ;;

    [(toyc (CALL p:proc-name args:list<expr>))
    ; Invoke the procedure, allocating memory for p's local variables and
    ; pushing the current stack frame and remaining instructions onto the stack
     (do (<- decl (lookup-in-global-store g p))
         (<- body (declaration->body decl))
         (<- vs   (eval-exprs (seec->list args) (state->context st)))
         (<- st+  (alloc-frame decl vs st))
         (update-state st+
                       #:statement (toyc (SEQ ,body RETURN))
                       )
         )]

    ; Return from a function call and pop the top-most frame
    [(toyc RETURN)
     (match (state->context st)
       [(toyc ((F0:frame (cons F+:frame S:stack)) m:memory))
        (let* ([m+ (pop-stack F0 m)]
               [ctx+ (toyc ((,F+ ,S) ,m+))])
          (update-state st
                        #:statement (toyc SKIP)
                        #:context ctx+)
          )])]


    ;; Control flow ;;

    [(toyc (IF b:expr t:statement f:statement))
     (let* ([ctx (state->context st)]
            [F   (context->top-frame ctx)]
            [m   (context->memory ctx)])
     (match (eval-expr b F m)
       [(toyc 1)
        (update-state st #:statement t)]
       [(toyc 0)
        (update-state st #:statemenet f)]
       [_ #f]
       ))]

    [(toyc (WHILE b:expr w:statement))
     (let* ([ctx (state->context st)]
            [F   (context->top-frame ctx)]
            [m   (context->memory ctx)])
     (match (eval-expr b F m)
       [(toyc 1)
        (update-state st  #:statement (toyc (SEQ ,w (WHILE ,b ,w))))]
       [(toyc 0)
        (update-state st  #:statement (toyc SKIP))]
       [_ #f]
       ))]

    ; Sequencing
    [(toyc (SEQ SKIP stmt+:statement))
     (update-state st #:statement stmt+)]

    [(toyc (SEQ stmt1:statement stmt2:statement))
     (do (<- st1 (update-state st #:statement stmt1))
         (<- st1+ (eval-statement-1 g st1))
         (update-state st1+ #:trace (state->trace st1+)
                            #:statement (toyc (SEQ ,(state->statement st1+) ,stmt2))
                            ))]


    ))

;; Take some number of steps specified by the amount of fuel given
(define/contract (eval-statement fuel g st)
  (-> integer? toyc-global-store? state? (or/c #f state?))
  (cond
    [(equal? (state->statement st)
             (toyc SKIP))
     st] ; Evaluation has normalized before fuel ran out

    [(<= fuel 0) st] ; Fuel ran out. Return #f here instead?

    [else
     (do (<- st+ (eval-statement-1 g st))
         (eval-statement (- fuel 1) g st+))]
    ))
(define run
  (λ (#:fuel [fuel 100]
      prog    ; A racket list of declarations
      inputs  ; A racket list of inputs to main
      )
    (eval-statement fuel
                    (list->seec prog)
                    (update-state (init-state (toyc ((nil nil) nil)))
                                  #:statement (toyc (CALL "main" ,(list->seec inputs)))
                                  ))))
