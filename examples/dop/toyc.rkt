#lang seec
(require racket/contract)
(require "monad.rkt")
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
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
      (BEGIN list<statement>)
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
  (stack        ::= list<stack-elem>)
  (stack-elem   ::= (frame list<statement>))
  (non-empty-stack ::= (stack-elem stack))

  ; A memory 'M' is a map from locations to objects
  (memory       ::= list<mem-mapping>)
  (mem-mapping  ::= (loc-ident object))

  ; A context ctx is a triple consisting of the top-most stack frame, the remainder
  ; of the stack, and memory
  (context      ::= (non-empty-stack memory))
  ; 
  (state        ::= (statement context))

  ; The global store 'G' is a sequence of procedure declarations
  (global-store ::= list<declaration>)

  ; An output trace 't' is a sequence of values
  (trace        ::= list<val>)

  )

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
    [(syntax simple-type) (toyc undef)]
    [(syntax (array ty+:simple-type len:integer))
     (seec-build-list len (toyc undef))]
    ))

; Look up a variable in a frame. How to handle errors?
(define/contract (lookup-var x F)
  (-> syntax-var? toyc-frame? (or/c #f toyc-loc?))
  (match F
    [(toyc nil) #f]
    [(toyc (cons (y:var l:loc) F+:frame))
     (if (equal? x y)
         l
         (lookup-var x F+))]
    ))

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

(define/contract (eval-lval lv F m)
  (-> syntax-lval? toyc-frame? toyc-memory? (or/c #f toyc-val?))
  (match lv
    [(toyc x:var) (lookup-var x F)]
    [(toyc (* lv+:lval))
     (match (eval-lval lv+ F m)
       [(toyc l:loc)
        (match (lookup-mem l m)
          [(toyc v:val) v]
          [_ #f]
          )]
       [_ #f]
       )]
    ))

(define/contract (eval-expr e F m)
  (-> syntax-expr? toyc-frame? toyc-memory? (or/c #f toyc-val?))
  (match e
    [(toyc n:integer) n]
    [(toyc null)      0]
    [(toyc (* e+:expr))
     (match (eval-expr e+ F m)
       [(toyc l:loc)
        (match (lookup-mem l m)
          [(toyc v:val) v]
          )]
       [_ #f]
       )]

    [(toyc x:var)
     (match (lookup-mem (lookup-var x F) m)
       [(toyc v:val) v]
       [_ #f]
       )]

    [(toyc (& lv:lval))
     (eval-lval lv F m)
     ]

    [(toyc (op:binop e1:expr e2:expr))
     (do (<- v1 (eval-expr e1 F m))
         (<- v2 (eval-expr e2 F m))
         (eval-binop op v1 v2))
     ]
    ))



; Remove a location from memory. Will return #f if x does not occur in m
(define/contract (drop-loc-ident x m)
  (-> toyc-loc-ident? toyc-memory? (or/c #f toyc-memory?))
  (match m
    [(toyc nil) #f]
    [(toyc (cons (y:loc-ident object) m+:memory))
     (if (equal? x y)
         m+
         (drop-loc-ident x m+)
         )]
    ))
(define (drop-loc l m)
  (match l
    [(toyc (x:loc-ident offset)) (drop-loc-ident x m)]
    ))
        

; Free all the locations allocated in F.
; If any of those locations do not occur in m, return #f
(define/contract (pop-stack F m)
  (-> toyc-frame? toyc-memory? (or/c #f toyc-memory?))
  (match F
    [(toyc nil) m]
    [(toyc (cons (x:var l:loc) F+:frame))
     (do (<- m+ (drop-loc l m))
         (pop-stack F+ m+))]
    ))

(define/contract (ctx->top-frame ctx)
  (-> toyc-context? toyc-stack-elem?)
  (match ctx
    [(toyc ((F:stack-elem _:stack) _:memory))
     F]
    ))
(define/contract (ctx->stack-tail ctx)
  (-> toyc-context? toyc-stack?)
  (match ctx
    [(toyc ((_:stack-elem S:stack) _:memory))
     S]))
(define/contract (ctx->mem ctx)
  (-> toyc-context? toyc-memory?)
  (match ctx
    [(toyc (_:non-empty-stack m:memory))
     m]))
(define/contract (state->ctx st)
  (-> toyc-state? toyc-context?)
  (match st
    [(toyc (_:statement ctx:context)) ctx]
    ))
(define/contract (state->statement st)
  (-> toyc-state? toyc-statement?)
  (match st
    [(toyc (stmt:statement _:context)) stmt]
    ))


(define make-state-output
  (λ (#:trace      [tr   seec-empty]
      #:statements [stmts #f]
      #:statement  [stmt (if stmts
                             (toyc (BEGIN ,(list->seec stmts)))
                             (toyc SKIP))]
      ctx)
    (cons tr (toyc (,stmt ,ctx)))
    ))

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
  (-> toyc-declaration? ((curry seec-list-of?) toyc-statement?))
  (match decl
    [(toyc (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     body]))


    
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

(define/contract (eval-exprs args F m)
  (-> (listof syntax-expr?) toyc-frame? toyc-memory? (or/c #f (listof toyc-val?)))
  (let ([ms-maybe (map (λ (e) (eval-expr e F m)) args)])
    (if (andmap ms-maybe)
        ms-maybe
        #f)))

#;(define/contract (make-frame decl vs ctx)
  (-> toyc-declaration? (listof toyc-val?) toyc-context? (or/c #f toyc-context?))

  ; Need to construct
  ; 1. new top frame
  ; 2. new memory consisting of ??
  ())

; Take a single step
(define/contract (eval-statement-1 g stmt ctx)
  (-> toyc-global-store? toyc-statement? toyc-context? (or/c #f (cons/c toyc-trace? toyc-state?)))

  (match stmt
    [(toyc (ASSIGN lv:lval e:expr))
     (let ([F (ctx->top-frame ctx)]
           [m (ctx->mem ctx)])
       (do (<- l    (eval-lval lv F m))
           (<- v    (eval-expr e F m))
           (<- ctx+ (set-lval l v ctx))
           (make-state-output ctx+)
           ))]


    ; Invoke the procedure, allocating memory for p's local variables and
    ; pushing the current stack frame and remaining instructions onto the stack
    #;[(toyc (CALL p:proc-name args:list<expr>))

     (let* ([decl (lookup-in-global-store g p)]
            [vs   (eval-exprs (seec->list args) ctx)]
            [ctx+ (make-frame decl vs ctx)]
            [body (decl->body decl)]
            )
       (make-state-output #:statement (toyc (SEQ (BEGIN ,body) RETURN))
                          ctx+)
       )]
    [(toyc RETURN)
     #f] ; TODO

    [(toyc (IF b:expr t:statement f:statement))
     (match (eval-expr b (ctx->top-frame ctx) (ctx->mem ctx))
       [(toyc 1)
        (make-state-output #:statement t
                           ctx)]
       [(toyc 0)
        (make-state-output #:statement f
                           ctx)]
       [_ #f]
       )]

    [(toyc (WHILE b:expr w:statement))
     (match (eval-expr b (ctx->top-frame ctx) (ctx->mem ctx))
       [(toyc 1)
        (make-state-output #:statement (toyc (SEQ ,w (WHILE ,b ,w)))
                           ctx)]

       [(toyc 0)
        (make-state-output ctx)]

       [_ #f]
       )]

    [(toyc (OUTPUT e:expr))
     (do (<- v (eval-expr e (ctx->top-frame ctx) (ctx->mem ctx)))
         (make-state-output #:trace (seec-singleton v)
                            ctx)
       )]

    ; Sequencing
    [(toyc (SEQ SKIP stmt+:statement))
     (make-state-output #:statement stmt+
                        ctx)]
    [(toyc (SEQ stmt1:statement stmt2:statement))
     (match (eval-statement-1 g stmt1 ctx)
       [(cons tr (toyc (stmt1+:statement ctx+:context)))
        (make-state-output #:trace tr
                           #:statement (toyc (SEQ ,stmt1+ ,stmt2))
                           ctx+)]
       [_ #f]
       )]
    ; Begin blocks
    [(toyc (BEGIN nil))
     (make-state-output ctx)
     ]    
    [(toyc (BEGIN (cons stmt+:statement stmts+:list<statement>)))
     (eval-statement-1 g (toyc (SEQ ,stmt+ (BEGIN ,stmts+)))
                       ctx)]


    [(toyc SKIP) ; SKIP cannot take a step
     #f
     ]

    ))
