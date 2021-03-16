#lang seec
(require seec/private/util)
(require seec/private/monad)
(require (only-in seec/private/string
                  string->racket))
(require (only-in racket/base
                  build-list
                  make-parameter
                  raise-argument-error
                  raise-arguments-error
                  [string? racket:string?]
                  [string-append racket:string-append]
                  ))
(require (only-in racket/string ; formatting
                  string-join
                  ))
(require rosette/lib/value-browser) ; debugging

(provide syntax
         syntax-type?
         syntax-simple-type?
         syntax-expr?
         syntax-binop?
         syntax-lval?
         syntax-var?
         syntax-proc-name?

         tinyC
         tinyC-lang
         tinyC-prog?
         tinyC-declaration?
         tinyC-param-decl?
         tinyC-local-decl?
         tinyC-statement?
         tinyC-val?
         tinyC-loc?
         tinyC-loc-ident?
         tinyC-offset?
         tinyC-object?
         tinyC-frame?
         tinyC-loc-mapping?
         tinyC-stack?
         tinyC-non-empty-stack?
         tinyC-memory?
         tinyC-mem-mapping?
         tinyC-context?
         tinyC-global-store?
         tinyC-trace?

         seec-ith
         seec-set-ith
         seec-build-list
         binop->racket
         decrement-fuel
         lid->loc

         max-fuel

         ; For functions that could potentially overlap with e.g. tinyAssembly,
         ; add a distinguishing prefix
         (prefix-out tinyC: (combine-out
            declaration->name
            declaration->parameters
            declaration->locals
            declaration->body
            display-memory
            lookup-mem
            lookup-mem-mapping
            update-object-at-offset
            store-mem
            set-lval
            drop-loc-ident
            pop-stack
            alloc
            alloc-object
            alloc-declarations
            alloc-frame
            
            (struct-out state)
            display-state
            init-state
            update-state
            state->context
            state->trace
            state->statement
            fresh-var

            display-statement
            display-declaration
            display-program
            display-env
            make-declaration

            context->memory
            context->top-frame
            context->non-empty-stack

            eval-binop
            eval-expr
            eval-exprs
            eval-statement-1
            run
            run+
            ))
         )


(use-contracts-globally #f)

(define-grammar syntax

  ; A type 'ty' is either a simple type 'py' or an array type
  ; '(arr py n)' is the type of an 'n' length array of
  ; values of type 'py'.
  (type        ::= simple-type (array simple-type natural))
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
  (var   ::= string)

  (proc-name ::= string)
  )

(define-grammar tinyC #:extends syntax

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
      ; Given a pointer to a buffer allocated in memory, accept input from the
      ; environment and write to the buffer.
      (INPUT expr)
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

  ; The environment is a tuple consisting of both (1) a list of values with
  ; which to call 'main'; and (2) a list of lists of values to be passed one at
  ; a time to calls to 'INPUT'
  (intlist      ::= list<integer>)
  (env          ::= (intlist list<intlist>))

  )

(define/contract (list->statement l)
  (-> (listof tinyC-statement?) tinyC-statement?)
  (cond
    [(empty? l) (tinyC SKIP)]
    [else       (let ([s1 (first l)]
                      [s2 (list->statement (rest l))])
                  (tinyC (SEQ ,s1 ,s2)))]
    ))
    

;;;;;;;;;;;;
;; States ;;
;;;;;;;;;;;;

; The input-buffer is a (racket) list of 'intlist's that are fed to calls to
; INPUT. This is a simple interaction model that cannot react dynamically to the
; program execution.
(struct state (statement context input-buffer trace fresh-var)
  #:transparent)
(define/contract (state->context st)
  (-> state? tinyC-context?)
  (state-context st))
(define/contract state->statement
  (-> state? tinyC-statement?)
  state-statement)
(define state->trace state-trace)
(define/contract (fresh-var st)
  (-> state? (cons/c integer? state?))
  (let* ([x (state-fresh-var st)]
         [st+ (state (state-statement st)
                     (state-context st)
                     (state-input-buffer st)
                     (state-trace st)
                     (+ 1 x))])
    (cons x st+)))


(define/contract (update-context-memory ctx m)
  (-> tinyC-context? tinyC-memory? tinyC-context?)
  (match ctx
    [(tinyC (S:non-empty-stack _:memory))
     (tinyC (,S ,m))]
    ))

; The optional arguments of update-state default to trivial trace and statement,
; NOT the trace and statemnt of the previous state. The context argument DOES
; default to that of the previous state. The fresh variable argument is always
; preserved. To update the fresh variable argument, you must call `fresh-var`
; above.
(define update-state
  (λ (st
      #:trace      [tr   (state->trace st)]
      #:statements [stmts #f] ; (or/c #f (listof tinyC-statement?))
      #:statement  [stmt (if stmts
                             (list->statement stmts)
                             (tinyC SKIP))]
      #:memory       [m  #f] ; This option only works if ctx is not supplied
      #:input-buffer [buf (state-input-buffer st)]
      #:context      [ctx (if m
                              (update-context-memory (state->context st) m)
                              (state->context st))]
      )
    (state stmt ctx buf tr (state-fresh-var st))
    ))

(define (max-loc ctx)
  (define (max-loc-in-mem m)
    (match m
      [(tinyC nil) 0]
      [(tinyC (cons (lid:loc-ident _:object) m+:memory))
       (max lid (max-loc-in-mem m+))]
      ))
  (match ctx
    [(tinyC (_:non-empty-stack m:memory))
     (max-loc-in-mem m)]
    ))
(define (init-state ctx)
  (state (tinyC SKIP)
         ctx
         (list)
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
    [(tinyC (x:any y:any))
     (format "    ~a |-> ~a" x y)]
    ))
(define (pp-map m)
  (map pp-mapping (seec->list m)))

(define (pp-memory m)
    (string-join (pp-map m)
                 (format "~n")))
(define (display-memory m)
  (for/all ([m m]) (displayln (pp-memory m))))

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
    [(tinyC ((F:frame S:stack) m:memory))
     (printf "==Top frame==~n")
     (display-frame F)
     (printf "==Stack==~n")
     (display-stack S)
     (printf "==Memory==~n")
     (display-memory m)
     ]))


(define (display-state st)
  (cond
    [(failure? st) (displayln st)]
    [else
     (display-context (state->context st))
     (printf "==Next statement== ~a~n" (state->statement st)) 
     (printf "==Trace== ~a~n" (state->trace st))
     (printf "==Fresh Var== ~a~n~n" (state-fresh-var st))
     ]))

(define (pp-intlist vals)
  (format "~a" (seec->list vals)))
(define (display-env env)
  (match env
    [(tinyC (args:intlist input:list<intlist>))
     (displayln (format "arguments: ~a" (pp-intlist args)))
     (displayln (format "input stream: ~a" (map pp-intlist (seec->list input))))]
    ))


(define/contract/debug (pp-expr e)
  (-> syntax-expr? racket:string?)
  (match e
    [(syntax x:integer)
     (format "~a" x)]
    [(syntax null)
     "null"]
    [(syntax (* e+:expr))
     (format "* ~a" (pp-expr e+))]
    [(syntax x:var)
     (string->racket x)]
    [(syntax (& lv:lval))
     (format "& ~a" (pp-expr lv))]
    [(syntax (op:binop e1:expr e2:expr))
     (format "~a ~a ~a" (pp-expr e1) op (pp-expr e2))]
    ))

(define-grammar listifyC #:extends tinyC
  (single-stmt ::= (ASSIGN lval expr)
                   (CALL proc-name list<expr>)
                   RETURN
                   (IF expr list<single-stmt> list<single-stmt>)
                   (WHILE expr list<single-stmt>)
                   (OUTPUT expr)
                   (INPUT expr)
                   ))
(define/contract (statement->list stmt)
  (-> tinyC-statement? (listof listifyC-single-stmt?))
  (match stmt
    [(tinyC (IF e:expr t:statement f:statement))
     (list (listifyC (IF ,e
                         ,(list->seec (statement->list t))
                         ,(list->seec (statement->list f)))))]
    [(tinyC (WHILE e:expr body:statement))
     (list (listifyC (WHILE ,e
                            ,(list->seec (statement->list body)))))]
    [(tinyC (SEQ stmt1:statement stmt2:statement))
     (append (statement->list stmt1)
             (statement->list stmt2))]
    [(tinyC SKIP)
     (list)]
    [_ (list stmt)]
    ))


(define (indent-string str)
  (racket:string-append "  " str))

; Produce a list of strings, one for each newline; this allows for proper indent
; management
(define/contract (pp-single-statement stmt)
  (-> listifyC-single-stmt? (listof racket:string?))
  (match stmt
    [(listifyC (ASSIGN x:lval e:expr))
     (list (format "~a = ~a;" (pp-expr x) (pp-expr e)))]
    [(listifyC (CALL p:proc-name es:list<expr>))
     (list (format "~a ~a;" (string->racket p) (map pp-expr (seec->list es))))]
    [(listifyC RETURN)
     (list (format "return();"))]
    [(listifyC (IF e:expr t:list<single-stmt> nil))
     (append (list (format "if (~a) {" (pp-expr e)))
             (map indent-string (flatten (map pp-single-statement (seec->list t))))
             (list (format "}"))
             )]
    [(listifyC (IF e:expr t:list<single-stmt> f:list<single-stmt>))
     (append (list (format "if (~a) {" (pp-expr e)))
             (map indent-string (flatten (map pp-single-statement (seec->list t))))
             (list (format "} else {"))
             (map indent-string (flatten (map pp-single-statement (seec->list f))))
             (list (format "}"))
             )
     #;(format "if (~a) {~n ~a~n} else {~n ~a~n};"
             e
             (pp-statement-list-indented (seec->list t))
             (pp-statement-list-indented (seec->list f))
             )]
    [(listifyC (WHILE e:expr body:list<single-stmt>))
     (append (list (format "while (~a) {" (pp-expr e)))
             (map indent-string (flatten (map pp-single-statement (seec->list body))))
             (list (format "}"))
             )
     #;(format "while (~a) {~n ~a ~n};"
             e
             (pp-statement-list-indented (seec->list body))
             )]
    [(listifyC (OUTPUT e:expr))
     (list (format "output(~a);" (pp-expr e)))]
    [(listifyC (INPUT e:expr))
     (list (format "input(~a);" (pp-expr e)))]
    ))

; Produce a list of strings, one for each newline; this allows for proper indent
; management
(define/contract (pp-statement stmt)
  (-> tinyC-statement? (listof racket:string?))
  (let* ([stmts   (statement->list stmt)])
    (flatten (map pp-single-statement stmts))))
(define/contract/debug #:suffix (pp-statements stmts)
  (-> (listof tinyC-statement?) (listof racket:string?))
  (flatten (map pp-statement stmts)))

(define (display-statement stmt)
  (displayln (string-join (pp-statement stmt)
                          "~n")))

(define/contract (pp-decl local-decl)
  (-> tinyC-local-decl? racket:string?)
  (match local-decl
    [(tinyC (x:var tp:type))
     (format "~a ~a" tp (string->racket x))]))

(define/contract (pp-params params)
  (-> (curry seec-list-of? tinyC-param-decl?)
      racket:string?)
  (string-join (map pp-decl (seec->list params))
               ", "))
(define/contract (pp-locals locals)
  (-> (curry seec-list-of? tinyC-local-decl?)
      (listof racket:string?))
  (map (λ (decl) (format "~a;" (pp-decl decl)))
       (seec->list locals)))

; Again produce a list of strings, for indent management
(define/contract/debug #:suffix (pp-declaration decl)
  (-> tinyC-declaration? (listof racket:string?))
  (match decl
    [(tinyC (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     (append (list (format "void ~a (~a) {" (string->racket p) (pp-params params)))
             (map indent-string (pp-locals locals))
             (map indent-string (pp-statements (seec->list body)))
             (list (format "}"))
             )]
    ))

(define/contract/debug #:suffix (display-declaration decl)
  (-> tinyC-declaration? any/c)
  (displayln (string-join (pp-declaration decl)
                          (format "~n"))))
(define/contract/debug #:suffix (display-program prog)
  (-> tinyC-prog? any/c)
  (andmap display-declaration (seec->list prog)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Testing pretty printing ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (pp-test)
  (define F1 (list->seec (list (tinyC ("x0" (100 0)))
                               (tinyC ("x1" (101 1)))
                               (tinyC ("x2" (102 0)))
                               )))
  (printf "~n==F1==~n")
  (display-frame F1)
  (define F2 (list->seec (list (tinyC ("x'" (200 0)))
                               )))
  (printf "~n==F2==~n")
  (display-frame F2)


  (define S (list->seec (list F2)))
  (printf "~n==S==~n")
  (display-stack S)

  (define m (list->seec (list (tinyC (100 undef))
                              (tinyC (101 (103 1)))
                              (tinyC (102 undef))
                              (tinyC (103 (cons undef (cons 42 nil))))
                              )))
  (printf "~n==m==~n")
  (display-memory m)

  (define ctx (tinyC ((,F1 ,S) ,m)))
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
    (tinyC (,lid ,o))))

(define/contract (declaration->name decl)
  (-> tinyC-declaration? syntax-proc-name?)
  (match decl
    [(tinyC (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     p]))
(define/contract (declaration->parameters decl)
  (-> tinyC-declaration? ((curry seec-list-of?) tinyC-param-decl?))
  (match decl
    [(tinyC (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     params]))
(define/contract (declaration->locals decl)
  (-> tinyC-declaration? ((curry seec-list-of?) tinyC-local-decl?))
  (match decl
    [(tinyC (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     locals]))
(define/contract (declaration->body decl)
  (-> tinyC-declaration? tinyC-statement?)
  (match decl
    [(tinyC (p:proc-name params:list<param-decl> locals:list<local-decl> body:list<statement>))
     (list->statement (seec->list body))]
    ))

(define/contract (context->top-frame ctx)
  (-> tinyC-context? tinyC-frame?)
  (match ctx
    [(tinyC ((top-f:frame rest-s:stack) _:memory))
     top-f]
    ))
(define/contract (context->non-empty-stack ctx)
  (-> tinyC-context? (listof tinyC-frame?))
  (match ctx
    [(tinyC ((top-f:frame rest-s:stack) _:memory))
     (cons top-f (seec->list rest-s))]
    ))
(define/contract (context->memory ctx)
  (-> tinyC-context? tinyC-memory?)
  (match ctx
    [(tinyC (_:non-empty-stack m:memory))
     m]))

(define/contract (ctx->top-frame ctx)
  (-> tinyC-context? tinyC-frame?)
  (match ctx
    [(tinyC ((F:frame _:stack) _:memory))
     F]
    ))
(define/contract (ctx->stack-tail ctx)
  (-> tinyC-context? tinyC-stack?)
  (match ctx
    [(tinyC ((_:frame S:stack) _:memory))
     S]))
(define/contract (ctx->mem ctx)
  (-> tinyC-context? tinyC-memory?)
  (match ctx
    [(tinyC (_:non-empty-stack m:memory))
     m]))





;;;;;;;;;;;;;;;;;;;;
;; SEEC Utilities ;;
;;;;;;;;;;;;;;;;;;;;

; Return `*fail*` value if not (0 <= i < length l), otherwise return the
; element at location i in the seec-list l
(define (seec-ith i l)
  (let ([l-list (seec->list l)])
    (cond
      [(< -1 i (length l-list))
       (list-ref l-list i)]
      [else *fail*]
      )))
(define (seec-set-ith i v l)
;  #:contract (-> integer? bonsai? seec-list? seec-list?)
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

; Return the object associated with the ident in memory. Returns `*fail*` if the
; ident does not occur in memory.
(define (lookup-mem-mapping x m)
  (-> tinyC-loc-ident? tinyC-memory? (failure/c tinyC-object?))
    (match m
      [(tinyC nil) *fail*] ; Should this be undef or not actually defined?
      [(tinyC (cons (y:loc-ident obj:object) m+:memory))
       (if (equal? x y)
           obj
           (lookup-mem-mapping x m+))]
      ))

; Dereference a location by looking up the label in the memory
; and indexing the object at the appropriate offset
(define/contract (lookup-mem l m)
  (-> tinyC-loc? tinyC-memory? (failure/c tinyC-object?))

  (match l
    [(tinyC (x:loc-ident o:offset))
     (match (lookup-mem-mapping x m)
       [(tinyC arr:list<object>) (seec-ith o arr)]
       [(tinyC obj:object)       ; either val or undef
                                (if (equal? o 0)
                                    obj
                                    *fail*)]
       [_                       *fail*]
       )]
    ))


; Update the offset into the object with the value v
;
; If obj is a value or undefined, the offset must be 0, or else the function
; will return *fail*. If obj is an array, o must be in the scope of the array, or
; else the function will return false
(define/contract (update-object-at-offset obj o v)
  (-> tinyC-object? integer? tinyC-val? (failure/c tinyC-object?))
  (match obj
    ; if the object is an array, update the array at that index
    [(tinyC arr:list<object>)
     (seec-set-ith o v arr)]
    ; otherwise, the offset must be 0
    [(tinyC _:object)
     (if (equal? o 0)
         v
         *fail*)]
    ))

; Update the value in memory at the specified location
; If (lookup-mem l m) is *fail*, store-mem is *fail*
(define/contract (store-mem l v m)
  (-> tinyC-loc? tinyC-val? tinyC-memory? (failure/c tinyC-memory?))

  (match l
    [(tinyC (x:loc-ident o:offset))

     (match m
       [(tinyC nil) *fail*]
       [(tinyC (cons (y:loc-ident obj:object) m+:memory))
        (cond
          [(= x y)
           ; if x occurs at the head of the memory list
           (do (<- obj+ (update-object-at-offset obj o v))
               (seec-cons (tinyC (,y ,obj+))
                          m+))]

          [else
           ; if x does not occur at the head of the memory list,
           ; recurse
           (do (<- m++ (store-mem l v m+))
               (seec-cons (tinyC (,y ,obj))
                          m++))
            ]
          )]
       )]))




;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluate expressions ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;


; Given a location and a value, update the memory in the input context
(define/contract (set-lval l v ctx)
  (-> tinyC-val? tinyC-val? tinyC-context? (failure/c tinyC-context?))
  (cond
    [(tinyC-loc? l)
     (match ctx
       [(tinyC (S:non-empty-stack m:memory))
        (do (<- m+ (store-mem l v m))
            (tinyC (,S ,m+))
          )])]

    [else *fail*]))
    

; Unitialized values are represented by 'undef' values
(define/contract (init-value ty)
  (-> syntax-type? tinyC-object?)
  (match ty
    [(syntax simple-type)  (tinyC undef)]
    [(syntax (array ty+:simple-type len:integer))
     (seec-build-list len (tinyC undef))]
    ))

; Look up a variable in a frame.
(define/contract (lookup-var x F)
  (-> syntax-var? tinyC-frame? (failure/c tinyC-loc?))
  (match F
    [(tinyC nil) *fail*]
    [(tinyC (cons (y:var l:loc) F+:frame))
     (if (equal? x y)
         l
         (lookup-var x F+))]
    ))

;  (binop ::= + - * / = <)
(define (binop->racket op)
  (match op
    [(syntax +) +]
    [(syntax -) -]
    [(syntax *) *]
    [(syntax /) /]
    [(syntax =) (λ (x y) (if (equal? x y) 1 0))]
    [(syntax <) (λ (x y) (if (< x y) 1 0))]
    ))

; Evaluate a binary operator on two values.
; Pointer arithmetic is possible for + and - if the first value is a pointer
; Equality comparison is allowed for any types
(define/contract (eval-binop op v1 v2)
  (-> syntax-binop? tinyC-val? tinyC-val? (failure/c tinyC-val?))
  (cond

    [(equal? op (syntax =))
     (if (equal? v1 v2) 1 0)]

    [(not (integer? v2))
     *fail*] ; Cannot call eval-binop when second argument is not an integer
                           
    [(and (not (integer? v1))
          (integer? v2))
     (match (cons op v1)
       [(cons (syntax +) (tinyC (x:loc-ident o:offset)))
        (tinyC (,x ,(+ o v2)))]
       [(cons (syntax -) (tinyC (x:loc-ident o:offset)))
        (tinyC (,x ,(- o v2)))]
       [_ *fail*] ; Can only perform +/- pointer arithmetic
       )]
    [(and (integer? v1)
          (integer? v2))
     ((binop->racket op) v1 v2)]

    ; Otherwise, both v1 and v2 are integers
    [else ((binop->racket op) v1 v2)]
    ))


; Evalue an l-value
(define/contract (eval-lval lv F m)
  (-> syntax-lval? tinyC-frame? tinyC-memory? (failure/c tinyC-val?))
  (match lv
    [(tinyC x:var) (lookup-var x F)]
    [(tinyC (* lv+:lval))
     (match (eval-lval lv+ F m)
       ; eval-lval could produce any value, including an integer, in which case
       ; (*lv) is undefined
       [(tinyC l:loc)
        (match (lookup-mem l m)
          ; lookup-mem could produce any object (including undef or an array
          ; object), in which case return *fail*
          [(tinyC v:val) v]
          [_ *fail*]
          )]
       [_ *fail*]
       )]
    ))

; Evaluate an expression given a frame and memory
(define/contract (eval-expr e F m)
  (-> syntax-expr? tinyC-frame? tinyC-memory? (failure/c tinyC-val?))
  (match e
    [(tinyC n:integer) n]
    [(tinyC null)      *fail*] ; Should this return 0 or something else instead?
                          ; Allow possibiility of returning undef?
    [(tinyC (* e+:expr))
     (match (eval-expr e+ F m)
       [(tinyC l:loc)
        (match (lookup-mem l m)
          [(tinyC v:val) v]
          )]
       [_ *fail*]
       )]

    [(tinyC x:var)
     (match (lookup-var x F)
       [(tinyC l:loc)
        (match (lookup-mem l m)
          [(tinyC v:val) v]
          [_ *fail*]
          )]
       [_ *fail*])]

    [(tinyC (& lv:lval)) ; Is this right?
     (eval-lval lv F m)
     ]

    [(tinyC (op:binop e1:expr e2:expr))
     (do (<- v1 (eval-expr e1 F m))
         (<- v2 (eval-expr e2 F m))
         (eval-binop op v1 v2))
     ]
    ))


; Evaluate a list of expressions to produce a list of values
(define/contract (eval-exprs args ctx)
  ; Note: for some reason, using the contract (listof any/c) on symbolic values
  ; is different than list; listof produces (assert: both branches infeasible)
  ;
  ; TODO: lift listof to symbolic stuff?
  (-> list? #;(listof syntax-expr?) tinyC-context? (failure/c (listof tinyC-val?)))
  (let* ([F (context->top-frame ctx)]
         [m (context->memory ctx)]
         [ms-maybe (map (λ (e) (eval-expr e F m)) args)])
    (if (any-failure? ms-maybe)
        *fail*
        ms-maybe)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Cleanup and stack management ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




; Remove a location from memory. Will return *fail* if x does not occur in m
(define/contract (drop-loc-ident x m)
  (-> tinyC-loc-ident? tinyC-memory? (failure/c tinyC-memory?))
  (match m
    [(tinyC nil) *fail*]
    [(tinyC (cons (y:loc-ident obj:object) m+:memory))
     (if (equal? x y)
         m+
         (do (<- m++ (drop-loc-ident x m+))
             (tinyC (cons (,y ,obj) ,m++)))
         )]
    ))

; Free all the locations allocated in F.
; If any of those locations do not occur in m, return *fail*
(define/contract (pop-stack F m)
  (-> tinyC-frame? tinyC-memory? (failure/c tinyC-memory?))
  (match F
    [(tinyC nil) m]
    [(tinyC (cons (_:var (x:loc-ident _:object)) F+:frame))
     (do (<- m+ (drop-loc-ident x m))
         (pop-stack F+ m+))]
    ))


; Return the declaration associated with the name p in g
(define/contract (lookup-in-global-store g p)
  (-> tinyC-global-store? syntax-proc-name? (failure/c tinyC-declaration?))
  (match g
    [(tinyC nil) *fail*]
    [(tinyC (cons decl:declaration g+:global-store))
     (if (equal? (declaration->name decl) p)
         decl
         (lookup-in-global-store g+ p)
         )]
    ))

; Check that a value v has a type ty, including pointers that might be included
; in m
(define/contract (check-type? ty obj m)
  (-> syntax-type? tinyC-object? tinyC-memory? boolean?)
  (or (equal? obj (tinyC undef))
  (match ty
    [(tinyC int) (integer? obj)]
    [(tinyC (* ty+:type))
     (do (tinyC-loc? obj)
         (<- obj+ (lookup-mem obj m))
         (check-type? ty+ obj+ m)
         )]
    [(tinyC (array ty+:simple-type len:integer))
     (let ([objs (seec->list obj)])
       (and (= (length objs) len)
            (andmap (λ (obj+) (check-type? ty+ obj+ m))
                    objs)))]
    )))


; Allocate a fresh location identifier and bind it to the object obj in memory
(define/contract (alloc obj st)
  (-> tinyC-object? state? (failure/c (cons/c tinyC-loc-ident? state?)))
  (match (fresh-var st)
    [(cons lid st+)
     (let* ([ctx (state->context st+)]
            [m  (context->memory ctx)]
            [m+ (tinyC ((,lid ,obj) ,m))]
            [ctx+ (update-context-memory ctx m+)]
            )
       (cons lid (update-state st+ #:context ctx+)))]
     [_ *fail*]
     ))

; Take as input an object of type ty and allocate a memory location l↦obj in
; memory, returning l. If ty is an array type, instead allocate the array in
; memory with l2↦obj and generate a fresh memory location l1↦l2.
(define/contract (alloc-object ty obj st)
  (-> syntax-type?
      tinyC-object?
      state?
      (failure/c (cons/c tinyC-loc? state?)))
  (match ty
    [(tinyC simple-type)
     (do (<- l-st (alloc obj st))
         (<- l    (lid->loc (car l-st)))
       (cons l (cdr l-st))
       )]

    [(tinyC (array ty+:simple-type len:integer))
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
  (-> (listof (list/c syntax-var? syntax-type? tinyC-object?))
      state?
      (failure/c (cons/c tinyC-frame? state?)))

  (cond
    [(empty? decls) (cons seec-empty st)]

    [else (match (first decls)
            [(list x ty obj)
             (do (<- l-st+  (alloc-object ty obj st))
                 (<- l      (car l-st+))
                 (<- F-st++ (alloc-declarations (rest decls)
                                                (cdr l-st+)))
                 (<- F      (car F-st++))
                 (<- F+     (seec-cons (tinyC (,x ,l))
                                       F))
                 (cons F+ (cdr F-st++)))]
            )]
    ))


(define/contract (alloc-param-declarations decls vs st)
  (-> (listof tinyC-param-decl?)
      (listof tinyC-val?)
      state?
      (failure/c (cons/c tinyC-frame? state?)))

  ; Check that the values have appropriate type and zip together the
  ; declarations and values to provide to alloc-declarations
  (let ([decl-vs (map (λ (decl v)
                        (match decl
                          [(tinyC (x:var ty:simple-type))
                           (do (check-type? ty v (context->memory (state->context st)))
                               (list x ty v))]
                          ))
                      decls
                      vs)])
    (alloc-declarations decl-vs st)))

    
(define/contract (alloc-local-declarations decls st)
  (-> (listof tinyC-local-decl?)
      state?
      (cons/c tinyC-frame? state?))

  ; Construct an appropriate input to alloc-declarations by constructing initial
  ; values for each type
  (let ([decl-vs (map (λ (decl)
                        (match decl
                          [(tinyC (x:var ty:type))
                           (list x ty (init-value ty))]
                          ))
                      decls)])
    (alloc-declarations decl-vs st)))

; Allocate a frame and update the memory associated with a particular function
; declaration
(define/contract (alloc-frame decl vs st)
  (-> tinyC-declaration? (listof tinyC-val?) state? (failure/c state?))

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
             [ctx++ (tinyC ((,F ,S) ,m))]
             )
        ; We need to pass along the state here because of the fresh
        ; variable counter. Alternately, we could consider a version of tinyC
        ; that uses symbolic variables and a fresh assertion constraint
        (update-state st+ #:context ctx++)
        ))))


;;;;;;;;;;;;;;;;;;;;;;;;;
;; Evaluate statements ;;
;;;;;;;;;;;;;;;;;;;;;;;;;

; Take a single step
(define/contract (eval-statement-1 g stmt st)
  (-> tinyC-global-store? tinyC-statement? state? (failure/c state?))

  (for/all ([stmt stmt])
  (debug-display "(eval-statement-1 ~a)~n" stmt)
  (match stmt

    [(tinyC SKIP) ; SKIP cannot take a step
     *fail*]

    [(tinyC (ASSIGN lv:lval e:expr))
     (let* ([ctx (state->context st)]
            [F (ctx->top-frame ctx)]
            [m (ctx->mem ctx)])
       (do (<- l    (eval-lval lv F m))
           (<- v    (eval-expr e F m))
           (<- ctx+ (set-lval l v ctx))
           (update-state st
                         #:statement (tinyC SKIP)
                         #:context ctx+
                         )
           ))]


    [(tinyC (OUTPUT e:expr))
     (do (<- ctx (state->context st))
         (<- v (eval-expr e (ctx->top-frame ctx) (ctx->mem ctx)))
         (update-state st #:trace (seec-singleton v)
                          #:statement (tinyC SKIP))
       )]

    [(tinyC (INPUT e:expr))
     (let* ([ctx (state->context st)]
            [F (ctx->top-frame ctx)]
            [m (ctx->mem ctx)]
            [input (state-input-buffer st)]
            )
       (cond
         [(and (list? input)
               (not (empty? input)))
          (do (<- v (eval-expr e F m))
              (<- ctx+ (set-lval v (car input) ctx))
              (update-state st
                            #:statement (tinyC SKIP)
                            #:context ctx+
                            #:input-buffer (cdr input)
                            ))]
            [else *fail*]
            ))]

    ;; Procedure calls ;;

    [(tinyC (CALL p:proc-name args:list<expr>))
    ; Invoke the procedure, allocating memory for p's local variables and
    ; pushing the current stack frame and remaining instructions onto the stack
     (do (<- decl (lookup-in-global-store g p))
         (<- body (declaration->body decl))
         (<- vs   (eval-exprs (seec->list args) (state->context st)))
         (<- st+  (alloc-frame decl vs st))
         (update-state st+
                       #:statement (tinyC (SEQ ,body RETURN))
                       )
         )]

    ; Return from a function call and pop the top-most frame
    [(tinyC RETURN)
     (match (state->context st)
       [(tinyC ((F0:frame (cons F+:frame S:stack)) m:memory))
        (let* ([m+ (pop-stack F0 m)]
               [ctx+ (tinyC ((,F+ ,S) ,m+))])
          (update-state st
                        #:statement (tinyC SKIP)
                        #:context ctx+)
          )])]


    ;; Control flow ;;

    [(tinyC (IF b:expr t:statement f:statement))
     (let* ([ctx (state->context st)]
            [F   (context->top-frame ctx)]
            [m   (context->memory ctx)])
     (match (eval-expr b F m)
       [(tinyC 1)
        (update-state st #:statement t)]
       [(tinyC 0)
        (update-state st #:statement f)]
       [_ *fail*]
       ))]

    [(tinyC (WHILE b:expr w:statement))
     (let* ([ctx (state->context st)]
            [F   (context->top-frame ctx)]
            [m   (context->memory ctx)])
     (match (eval-expr b F m)
       [(tinyC 1)
        (update-state st  #:statement (tinyC (SEQ ,w (WHILE ,b ,w))))]
       [(tinyC 0)
        (update-state st  #:statement (tinyC SKIP))]
       [_ *fail*]
       ))]

    ; Sequencing
    [(tinyC (SEQ SKIP stmt+:statement))
     (update-state st #:statement stmt+)]

    [(tinyC (SEQ stmt1:statement stmt2:statement))
     (do (<- st1 (update-state st #:statement stmt1))
         (<- st1+ (eval-statement-1 g stmt1 st1))
         (update-state st1+ #:trace (state->trace st1+)
                            #:statement (tinyC (SEQ ,(state->statement st1+) ,stmt2))
                            ))]


    )))


(define/contract (decrement-fuel fuel)
  (-> (or/c #f integer?) (or/c #f integer?))
  (if fuel
      (- fuel 1)
      #f))

(define (CALL? insn)
  (match insn
    [(tinyC (CALL any any)) #t]
    [_ #f]))


;; Take some number of steps bounded by the amount of fuel given
(define/contract (eval-statement fuel g st)
  (-> (or/c integer? #f) tinyC-global-store? state? (failure/c state?))
  (for/all ([stmt (state->statement st)])
  (debug-display "=====================")
  (debug-display "(eval-statement ~a ~a)" fuel stmt)
  (cond
    [(equal? stmt (tinyC SKIP))
     st] ; Evaluation has normalized before fuel ran out

    [(<= fuel 0) st] ; Fuel ran out. Return *fail* here instead?

    [else (do (<- st+ (eval-statement-1 g stmt st))
              (eval-statement (decrement-fuel fuel) g st+))]
    )))


(define max-fuel (make-parameter 100))

(define run+
  (λ (prog    ; A seec list of declarations (aka global store)
      inputs  ; A seec list of inputs to main
      buf     ; A racket list of seec lists to pass to INPUT
      )
    (eval-statement (max-fuel)
                    prog
                    (update-state (init-state (tinyC ((nil nil) nil)))
                                  #:statement (tinyC (CALL "main" ,inputs))
                                  #:input-buffer buf
                                  ))))

(define run
  (λ (prog    ; A racket list of declarations
      inputs  ; A racket list of inputs to main
      buf     ; A racket list of seec lists to pass to INPUT
      )
    (run+ (list->seec prog)
          (list->seec inputs)
          buf)))


(define/contract (make-declaration name params locals statements)
    (-> string? (listof tinyC-param-decl?)
                (listof tinyC-local-decl?)
                (listof tinyC-statement?)
                tinyC-declaration?)
    (tinyC (,name ,(list->seec params) ,(list->seec locals) ,(list->seec statements))))


(define-language tinyC-lang
  #:grammar tinyC
  #:expression global-store #:size 5
  #:context env #:size 4 ; The trace acts like an argument list. Should we add
                         ; a constraint that these should contain only
                         ; integers, not locations?
  #:link (λ (env prog) #;(cons args prog)
            (match env
              [(tinyC (args:intlist buf:list<intlist>))
               (list prog args (seec->list buf))]))

  ; During evaluation, just produce the trace
  #:evaluate (λ (p) (do st <- (run+ (first p) (second p) (third p))
                        (state-trace st)))
  )

; find-gadget(behav): ∃ e, ∀ ctx, behavior(ctx[e]) = behav
;
; ∃ ctx ∀ e, e = simple-call-example -> behavior(ctx[e]) = behav
;
; Perhaps just switch context and expressions
