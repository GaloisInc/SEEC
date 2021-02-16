#lang seec
#;(require racket/base)
(require racket/contract)
(require (only-in racket/base
                  make-parameter
                  ))
(require rosette/lib/value-browser)

(require (only-in racket/base
                  [make-string unsafe:make-string]
                  ))
(require (only-in seec/private/string
                  char->string))
(require (prefix-in safe:
                    (file "printf-spec.rkt")))


(provide printf-lang
         printf-impl
         val->number
         val->loc
         conf->acc
         conf->mem
         behavior->trace
         behavior->config
         context->config
         context->arglist
         printf-program?
         program->fmt
         program->context
         program->arglist
         program->config
         make-program
         make-context
         make-config
         make-config-triv
         make-behav
         make-behav-triv
         lookup-offset
         lookup-loc
         eval-expr
         config-add
         mem-update
         (rename-out [interp-fmt-unsafe interp-fmt])
         (rename-out [printf-lang-ident? ident?]
                     [printf-lang-val? val?]
                     [printf-lang-expr? expr?]
                     [printf-lang-arglist? arglist?]
                     [printf-lang-mem? mem?]
                     [printf-lang-trace? trace?]
                     [printf-lang-constant? const?]
                     [printf-lang-behavior? behavior?]
                     [printf-lang-config? config?]
                     [printf-lang-context? context?]
                     )
         err?
         debug?
         fmt-consistent-with-arglist?
         )

; We aim to eventually support all or most of the syntax for printf formats:
;
; %[parameter][flags][width][.precision][length]type
; 
; We currently support:
; - All parameters (e.g. index into argument list) are explicit
; - Types include d (integers) and n (write value of current accumulator to memory)
; - Optional width argument (pad output by a certain amount)
;
; printf("%d",20)
;   ==> evaluates to "20"
;   ==> fmt-elt = (printf-lang (cons (% (0 $) NONE d) nil))
;                                       ^-- explicit parameter argument:
;                                        -- offset into arg-list
;       arglist = (printf-lang (cons 20 nil))
;
; printf("%*d",20,4) ==> 
;   ==> evaluates to "0020" (pads argument so its length is at least 4)
;   ==> fmt-elt = (printf-lang (cons (% 0 $ (* 1) d) nil))
;                                              ^-- explicit width argument:
;                                               -- offset into arg-list
;       arglist = (printf-lang (cons 20 (cons 4 nil)))
;
; Goal: Specification language expects the number and type of arguments to line
;       up with the requirements of the format string
;
;       Implementation language will do nothing (output "") if number of
;       arguments don't line up. In the future, we will incorporate stack layout
;       so when not enough arguments are provided, execution will access stack
;       variables.
;
;       If the type of arguments don't line up, the implementation language will
;       interpret constant numbers as pointers into memory and vice versa.

(define-grammar printf-lang
  #:extends safe:fmt-string

  (arglist ::= list<expr>)
  (expr ::= (LOC ident) (* expr) bitvector string)
  #;(mem ::= mnil (mcons ident val mem))
  (mem-elem ::= (ident val))
  (mem ::= list<mem-elem>)
  (val ::= (LOC ident) bitvector string ERR #;(DEREF val))
  ; use signed bitvectors to represent integers in certain places
  (ident ::= integer)
  (trace ::= list<constant>)
  (constant ::= string integer (pad-by natural))
  ; a configuration consists of an accumulator and a memory value
  (config ::= (bitvector mem))
  (context ::= (arglist config))
  (behavior ::= (trace config))
  )


(define debug? (make-parameter #f))
(define (debug stmt)
  (if (debug?)
      (stmt)
      (void)))

#||||||||||||||||||||||||||||#
#| Projections out of types |#
#||||||||||||||||||||||||||||#

(define (loc? v)
  #;(-> any/c boolean?)
  (match v
    [(printf-lang (LOC l:ident)) #t]
    [_ #f]
    ))
(define (err? x)
  #;(-> any/c boolean?)
  (match x
    [(printf-lang ERR) #t]
    [_ #f]))
(define (natural? n)
  (and (integer? n)
       (>= n 0)))


(define (val->number v)
  #;(-> printf-lang-bitvector? integer?)
  (match v
    [(printf-lang n:bitvector) (bitvector->integer n)]
    #;[_ (raise-argument-error 'val->number "printf-lang-bitvector?" v)]
    ))
(define (val->loc v)
  #;(-> loc? printf-lang-ident?)
  (match v
    [(printf-lang (LOC x:ident)) x]
    ))
(define (conf->mem c)
  #;(-> printf-lang-config? printf-lang-mem?)
  (match c
    [(printf-lang (bitvector m:mem)) m]
    ))
(define (conf->acc c)
  #;(-> printf-lang-config? bv?)
  (match c
    [(printf-lang (acc:bitvector mem)) acc]
    #;[_ (raise-argument-error 'conf->acc "conf" c)]
    ))

(define (behavior->trace b)
  #;(-> printf-lang-behavior? printf-lang-trace?)
  (match b
    [(printf-lang (t:trace config)) t]))
(define (behavior->config b)
  #;(-> printf-lang-behavior? printf-lang-config?)
  (match b
    [(printf-lang (trace c:config)) c]
    ))

(define (make-context args conf)
  (printf-lang (,args ,conf)))
(define (make-config n m)
  #;(-> integer? printf-lang-mem? printf-lang-config?)
  (printf-lang (,(integer->bv n) ,m)))
(define (make-config-triv n)
  (make-config n (printf-lang nil)))
(define (make-behav t n m)
  #;(-> printf-lang-trace? integer? printf-lang-mem? printf-lang-behavior?)
  (printf-lang (,t ,(make-config n m))))
(define (make-behav-triv t n)
  (printf-lang (,t ,(make-config-triv n))))

(define (context->config ctx)
  #;(-> printf-lang-context? printf-lang-config?)
  (match ctx
    [(printf-lang (args:arglist cfg:config)) cfg]
    ))
(define (context->arglist ctx)
  #;(-> printf-lang-context? printf-lang-arglist?)
  (match ctx
    [(printf-lang (args:arglist cfg:config)) args]
    ))
; a printf-program is a racket pair of a context and a format string
(define (printf-program? p)
  (and (pair? p)
       (printf-lang-context? (car p))
       (safe:fmt? (cdr p))
       ))
(define (program->fmt p)
  #;(-> printf-program? safe:fmt?)
  (cdr p))
(define (program->context p)
  #;(-> printf-program? printf-lang-context?)
  (car p))
(define (program->arglist p)
  #;(-> printf-program? printf-lang-arglist?)
  (context->arglist (car p)))
(define (program->config p)
  #;(-> printf-program? printf-lang-config?)
  (context->config (car p)))
(define (make-program f args conf)
  #;(-> safe:fmt? printf-lang-arglist? printf-lang-config? printf-program?)
  (cons (printf-lang (,args ,conf)) f))



#;(define (bonsai-string-append s1 s2)
  #;(-> bonsai-string? bonsai-string? bonsai-string?)
  (bonsai-string (string-append (bonsai-string-value s1) (bonsai-string-value s2))))


#|||||||||||||||||||||||||||||#
#| Operations on printf-lang |#
#|||||||||||||||||||||||||||||#

; INPUT: a location identifier l and a memory value m with l in the domain of m
; OUTPUT: the value mapped to by the identifier
(define (lookup-loc l m)
  #;(-> printf-lang-ident? printf-lang-mem? (or/c err? printf-lang-val?))
  (debug (thunk (printf "(lookup-loc ~a ~a)~n" l m)))
  (match m
    [(printf-lang nil) (printf-lang ERR)]
    [(printf-lang (cons (l0:ident v0:val) m0:mem))
     (if (equal? l l0)
         v0
         (lookup-loc l m0))]
    ))

(define (eval-expr e m)
  #;(-> printf-lang-expr? printf-lang-mem? (or/c err? printf-lang-val?))
  (debug (thunk (printf "(eval-expr ~a ~a)~n" e m)))
  (match e
    [(printf-lang v:val) v]
    [(printf-lang (* e+:expr))
     (match (eval-expr e+ m)
       [(printf-lang (LOC l:ident)) (lookup-loc l m)]
       [_ (printf-lang ERR)]
       )]
    ))

; INPUT: an integer offset and an argument list args such that offset < length(args)
; OUTPUT: the value mapped to the offset
(define (lookup-offset offset ctx)
  #;(-> integer? printf-lang-context? (or/c err? printf-lang-val?))
  (debug (thunk (printf "(lookup-offset ~a ~a)~n" offset ctx)))
  (define res 
    (let ([args (context->arglist ctx)]
          [conf (context->config ctx)]
          )
      (match args
        [(printf-lang nil) (printf-lang ERR)]
        [(printf-lang (cons e:expr args+:arglist))
         (cond
           [(< offset 0) (printf-lang ERR)]
           [(= offset 0) (eval-expr e (conf->mem conf))]
           [else         (lookup-offset (- offset 1) (make-context args+ conf))]
           )])))
  (debug (thunk (printf "result of lookup-offset: ~a~n" res)))
  res
  )


; INPUT: a configuration (acc,mem) and a number n
; OUTPUT: a new configuration (acc+n,mem)
(define (config-add conf n)
  #;(-> printf-lang-config? integer? printf-lang-config?)
  (debug (thunk (printf "(config-add ~a ~a)~n" conf n)))
  (let* ([acc   (conf->acc conf)]
         [m     (conf->mem conf)]
         [n-bv  (integer->bv n)]
         [acc+n (bvadd acc n-bv)]
         )
    (begin
      ; uncomment to avoid overflow
      #;(assert (<= acc acc+n))
      (printf-lang (,acc+n ,m))
      )
    ))


; INPUT: a mem, a location, and a value
; OUTPUT: an updated memory with the location mapping to the new value
(define (mem-update m l v)
  #;(-> printf-lang-mem? printf-lang-ident? printf-lang-val? printf-lang-mem?)
  (printf-lang (cons (,l ,v) ,m)))



  #;(render-value/window n)
  #;(if (or (union? n) (term? n))
      (abstract-defn n)
      (concrete-defn n)
      )

  
; If the constant is a string, give the length of the string
; If the constant is an integer (represented by a bitvector) give the length of
; the string representing the number.
(define (constant-length c)
  #;(-> printf-lang-constant? integer?)
  (debug (thunk (printf "(constant-length ~a)~n" c)))
  (define res (match c
    [(printf-lang s:string)   (string-length s)]
    [(printf-lang n:integer)  (string-length (number->string n))]
    [(printf-lang (pad-by n:natural)) n]
    ))
  (debug (thunk (printf "Computed constant-length: ~a~n" res)))
  res)


; INPUT: a config OR behavior conf-or-behav and constant c
; OUTPUT: a behavior consisting of the trace containing n and the upated configuration
(define (print-constant conf-or-behav c)
  #;(-> (or/c printf-lang-config? printf-lang-behavior?) printf-lang-constant? printf-lang-behavior?)
  (debug (thunk (printf "(print-constant ~a ~a)~n" conf-or-behav c)))
  (define res (match conf-or-behav
    [(printf-lang conf:config)
     (let* ([len-c (constant-length c)]
            [conf+ (config-add conf len-c)]
            )
       (printf-lang ((cons ,c nil) ,conf+)))]
    [(printf-lang (t:trace conf:config))
     (let* ([len-c (constant-length c)]
            [conf+ (config-add conf len-c)]
            )
       (printf-lang ((cons ,c ,t) ,conf+)))]
    )
  )
  (debug (thunk (printf "computed print-constant: ~a~n" res)))
  res
  )
; Input: t is either a trace or ERR
(define (print-trace conf t)
  #;(-> printf-lang-config? (or/c err? printf-lang-trace?) (or/c err? printf-lang-behavior?))
  (debug (thunk (printf "(print-trace ~a ~a)~n" conf t)))
  (define res (match t
    [(printf-lang ERR) t]
    [(printf-lang nil) (printf-lang (nil ,conf))]
    [(printf-lang (cons c:constant t+:trace))
     (match (print-trace conf t+)
       [(printf-lang ERR) (printf-lang ERR)]
       [(printf-lang behav:behavior)
        (print-constant behav c)]
       )]
    #;[_ (raise-argument-error 'print-trace "printf-lang-trace?" t)]
    ))
  (debug (thunk (printf "result of print-trace: ~a~n" res)))
  res)



; INPUT: a config conf and a location identifier l
; OUTPUT: an updated configuration that assigns l the value of the accumulator.
(define (print-n-loc conf l)
  #;(-> printf-lang-config? printf-lang-ident? printf-lang-config?)
  (debug (thunk (printf "(print-n-loc ~a)~n" l)))
  (let* ([acc (conf->acc conf)]
         [new-mem (mem-update (conf->mem conf) l acc)]
         )
    (printf-lang (,acc ,new-mem))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an concrete "unsafe" implementation of printf                          ;
;                                                                               ;
; If an argument in the format string is not in scope with respect to the       ;
; argument list, or if it maps to a value of the wrong type, it will return the ;
; empty string and proceed silently.                                            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (unsafe:ident->number l)
  #;(-> printf-lang-ident? integer?)
  l
  #;(match l
    [(printf-lang x:integer) x]
    ))

(define (unsafe:val->integer v)
  #;(-> printf-lang-val? integer?)
  (debug (thunk (printf "(unsafe:val->integer ~a)~n" v)))
  (define res (match v
    [(printf-lang n:bitvector)       (bitvector->integer n)]
    ; if the value is a location, we interpret the location as an integer
    [(printf-lang (LOC l:ident))     (unsafe:ident->number l)]
    ; for strings, `s` is a boxed string from string.rkt, aka a list of
    ; characters, aka a list of integers. Therefore, interpreting a string as an
    ; integer is just the integer value of the first character in the string. If
    ; the string is the empty string, instead produce 0.
    [(printf-lang s:string)      (if (equal? (string-length s) 0)
                                     0
                                     (char->ascii (first (string->char-list s)))
                                     )]
    ))
  (debug (thunk (printf "result of unsafe:val->integer: ~a~n" res)))
  res)

(define (unsafe:val->natural v)
  #;(-> printf-lang-val? integer?)
  (debug (thunk (printf "(unsafe:val->natural ~a)~n" v)))
  (define res (match v
    [(printf-lang n:bitvector) (bitvector->natural n)]
    [_                         (unsafe:val->integer v)]
    ))
  (debug (thunk (printf "result of unsafe:val->integer: ~a~n" res)))
  res)


#;(define (unsafe:val->string v)
  #;(-> printf-lang-val? string?)
  (debug (thunk (printf "(unsafe:val->string ~a)~n" v)))
  (define (unsafe:char->string x)
    (cond
      [(char? x) (char->string x)]
      [else      (string "")]
      ))
  (define res (match v
    [(printf-lang s:string) s]
    ; for an integer or location, interpret the integer as a character. In
    ; actuality C would expect a null-terminated string in memory, so it would
    ; actually not stop at the single value, but we aren't modeling that for
    ; now.
    [(printf-lang n:bitvector)       (unsafe:char->string (bitvector->integer n))]
    [(printf-lang (LOC l:ident)) (unsafe:char->string (unsafe:ident->number l))]
    ))
  (debug (thunk (printf "result of unsafe:val->string: ~a~n" res)))
  res)

(define (unsafe:fmt->constant ftype param ctx)
  #;(-> safe:fmt-type? safe:parameter? printf-lang-context? (or/c err? printf-lang-constant?))
  (debug (thunk (printf "(unsafe:fmt->constant ~a ~a ~a)~n" ftype param ctx)))
  (define res (match (lookup-offset (safe:param->offset param) ctx)
    [(printf-lang ERR) (printf-lang ERR)]
    [(printf-lang v:val)
     (match ftype
       ; if ftype = 'd', interpret the argument as an integer
       [(printf-lang %d) (unsafe:val->integer v)]
       ; if ftype = 's', interpret the argument as a string
       [(printf-lang %s)
        (match v
          [(printf-lang s:string) v]
          [_                      (printf-lang ERR)]
          )]
       ; if ftype = 'n', interpret the argument as a location aka an integer
       [(printf-lang %n) (printf-lang ,(unsafe:val->integer v))]
       )]))
  (debug (thunk (printf "result of unsafe:fmt->constant: ~a~n" res)))
  res
  )

; INPUT: a format string, a stack (we assume that the arguments have been pushed
; onto the stack), and a configuration
;
; OUTPUT: an outputted trace and a configuration
(define (interp-fmt-elt-unsafe f ctx)
  #;(-> safe:fmt-elt? printf-lang-context? printf-lang-behavior?)
  (debug (thunk (printf "(interp-fmt-elt-unsafe ~a ~a)~n" f ctx)))
  (define conf (context->config ctx))
  (define res (match f

    [(printf-lang s:string)
     (print-constant conf s)
     ]

    ; the width parameter doesn't make a difference for n formats
    [(printf-lang (%n (p:parameter _:width)))
     (match (unsafe:fmt->constant (printf-lang %n) p ctx)
       [(printf-lang ERR)     (printf-lang (nil ,conf))]
       [(printf-lang l:ident) (printf-lang (nil ,(print-n-loc conf l)))]
       )]

    ; for d and n format types, we will first calculate the constant associated
    ; with the format type, and then pad it by the appropriate amount
    [(printf-lang (ftype:fmt-type (p:parameter NONE)))
     (match (unsafe:fmt->constant ftype p ctx)
       [(printf-lang ERR)        (printf-lang (nil ,conf))]
       [(printf-lang c:constant) (print-constant conf c)]
       )]

    [(printf-lang (ftype:fmt-type (p:parameter w:natural)))
     (match (unsafe:fmt->constant ftype p ctx)
       [(printf-lang ERR)        (printf-lang (nil ,conf))]
       [(printf-lang c:constant)
        (print-trace conf (safe:pad-constant c w))]
       )]

    [(printf-lang (ftype:fmt-type (p:parameter (* o:offset))))
     (match (lookup-offset o ctx)
       ; if o is greater than the length of the argument list, no-op
       [(printf-lang ERR)   (printf-lang (nil ,conf))]
       [(printf-lang v:val)
        (match (unsafe:fmt->constant ftype p ctx)
          [(printf-lang ERR) (printf-lang (nil ,conf))]
          [(printf-lang c:constant)
           ; if c is a negative signed bitvector: interpret the bitvector as
           ; overflow???? is this right?
           (print-trace conf (safe:pad-constant c (unsafe:val->natural v)))]
          )]
       )]

    #;[_ (raise-argument-error 'interp-fmt-elt-unsafe "(printf-lang fmt-elt)" f)]
    ))
  (debug (thunk (printf "result of interp-fmt-elt-unsafe: ~a~n" res)))
  res
  )
(define (interp-fmt-unsafe f args conf)
  #;(-> safe:fmt? printf-lang-arglist? printf-lang-config? printf-lang-behavior?)
  (debug (thunk (printf "(interp-fmt-unsafe ~a ~a ~a)~n" f args conf)))
  (define res (match f
    [(printf-lang nil) (printf-lang (nil ,conf))]

    [(printf-lang (cons f1:fmt-elt f+:fmt))

     (let* ([b1 (interp-fmt-elt-unsafe f1 (make-context args conf))]
            [b2 (interp-fmt-unsafe f+ args (behavior->config b1))]
            [t+ (seec-append (behavior->trace b1) (behavior->trace b2))]
            )
       (printf-lang (,t+ ,(behavior->config b2))))
     ]
    ))
  (debug (thunk (printf "result of interp-fmt-unsafe: ~a~n" res)))
  res)


#|||||||||||||||||||||||||||||||||||||#
#| Classifiers for printf-lang forms |#
#|||||||||||||||||||||||||||||||||||||#


; p is the parameter offset as a bonsai number
; ftype is the format type associated with the parameter
(define (parameter-consistent-with-arglist p ftype ctx)
  #;(-> safe:parameter? safe:fmt-type? printf-lang-context? boolean?)
  (let* ([offset (safe:param->offset p)]
         [arg (lookup-offset offset ctx)])
    (and (< offset (seec-length (context->arglist ctx)))
         (match (cons ftype arg)
           [(cons (printf-lang %d) (printf-lang bitvector))   #t]
           [(cons (printf-lang %n) (printf-lang (LOC ident))) #t]
           [(cons (printf-lang %s) (printf-lang string))      #t]
           [_                                                #f]
           ))))
(define (width-consistent-with-arglist w ctx)
  #;(-> safe:fmt-string-width? printf-lang-context? boolean?)
  (match w
    [(printf-lang NONE) #t]
    [(printf-lang natural) #t]
    [(printf-lang (* o:offset))
     (and (< o (seec-length (context->arglist ctx)))
          (printf-lang-bitvector? (lookup-offset o ctx)))]
    ))


(define (fmt-consistent-with-arglist? f ctx)
  (define (fmt-elt-consistent-with-arglist? f0)
    (match f0
      [(printf-lang string) #t]

      [(printf-lang (ftype:fmt-type (p:parameter w:width)))
       (and (parameter-consistent-with-arglist p ftype ctx)
            (width-consistent-with-arglist w ctx))]
      ))
  (match f
    [(printf-lang nil) #t]
    [(printf-lang (cons f0:fmt-elt f+:fmt))
     (and (fmt-elt-consistent-with-arglist? f0)
          (fmt-consistent-with-arglist? f+ ctx))]
    ))


(define-language printf-impl
  #:grammar printf-lang
  #:expression fmt #:size 3
  #:context context #:size 5
  #:link cons
  #:evaluate (λ (p) (interp-fmt-unsafe (program->fmt p)
                                       (program->arglist p)
                                       (program->config p)))
  )
