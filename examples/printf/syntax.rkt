#lang seec
#;(require racket/base)
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))
(require rosette/lib/value-browser)

(require (only-in racket/base
                  [make-string unsafe:make-string]
                  ))
(require (only-in seec/private/bonsai2
                  bonsai-pretty))
(require (only-in seec/private/string
                  char->string))

(provide printf-lang
         bonsai->number
         val->number
         val->loc
         conf->acc
         conf->mem
         behavior->trace
         behavior->config
         lookup-offset
         lookup-loc
         config-add
         mem-update
         interp-fmt-safe
         interp-fmt-unsafe
         fmt?
         ident?
         val?
         arglist?
         mem?
         conf?
         fmt-consistent-with-arglist?

         ll-singleton
         ll-cons
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
  (fmt ::= list<fmt-elt>)
  (fmt-elt ::= string (% parameter width fmt-type))
  (parameter ::= (offset $))
  (width ::= NONE (* offset) natural)
  (offset ::= natural)
  (fmt-type ::= s d n)

  (arglist ::= list<val>)
  (mem ::= mnil (mcons ident val mem))
  (val ::= (LOC ident) bvint string ERR #;(DEREF val))
  ; use signed bitvectors to represent integers in certain places
  (bvint ::= bitvector)
  ; TODO: should idents be implemented as bitvectors?
  (ident ::= integer)
  (trace ::= list<constant>)
  (constant ::= string integer (pad-by natural))
  ; a configuration consists of an accumulator and a memory value
  (config ::= (bvint mem))
  (context ::= (arglist config))
  (behavior ::= (trace config))
  )

  #;(behavior ::= (string config))


(define (ll-singleton x) (printf-lang (cons ,x nil)))
(define (ll-cons x xs) (printf-lang (cons ,x ,xs)))

(define (debug stmt)
  #;(stmt)
  (void)
  )

#||||||||||||||||||||||||||||#
#| Projections out of types |#
#||||||||||||||||||||||||||||#


(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    [_ (raise-argument-error 'bonsai->number "bonsai-integer?" n)]
    ))

(define (bonsai->bv b) (bonsai-bv-value b))

(define (bvint->number n) (bitvector->integer (bonsai->bv n)))
(define (number->bvint n) (integer->bonsai-bv n))
(define (val->number v)
  (match v
    #;[(printf-lang n:integer) (bonsai->number n)]
    [(printf-lang n:bvint) (bvint->number n)]
    [_ (raise-argument-error 'val->number "(printf-lang integer)" v)]
    ))
(define (val->loc v)
  (match v
    [(printf-lang (LOC x:ident)) x]
    [_ (raise-argument-error 'val->loc "(printf-lang (LOC ident))" v)]
    ))
(define (conf->mem c)
  (match c
    [(printf-lang (bvint m:mem)) m]
    [_ (raise-argument-error 'conf->mem "conf" c)]
    ))

(define (conf->acc c)
  (match c
    [(printf-lang (acc:bvint mem)) (bonsai->bv acc)]
    [_ (raise-argument-error 'conf->acc "conf" c)]
    ))

(define (param->offset param)
  (match param
    [(printf-lang (o:offset $)) (bonsai->number o)]
    ))


(define (behavior->trace b)
  (match b
    [(printf-lang (t:trace config)) t]))
(define (behavior->config b)
  (match b
    [(printf-lang (trace c:config)) c]
    ))
(define (behavior? b)
  (match b
    [(printf-lang behavior) #t]
    [_ #f]
    ))

(define (bonsai-string-append s1 s2)
  (bonsai-string (string-append (bonsai-string-value s1) (bonsai-string-value s2))))


#|||||||||||||||||||||||||||||#
#| Operations on printf-lang |#
#|||||||||||||||||||||||||||||#

; INPUT: an integer offset and an argument list args such that offset < length(args)
; OUTPUT: the value mapped to the offset
(define (lookup-offset offset args)
  #;(debug (thunk (printf "(lookup-offset ~a ~a)~n" offset args)))
  (define res (match args
    [(printf-lang nil) (printf-lang ERR)]
    [(printf-lang (cons v:val args+:arglist))
     (if (<= offset 0)
         v
         (lookup-offset (- offset 1) args+))]
    ))
  #;(debug (thunk (printf "result: ~a~n" res)))
  res
  )

; INPUT: a location identifier l and a memory value m with l in the domain of m
; OUTPUT: the value mapped to by the identifier
(define (lookup-loc l m)
  (match m
    [(printf-lang mnil) (printf-lang ERR)]
    [(printf-lang (mcons l0:ident v0:val m0:mem))
     (if (equal? l l0)
         v0
         (lookup-loc l m0))]
    ))


; INPUT: a configuration (acc,mem) and a number n
; OUTPUT: a new configuration (acc+n,mem)
(define (config-add conf n)
  (debug (thunk (printf "(config-add ~a ~a)~n" conf n)))
  (let* ([acc   (conf->acc conf)]
         [m     (conf->mem conf)]
         [n-bv  (bonsai->bv (number->bvint n))]
         [acc+n (bonsai-bv (bvadd acc n-bv))]
         )
    (begin
      ; avoid overflow
      #;(assert (<= acc acc+n))
      (printf-lang (,acc+n ,m))
      )
    ))


; INPUT: a mem, a location, and a value
; OUTPUT: an updated memory with the location mapping to the new value
(define (mem-update m l v)
  (printf-lang (mcons ,l ,v ,m)))


; returns #t iff x = ceiling(log_{base} y)
;
; i.e. x-1 < log_{base} y <= x
;
; i.e. base^{x-1} < y <= base^x
#;(define (is-ceil-log? x base y)
  #;(printf "(is-ceil-log? ~a ~a ~a)~n" x base y)
  #;(printf "(number? ~a) = ~a~n" (- x 1) (number? (- x 1)))
  #;(printf "(expt ~a ~a) = ~a~n" base x (expt base x))
  ; NOTE: the problem is in (expt base x) when x is symbolic
  (and (< (expt base (- x 1) ) y)
       (<= y (expt base x)))
  )


; for positive numbers, return (ceiling (log n 10)); this is the number of characters
; it takes to represent the number as a string
; for negative numbers, add 1.
;
; Because log is not lifted in bonsai, we need to define our own operation.
; if n is symbolic, create a new symbolic integer that is the power set of n
; if n is concrete, then do a simple algorithm
#;(define (int->string-length n)
  #;(printf "(int->string-length ~a) [~a]~n" n (number? n))
  (define (concrete-defn x)
    (cond
      [(negative? x) (+ 1 (concrete-defn (* -1 x)))]
      [(<= 0 x 9) 1]
      [else (let* ([q (quotient x 10)]
                   [r (remainder x 10)])
              (+ 1 (concrete-defn q)))]
      ))
  (define (abstract-defn x)
    (define-symbolic l integer?)

    ; if x is positive, then
    ;    l = ceiling(log n 10)
    (define if-pos-val (is-ceil-log? l 10 n))

    ; if x is negative, it should be the fact that
    ;    l = ceiling(log n 10) + 1
    (define if-neg-val (is-ceil-log? (- l 1) 10 n))
    
    (assert (or (and (negative? x) if-neg-val)
                (and (positive? x) if-pos-val)))
    l
    )

  #;(render-value/window n)
  (if (or (union? n) (term? n))
      (abstract-defn n)
      (concrete-defn n)
      ))

  
; If the constant is a string, give the length of the string
; If the constant is an integer (represented by a bitvector) give the length of
; the string representing the number.
(define (constant-length c)
  (debug (thunk (printf "(constant-length ~a)~n" c)))
  (define res (match c
    [(printf-lang s:string) (string-length (bonsai-string-value s))]
    [(printf-lang n:integer)  (string-length (number->string n))]
    [(printf-lang (pad-by n:natural)) (bonsai->number n)]
    [_ (raise-argument-error 'constant-length "(printf-lang constant)" c)]
    ))
  #;(debug (thunk (printf "Computed constant-length: ~a~n" res)))
  res)


; INPUT: a string s and a behavior (t (acc m))
; OUTPUT: a behavior ((cons s t) ((+ (length s) acc) m))
#;(define (print-string s behav)
  (match behav
    [(printf-lang (t:trace (acc:integer m:mem)))
     (let* ([len-s (string-length s)]
            [acc+ (+ (bonsai->number acc) len-s)]
            )
       (printf-lang ((cons ,(bonsai-string s) ,t) (,acc+ ,m)))
       )]
    ))

; INPUT: a config OR behavior conf-or-behav and constant c
; OUTPUT: a behavior consisting of the trace containing n and the upated configuration
(define (print-constant conf-or-behav c)
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
    [_ (raise-argument-error 'print-constant "(or/c (config?) (behavior?))" conf-or-behav)]
    )
  )
  (debug (thunk (printf "computed print-constant: ~a~n" res)))
  res
  )

(define (trace? t)
  (match t
    [(printf-lang trace) #t]
    [_ #f]
    ))

; Input: t is either a trace or ERR
(define (print-trace conf t)
  (debug (thunk (printf "(print-trace ~a ~a)~n" conf t)))
  #;(debug (thunk (printf "    (trace? ~a): ~a~n" t (trace? t))))
  (define res (match t
    [(printf-lang ERR) (printf-lang ERR)]
    [(printf-lang nil) conf]
    [(printf-lang (cons c:constant t+:trace))
     (print-constant (print-trace conf t+) c)]
    [_ (raise-argument-error 'print-trace "trace?" t)]
    ))
  (debug (thunk (printf "result of print-trace: ~a~n" res)))
  res)


; INPUT: a config conf and a location identifier l
; OUTPUT: an updated configuration that assigns l the value of the accumulator.
(define (print-n-loc conf l)
  (debug (thunk (printf "(print-n-loc ~a): ~a~n" l)))
  (let* ([acc (bonsai-integer (conf->acc conf))]
         [new-mem (mem-update (conf->mem conf) l acc)]
         )
    (printf-lang (,acc ,new-mem))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an abstract "safe" implementation of printf                          ;
;                                                                             ;
; If an argument in the format string is not in scope with respect to the     ;
; argument list, or if it maps to a value of the wrong type, it will throw an ;
; error.                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; either return a behavior (trace config)
; or an ERR
#;(define (interp-ftype-safe ftype param args conf)
  #;(printf "(interp-ftype-safe ~a ~a ~a ~a)~n" ftype param args conf)
  #;(printf "(lookup-offset ~a ~a)== ~a~n" (param->offset param) args (lookup-offset (param->offset param) args))
  (define res (match (cons ftype (lookup-offset (param->offset param) args))
    ; if the type = 'd', the corresponding argument should be an integer
    ; The function `print-constant` is shared between safe and unsafe versions
    [(cons (printf-lang d) (printf-lang n:integer))
     (print-constant conf n)
     ]

    [(cons (printf-lang s) (printf-lang s:string))
     (print-constant conf s)]
    ; if the type = 'n', the correesponding argument should be a location
    ; The function `print-n-loc` is shared between safe and unsafe versions
    [(cons (printf-lang n) (printf-lang (LOC l:ident)))
     (printf-lang (nil ,(print-n-loc conf l)))
     ]

    [_ (printf-lang ERR)]
    )
  )
  #;(printf "computed interp-ftype-safe: ~a~n" res)
  res)

; returns the contant to be printed, or ERR
(define (fmt->constant ftype param args)
  (debug (thunk (printf "(fmt->constant ~a ~a ~a)~n" ftype param args)))
  (define res
    (match (cons ftype (lookup-offset (param->offset param) args))
    [(cons (printf-lang d) (printf-lang n:bvint))
     (bonsai-integer (bvint->number n))]
    [(cons (printf-lang s) (printf-lang s:string))
     s]
    [_ (printf-lang ERR)]
    ))
  (debug (thunk (printf "result of fmt->constant: ~a~n" res)))
  res)

; INPUT: a constant `c` and a natural number `w`
; OUTPUT: the trace of length max(w,len(c)) obtained by padding `c` with up to `w` spaces.
;
; TODO: do we need to use bitvectors to keep track of potential overflow? Right
; now both the constant lengths and widths are integers, rather than bitvectors.
(define (pad-constant c w)
  (debug (thunk (printf "(pad-constant ~a ~a)~n" c w)))
  (define res (let* ([c-len (constant-length c)]
         )
    (cond
      [(<= w c-len) (ll-singleton c)]
      [else         (ll-cons (printf-lang (pad-by ,(bonsai-integer (- w c-len)))) (ll-singleton c))]
      )))
  (debug (thunk (printf "result of pad-constant: ~a~n" res)))
  res)


; INPUT: a format string, an argument list, and a configuration
; OUTPUT: an outputted string and a configuration OR ERR
(define (interp-fmt-elt-safe f args conf)
  (debug (thunk (printf "(interp-fmt-elt-safe ~a ~a ~a)~n" f args conf)))
  (define res (match f
    [(printf-lang s:string)
     (print-constant conf s)]

    ; the width parameter doesn't make a difference for n formats
    [(printf-lang (% p:parameter width n))
     (match (lookup-offset (param->offset p) args)
       [(printf-lang (LOC l:ident))
        (printf-lang (nil ,(print-n-loc conf l)))
        ]
       [_ (printf-lang ERR)]
       )]

    ; otherwise, for the 's' and 'd' format types:
    [(printf-lang (% p:parameter NONE ftype:fmt-type))
     (print-constant conf (fmt->constant ftype p args))]

    [(printf-lang (% p:parameter w:natural ftype:fmt-type))
     (let* ([c (fmt->constant ftype p args)]
            [t (pad-constant c (bonsai->number w))]
            )
       (print-trace conf t))
     ]

    [(printf-lang (% p:parameter (* o:offset) ftype:fmt-type))
     (match (lookup-offset (bonsai->number o) args)
       [(printf-lang w:bvint)
        (let* ([c (fmt->constant ftype p args)]
               [t (pad-constant c (bvint->number w))]
               )
          (print-trace conf t))]
       [_ (printf-lang ERR)]
       )
     ]

    [_ (raise-argument-error 'interp-fmt-elt-safe "(printf-lang fmt-elt)" f)]
    ))
    
  (debug (thunk (printf "done with interp-fmt-elt-safe: ~a~n" res)))
  res)


(define (interp-fmt-safe f args conf)
  (debug (thunk (printf "(interp-fmt-safe ~a ~a ~a)~n" f args conf)))
  (define res (match f
    [(printf-lang nil) (printf-lang (nil ,conf))]

    [(printf-lang (cons f1:fmt-elt f+:fmt))
     (match (interp-fmt-elt-safe f1 args conf)
       [(printf-lang ERR) (printf-lang ERR)]
       [(printf-lang (t1:trace conf+:config))
        (match (interp-fmt-safe f+ args conf+)
          [(printf-lang ERR) (printf-lang ERR)]
          [(printf-lang (t2:trace conf++:config))
           (printf-lang (,(bonsai-ll-append t1 t2) ,conf++))]
          )]
       )

     ]

    [_ (raise-argument-error 'interp-fmt-safe "(printf-lang fmt)" f)]
    ))
  (debug (thunk (printf "result of interp-fmt-safe: ~a~n" res)))
  res
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an concrete "unsafe" implementation of printf                          ;
;                                                                               ;
; If an argument in the format string is not in scope with respect to the       ;
; argument list, or if it maps to a value of the wrong type, it will return the ;
; empty string and proceed silently.                                            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (unsafe:val->integer v)
  (match v
    [(printf-lang n:bvint)       (bvint->number n)]
    ; if the value is a location, we interpret the location as an integer
    [(printf-lang (LOC l:ident)) (bonsai->number l)]
    ; for strings, `s` is a boxed string from string.rkt, aka a list of
    ; characters, aka a list of integers. Therefore, interpreting a string as an
    ; integer is just the integer value of the first character in the string.
    [(printf-lang s:string)      (first (bonsai-string-value s))]
    [_ (raise-argument-error 'unsafe:val->integer "(printf-lang val)" v)]
    ))

(define (unsafe:val->string v)
  (match v
    [(printf-lang s:string) (bonsai-string-value s)]
    ; for an integer or location, interpret the integer as a character. In
    ; actuality C would expect a null-terminated string in memory, so it would
    ; actually not stop at the single value, but we aren't modeling that for
    ; now.
    [(printf-lang n:bvint)      (char->string (bvint->number n))]
    [(printf-lang (LOC l:ident)) (char->string (bonsai->number l))]
    [_ (raise-argument-error 'unsafe:val->string "(printf-lang val)" v)]
    ))


(define (unsafe:fmt->constant ftype param args)
  (match (lookup-offset (param->offset param) args)
    [(printf-lang ERR) (printf-lang ERR)]
    [(printf-lang v:val)
     (match ftype
       ; if ftype = 'd', interpret the argument as an integer
       [(printf-lang d) (bonsai-integer (unsafe:val->integer v))]
       ; if ftype = 's', interpret the argument as a string
       [(printf-lang s) (bonsai-string (unsafe:val->string v))]
       ; if ftype = 'n', interpret the argument as a location aka an integer
       [(printf-lang n) (bonsai-integer (unsafe:val->integer v))]
       [_ (raise-argument-error 'unsafe:fmt->constant "(printf-lang fmt-type)" ftype)]
       )]
    ))

; INPUT: a format string, a stack (we assume that the arguments have been pushed
; onto the stack), and a configuration
;
; OUTPUT: an outputted trace and a configuration
(define (interp-fmt-elt-unsafe f args conf)
  (match f

    [(printf-lang s:string)
     (print-constant conf s)
     ]

    ; the width parameter doesn't make a difference for n formats
    [(printf-lang (% p:parameter width n))
     (match (unsafe:fmt->constant (printf-lang n) p args)
       [(printf-lang ERR)     (printf-lang (nil ,conf))]
       [(printf-lang l:ident) (printf-lang (nil ,(print-n-loc conf l)))]
       )]

    ; for d and n format types, we will first calculate the constant associated
    ; with the format type, and then pad it by the appropriate amount
    [(printf-lang (% p:parameter NONE ftype:fmt-type))
     (match (unsafe:fmt->constant (printf-lang n) p args)
       [(printf-lang ERR)        (printf-lang (nil ,conf))]
       [(printf-lang c:constant) (print-constant conf c)]
       )]

    [(printf-lang (% p:parameter w:natural ftype:fmt-type))
     (match (unsafe:fmt->constant ftype p args)
       [(printf-lang ERR)        (printf-lang (nil ,conf))]
       [(printf-lang c:constant)
        (print-trace conf (pad-constant c (bonsai->number w)))]
       )]

    [(printf-lang (% p:parameter (* o:offset) ftype:fmt-type))
     (match (lookup-offset (bonsai->number o) args)
       ; if o is greater than the length of the argument list, no-op
       [(printf-lang ERR)   (printf-lang (nil ,conf))]
       [(printf-lang v:val)
        (match (unsafe:fmt->constant ftype p args)
          [(printf-lang ERR) (printf-lang (nil ,conf))]
          [(printf-lang c:constant)
           (print-trace conf (pad-constant c (unsafe:val->integer v)))]
          )]
       )]

    [_ (raise-argument-error 'interp-fmt-elt-unsafe "(printf-lang fmt-elt)" f)]
    ))
(define (interp-fmt-unsafe f args conf)
  (match f
    [(printf-lang nil) (printf-lang (nil ,conf))]

    [(printf-lang (cons f1:fmt-elt f+:fmt))

     (let* ([b1 (interp-fmt-elt-unsafe f1 args conf)]
            [b2 (interp-fmt-unsafe f+ args (behavior->config b1))]
            [t+ (bonsai-ll-append (behavior->trace b1) (behavior->trace b2))]
            )
       (printf-lang (,t+ ,(behavior->config b2))))
     ]
    ))


#|||||||||||||||||||||||||||||||||||||#
#| Classifiers for printf-lang forms |#
#|||||||||||||||||||||||||||||||||||||#

(define (fmt? f)
  (match f
    #;[(printf-lang fmt) #t]
    [(printf-lang nil) #t]
    [(printf-lang (cons f0:fmt-elt f+:fmt)) #t]
    [_ #f]))

;(fmt? example-fmt)

(define (ident? x)
  (bonsai-integer? x)
  )
(define (val? v)
  (match v
    [(printf-lang val) #t]
    [_ #f]
    ))
(define (bvint? v)
  (match v
    [(printf-lang bvint) #t]
    [_ #f]))


(define (arglist? args)
  (match args
    [(printf-lang arglist) #t]
    [_ #f]
    ))

; p is the parameter offset as a bonsai number
; ftype is the format type associated with the parameter
(define (parameter-consistent-with-arglist p ftype args)
  (let* ([offset (param->offset p)]
         [arg (lookup-offset offset args)])
    (and (< offset (bonsai-ll-length args))
         (match (cons ftype arg)
           [(cons (printf-lang d) (printf-lang bvint))       #t]
           [(cons (printf-lang n) (printf-lang (LOC ident))) #t]
           [(cons (printf-lang s) (printf-lang string))      #t]
           [_                                                #f]
           ))))
(define (width-consistent-with-arglist w args)
  (match w
    [(printf-lang NONE) #t]
    [(printf-lang natural) #t]
    [(printf-lang (* o:offset))
     (and (< (bonsai->number o) (bonsai-ll-length args))
          (bvint? (lookup-offset (bonsai->number o) args)))]
    ))


(define (fmt-consistent-with-arglist? f args)
  (define (fmt-elt-consistent-with-arglist? f0)
    (match f0
      [(printf-lang string) #t]

      [(printf-lang (% p:parameter w:width ftype:fmt-type))
       (and (parameter-consistent-with-arglist p ftype args)
            (width-consistent-with-arglist w args))]
      ))
  (match f
    [(printf-lang nil) #t]
    [(printf-lang (cons f0:fmt-elt f+:fmt))
     (and (fmt-elt-consistent-with-arglist? f0)
          (fmt-consistent-with-arglist? f+ args))]
    ))


(define (mem? m)
  (match m
    [(printf-lang mnil) #t]
    [(printf-lang (mcons x:ident v:val m+:mem))
     (and (ident? x) (val? v) (mem? m+))]
    [_ #f]
    ))

(define (conf? conf)
  (match conf
    [(printf-lang (i:integer m:mem)) (mem? m)] 
    [_ #f]
    ))
