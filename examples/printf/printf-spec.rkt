#lang seec
#;(require racket/base)
(require racket/contract)
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error
                  make-parameter
                  ))
(require rosette/lib/value-browser)

(require (only-in racket/base
                  [make-string unsafe:make-string]
                  ))
(require (only-in seec/private/string
                  char->string))

(provide printf-lang
         printf-spec
         fmt-string

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
         interp-fmt

         pad-constant
         print-trace

         (rename-out [fmt-string-fmt? fmt?]
                     [fmt-string-fmt-type? fmt-type?]
                     [fmt-string-parameter? parameter?]
                     [fmt-string-fmt-elt? fmt-elt?]

                     [printf-lang-ident? ident?]
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
         fmt-string-width?

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

(define-grammar fmt-string
  (fmt ::= list<fmt-elt>)
  (fmt-elt ::= string (% (parameter (width fmt-type))))
  (parameter ::= (offset $))
  (width ::= NONE (* offset) natural)
  (offset ::= natural)
  (fmt-type ::= s d n)
  )

(define-grammar printf-lang
  #:extends fmt-string
  (arglist ::= list<expr>)
  (expr ::= (LOC ident) (* expr) integer string)
  (mem ::= mnil (mcons ident val mem))
  (val ::= (LOC ident) integer string ERR #;(DEREF val))
  (ident ::= integer)
  (trace ::= list<constant>)
  (constant ::= string integer (pad-by natural))
  ; a configuration consists of an accumulator and a memory value
  (config ::= (integer mem))
  (context ::= (arglist config))
  (behavior ::= (trace config))
  )

  #;(behavior ::= (string config))


(define debug? (make-parameter #f))
(define (debug stmt)
  (if (debug?)
      (stmt)
      (void)))

#||||||||||||||||||||||||||||#
#| Projections out of types |#
#||||||||||||||||||||||||||||#

(define/contract (loc? v)
  (-> any/c boolean?)
  (match v
    [(printf-lang (LOC l:ident)) #t]
    [_ #f]
    ))

(define/contract (err? x)
  (-> any/c boolean?)
  (match x
    [(printf-lang ERR) #t]
    [_ #f]))
(define (natural? n)
  (and (integer? n)
       (>= n 0)))

(define/contract (val->number v)
  (-> printf-lang-integer? integer?)
  (match v
    [(printf-lang n:integer) n]
    [_ (raise-argument-error 'val->number "(printf-lang integer)" v)]
    ))
(define/contract (val->loc v)
  (-> loc? printf-lang-ident?)
  (match v
    [(printf-lang (LOC x:ident)) x]
    ))
(define/contract (conf->mem c)
  (-> printf-lang-config? printf-lang-mem?)
  (match c
    [(printf-lang (integer m:mem)) m]
    ))
(define/contract (conf->acc c)
  (-> printf-lang-config? integer?)
  (match c
    [(printf-lang (acc:integer mem)) acc]
    [_ (raise-argument-error 'conf->acc "conf" c)]
    ))

(define/contract (param->offset param)
  (-> fmt-string-parameter? integer?)
  (match param
    [(printf-lang (o:offset $)) o]
    ))


(define/contract (behavior->trace b)
  (-> printf-lang-behavior? printf-lang-trace?)
  (match b
    [(printf-lang (t:trace config)) t]))
(define/contract (behavior->config b)
  (-> printf-lang-behavior? printf-lang-config?)
  (match b
    [(printf-lang (trace c:config)) c]
    ))

(define (make-context args conf)
  (printf-lang (,args ,conf)))
(define/contract (make-config n m)
  (-> integer? printf-lang-mem? printf-lang-config?)
  (printf-lang (,n ,m)))
(define (make-config-triv n)
  (make-config n (printf-lang mnil)))
(define/contract (make-behav t n m)
  (-> printf-lang-trace? integer? printf-lang-mem? printf-lang-behavior?)
  (printf-lang (,t ,(make-config n m))))
(define (make-behav-triv t n)
  (printf-lang (,t ,(make-config-triv n))))

(define/contract (context->config ctx)
  (-> printf-lang-context? printf-lang-config?)
  (match ctx
    [(printf-lang (args:arglist cfg:config)) cfg]
    ))
(define/contract (context->arglist ctx)
  (-> printf-lang-context? printf-lang-arglist?)
  (match ctx
    [(printf-lang (args:arglist cfg:config)) args]
    ))
; a printf-program is a racket pair of a context and a format string
(define (printf-program? p)
  (and (pair? p)
       (printf-lang-context? (car p))
       (fmt-string-fmt? (cdr p))
       ))
(define/contract (program->fmt p)
  (-> printf-program? fmt-string-fmt?)
  (cdr p))
(define/contract (program->context p)
  (-> printf-program? printf-lang-context?)
  (car p))
(define/contract (program->arglist p)
  (-> printf-program? printf-lang-arglist?)
  (context->arglist (car p)))
(define/contract (program->config p)
  (-> printf-program? printf-lang-config?)
  (context->config (car p)))
(define/contract (make-program f args conf)
  (-> fmt-string-fmt? printf-lang-arglist? printf-lang-config? printf-program?)
  (cons (printf-lang (,args ,conf)) f))



#|||||||||||||||||||||||||||||#
#| Operations on printf-lang |#
#|||||||||||||||||||||||||||||#

; INPUT: a location identifier l and a memory value m with l in the domain of m
; OUTPUT: the value mapped to by the identifier
(define/contract (lookup-loc l m)
  (-> printf-lang-ident? printf-lang-mem? (or/c err? printf-lang-val?))
  (debug (thunk (printf "(lookup-loc ~a ~a)~n" l m)))
  (match m
    [(printf-lang mnil) (printf-lang ERR)]
    [(printf-lang (mcons l0:ident v0:val m0:mem))
     (if (equal? l l0)
         v0
         (lookup-loc l m0))]
    ))

(define/contract (eval-expr e m)
  (-> printf-lang-expr? printf-lang-mem? (or/c err? printf-lang-val?))
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
(define/contract (lookup-offset offset ctx)
  (-> integer? printf-lang-context? (or/c err? printf-lang-val?))
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
(define/contract (config-add conf n)
  (-> printf-lang-config? integer? printf-lang-config?)
  (debug (thunk (printf "(config-add ~a ~a)~n" conf n)))
  (let* ([acc   (conf->acc conf)]
         [m     (conf->mem conf)]
         [acc+n (+ acc n)]
         )
    (begin
      (printf-lang (,acc+n ,m))
      )
    ))


; INPUT: a mem, a location, and a value
; OUTPUT: an updated memory with the location mapping to the new value
(define/contract (mem-update m l v)
  (-> printf-lang-mem? printf-lang-ident? printf-lang-val? printf-lang-mem?)
  (printf-lang (mcons ,l ,v ,m)))



  #;(render-value/window n)
  #;(if (or (union? n) (term? n))
      (abstract-defn n)
      (concrete-defn n)
      )

  
; If the constant is a string, give the length of the string
; If the constant is an integer (represented by a bitvector) give the length of
; the string representing the number.
(define/contract (constant-length c)
  (-> printf-lang-constant? integer?)
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
(define/contract (print-constant conf-or-behav c)
  (-> (or/c printf-lang-config? printf-lang-behavior?) printf-lang-constant? printf-lang-behavior?)
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
    [_ (raise-argument-error 'print-constant "(or/c printf-lang-config? printf-lang-behavior?)" conf-or-behav)]
    )
  )
  (debug (thunk (printf "computed print-constant: ~a~n" res)))
  res
  )


; Input: t is either a trace or ERR
(define/contract (print-trace conf t)
  (-> printf-lang-config? (or/c err? printf-lang-trace?) (or/c err? printf-lang-behavior?))
  (debug (thunk (printf "(print-trace ~a ~a)~n" conf t)))
  (define res (match t
    [(printf-lang ERR) (printf-lang ERR)]
    [(printf-lang nil) (printf-lang (nil ,conf))]
    [(printf-lang (cons c:constant t+:trace))
     (print-constant (print-trace conf t+) c)]
    [_ (raise-argument-error 'print-trace "printf-lang-trace?" t)]
    ))
  (debug (thunk (printf "result of print-trace: ~a~n" res)))
  res)


; INPUT: a config conf and a location identifier l
; OUTPUT: an updated configuration that assigns l the value of the accumulator.
(define/contract (print-n-loc conf l)
  (-> printf-lang-config? printf-lang-ident? printf-lang-config?)
  (debug (thunk (printf "(print-n-loc ~a)~n" l)))
  (let* ([acc (printf-lang ,(conf->acc conf))]
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


; returns the contant to be printed, or ERR
; expects ftype to not be equal to `n`
(define/contract (fmt->constant ftype param ctx)
  (-> fmt-string-fmt-type? fmt-string-parameter? printf-lang-context? (or/c err? printf-lang-constant?))
  (debug (thunk (printf "(fmt->constant ~a ~a ~a)~n" ftype param ctx)))
  (define res
      (match (cons ftype (lookup-offset (param->offset param) ctx))
        [(cons (printf-lang d) (printf-lang n:integer))
         (printf-lang ,n)]
        [(cons (printf-lang s) (printf-lang s:string))
         (printf-lang ,s)]
        [_ (printf-lang ERR)]
        ))
  (debug (thunk (printf "result of fmt->constant: ~a~n" res)))
  res)

; INPUT: a constant `c` and a natural number `w`
; OUTPUT: the trace of length max(w,len(c)) obtained by padding `c` with up to `w` spaces.
;
; TODO: do we need to use bitvectors to keep track of potential overflow? Right
; now both the constant lengths and widths are integers, rather than bitvectors.
(define/contract (pad-constant c w)
  (-> printf-lang-constant? integer? printf-lang-trace?)
  (debug (thunk (printf "(pad-constant ~a ~a)~n" c w)))
  (define res (let* ([c-len (constant-length c)]
         )
    (cond
      [(<= w c-len) (seec-singleton c)]
      [else         (seec-cons (printf-lang (pad-by ,(- w c-len))) (seec-singleton c))]
      )))
  (debug (thunk (printf "result of pad-constant: ~a~n" res)))
  res)


; INPUT: a format string, an argument list, and a configuration
; OUTPUT: an outputted string and a configuration OR ERR
(define/contract (interp-fmt-elt-safe f ctx)
  (-> fmt-string-fmt-elt? printf-lang-context? (or/c err? printf-lang-behavior?))
  (debug (thunk (printf "(interp-fmt-elt-safe ~a ~a)~n" f ctx)))
  (define conf (context->config ctx))
  (define res (match f
    [(printf-lang s:string)
     (print-constant conf (printf-lang ,s))]

    ; the width parameter doesn't make a difference for n formats
    [(printf-lang (% (p:parameter (width n))))
     (match (lookup-offset (param->offset p) ctx)
       [(printf-lang (LOC l:ident))
        (printf-lang (nil ,(print-n-loc conf l)))
        ]
       [_ (printf-lang ERR)]
       )]

    ; otherwise, for the 's' and 'd' format types:
    [(printf-lang (% (p:parameter (NONE ftype:fmt-type))))
     (match (fmt->constant ftype p ctx)
       [(printf-lang c:constant)
        (print-constant conf (fmt->constant ftype p ctx))]
       [(printf-lang ERR)
        (printf-lang ERR)]
       )]

    [(printf-lang (% (p:parameter (w:natural ftype:fmt-type))))
     (match (fmt->constant ftype p ctx)
       [(printf-lang c:constant)
        (print-trace conf (pad-constant c w))]
       [(printf-lang ERR) (printf-lang ERR)]
       )]

    [(printf-lang (% (p:parameter ((* o:offset) ftype:fmt-type))))
     (match (list (lookup-offset o ctx)
                  (fmt->constant ftype p ctx))
       [(list (printf-lang w:integer)
              (printf-lang c:constant))
        (print-trace conf (pad-constant c w))]
       [_ (printf-lang ERR)]
       )]

    [_ (raise-argument-error 'interp-fmt-elt-safe "(printf-lang fmt-elt)" f)]
    ))
    
  (debug (thunk (printf "done with interp-fmt-elt-safe: ~a~n" res)))
  res)


(define/contract (interp-fmt f args conf)
  (-> fmt-string-fmt? printf-lang-arglist? printf-lang-config? (or/c err? printf-lang-behavior?))
  (debug (thunk (printf "(safe:interp-fmt ~a ~a ~a)~n" f args conf)))
  (define res (match f
    [(printf-lang nil) (printf-lang (nil ,conf))]

    [(printf-lang (cons f1:fmt-elt f+:fmt))
     (match (interp-fmt-elt-safe f1 (make-context args conf))
       [(printf-lang ERR) (printf-lang ERR)]
       [(printf-lang (t1:trace conf+:config))
        (match (interp-fmt f+ args conf+)
          [(printf-lang ERR) (printf-lang ERR)]
          [(printf-lang (t2:trace conf++:config))
           (printf-lang (,(seec-append t1 t2) ,conf++))]
          )]
       )

     ]
    ))
  (debug (thunk (printf "result of safe:interp-fmt: ~a~n" res)))
  res
  )


#|||||||||||||||||||||||||||||||||||||#
#| Classifiers for printf-lang forms |#
#|||||||||||||||||||||||||||||||||||||#


; p is the parameter offset
; ftype is the format type associated with the parameter
(define/contract (parameter-consistent-with-arglist p ftype ctx)
  (-> fmt-string-parameter? fmt-string-fmt-type? printf-lang-context? boolean?)
  (let* ([offset (param->offset p)]
         [arg (lookup-offset offset ctx)])
    (and (< offset (seec-length (context->arglist ctx)))
         (match (cons ftype arg)
           [(cons (printf-lang d) (printf-lang integer))       #t]
           [(cons (printf-lang n) (printf-lang (LOC ident))) #t]
           [(cons (printf-lang s) (printf-lang string))      #t]
           [_                                                #f]
           ))))
(define (width-consistent-with-arglist w ctx)
  (-> fmt-string-width? printf-lang-context? boolean?)
  (match w
    [(printf-lang NONE) #t]
    [(printf-lang natural) #t]
    [(printf-lang (* o:offset))
     (and (< o (seec-length (context->arglist ctx)))
          (printf-lang-integer? (lookup-offset o ctx)))]
    ))


(define (fmt-consistent-with-arglist? f ctx)
  (define (fmt-elt-consistent-with-arglist? f0)
    (match f0
      [(printf-lang string) #t]

      [(printf-lang (% (p:parameter (w:width ftype:fmt-type))))
       (and (parameter-consistent-with-arglist p ftype ctx)
            (width-consistent-with-arglist w ctx))]
      ))
  (match f
    [(printf-lang nil) #t]
    [(printf-lang (cons f0:fmt-elt f+:fmt))
     (and (fmt-elt-consistent-with-arglist? f0)
          (fmt-consistent-with-arglist? f+ ctx))]
    ))

(define-language printf-spec
  #:grammar printf-lang
  #:expression fmt #:size 3
  #:context context #:size 5
  #:link cons
  #:evaluate (λ (p) (interp-fmt (program->fmt p)
                                (program->arglist p)
                                (program->config p)))
  )
