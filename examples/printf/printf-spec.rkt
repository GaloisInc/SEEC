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
(require (only-in seec/private/bonsai2
                  bonsai-pretty))
(require (only-in seec/private/string
                  char->string))

(provide printf-lang
         printf-spec

         bonsai->number
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

         fmt?
         ident?
         val?
         expr?
         arglist?
         mem?
         trace?
         const?
         behavior?
         config?
         context?
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
  (fmt ::= list<fmt-elt>)
  (fmt-elt ::= string (% parameter width fmt-type))
  (parameter ::= (offset $))
  (width ::= NONE (* offset) natural)
  (offset ::= natural)
  (fmt-type ::= s d n)

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


#;(define/contract (ll-singleton x)
  (-> bonsai? bonsai-linked-list?)
  (printf-lang (cons ,x nil)))
#;(define/contract (ll-cons x xs)
  (-> bonsai? bonsai-linked-list? bonsai-linked-list?)
  (printf-lang (cons ,x ,xs)))

(define debug? (make-parameter #f))
(define (debug stmt)
  (if (debug?)
      (stmt)
      (void)))

#||||||||||||||||||||||||||||#
#| Projections out of types |#
#||||||||||||||||||||||||||||#

(define/contract (mem? m)
  (-> any/c boolean?)
  (match m
    [(printf-lang mnil) #t]
    [(printf-lang (mcons x:ident v:val m+:mem))
     (and (ident? x) (val? v) (mem? m+))]
    [_ #f]
    ))
(define/contract (expr? e)
  (-> any/c boolean?)
  (match e
    [(printf-lang expr) #t]
    ))
(define/contract (width? w)
  (-> any/c boolean?)
  (match w
    [(printf-lang width) #t]
    [_ #f]
    ))

(define/contract (trace? t)
  (-> any/c boolean?)
  (match t
    [(printf-lang trace) #t]
    [_ #f]
    ))

(define/contract (fmt? f)
  (-> any/c boolean?)
  (match f
    [(printf-lang fmt) #t]
    [_ #f]))
(define/contract (fmt-type? f)
  (-> any/c boolean?)
  (match f
    [(printf-lang fmt-type) #t]
    [_ #f]))
(define/contract (fmt-elt? f)
  (-> any/c boolean?)
  (match f
    [(printf-lang fmt-elt) #t]
    [_ #f]))


(define/contract (parameter? p)
  (-> any/c boolean?)
  (match p
    [(printf-lang parameter) #t]
    [_ #f]))

(define (ident? x)
  (bonsai-integer? x)
  )
(define/contract (val? v)
  (-> any/c boolean?)
  (match v
    [(printf-lang val) #t]
    [_ #f]
    ))
(define/contract (loc? v)
  (-> any/c boolean?)
  (match v
    [(printf-lang (LOC l:ident)) #t]
    [_ #f]
    ))

(define/contract (arglist? args)
  (-> any/c boolean?)
  (match args
    [(printf-lang arglist) #t]
    [_ #f]
    ))
(define/contract (behavior? b)
  (-> any/c boolean?)
  (match b
    [(printf-lang behavior) #t]
    [_ #f]
    ))
(define/contract (config? cfg)
  (-> any/c boolean?)
  (match cfg
    [(printf-lang config) #t]
    [_ #f]
    ))
(define/contract (err? x)
  (-> any/c boolean?)
  (match x
    [(printf-lang ERR) #t]
    [_ #f]))
(define/contract (const? x)
  (-> any/c boolean?)
  (match x
    [(printf-lang constant) #t]
    [_ #f]))
(define (natural? n)
  (and (integer? n)
       (>= n 0)))


(define/contract (bonsai->number n)
  (-> bonsai-integer? integer?)
  (bonsai-integer-value n))

(define/contract (val->number v)
  (-> bonsai-integer? integer?)
  (match v
    [(printf-lang n:integer) (bonsai->number n)]
    [_ (raise-argument-error 'val->number "(printf-lang integer)" v)]
    ))
(define/contract (val->loc v)
  (-> loc? bonsai-integer?)
  (match v
    [(printf-lang (LOC x:ident)) x]
    ))
(define/contract (conf->mem c)
  (-> config? mem?)
  (match c
    [(printf-lang (integer m:mem)) m]
    ))
(define/contract (conf->acc c)
  (-> config? integer?)
  (match c
    [(printf-lang (acc:integer mem)) (bonsai->number acc)]
    [_ (raise-argument-error 'conf->acc "conf" c)]
    ))

(define/contract (param->offset param)
  (-> parameter? integer?)
  (match param
    [(printf-lang (o:offset $)) (bonsai->number o)]
    ))


(define/contract (behavior->trace b)
  (-> behavior? trace?)
  (match b
    [(printf-lang (t:trace config)) t]))
(define/contract (behavior->config b)
  (-> behavior? config?)
  (match b
    [(printf-lang (trace c:config)) c]
    ))

(define (context? ctx)
  (match ctx
    [(printf-lang context) #t]
    [_ #f]
    ))
(define (make-context args conf)
  (printf-lang (,args ,conf)))
(define/contract (make-config n m)
  (-> integer? mem? config?)
  (printf-lang (,(bonsai-integer n) ,m)))
(define (make-config-triv n)
  (make-config n (printf-lang mnil)))
(define/contract (make-behav t n m)
  (-> trace? integer? mem? behavior?)
  (printf-lang (,t ,(make-config n m))))
(define (make-behav-triv t n)
  (printf-lang (,t ,(make-config-triv n))))

(define/contract (context->config ctx)
  (-> context? config?)
  (match ctx
    [(printf-lang (args:arglist cfg:config)) cfg]
    ))
(define/contract (context->arglist ctx)
  (-> context? arglist?)
  (match ctx
    [(printf-lang (args:arglist cfg:config)) args]
    ))
; a printf-program is a racket pair of a context and a format string
(define (printf-program? p)
  (and (pair? p)
       (context? (car p))
       (fmt? (cdr p))
       ))
(define/contract (program->fmt p)
  (-> printf-program? fmt?)
  (cdr p))
(define/contract (program->context p)
  (-> printf-program? context?)
  (car p))
(define/contract (program->arglist p)
  (-> printf-program? arglist?)
  (context->arglist (car p)))
(define/contract (program->config p)
  (-> printf-program? config?)
  (context->config (car p)))
(define/contract (make-program f args conf)
  (-> fmt? arglist? config? printf-program?)
  (cons (printf-lang (,args ,conf)) f))



(define/contract (bonsai-string-append s1 s2)
  (-> bonsai-string? bonsai-string? bonsai-string?)
  (bonsai-string (string-append (bonsai-string-value s1) (bonsai-string-value s2))))


#|||||||||||||||||||||||||||||#
#| Operations on printf-lang |#
#|||||||||||||||||||||||||||||#

; INPUT: a location identifier l and a memory value m with l in the domain of m
; OUTPUT: the value mapped to by the identifier
(define/contract (lookup-loc l m)
  (-> ident? mem? (or/c err? val?))
  (debug (thunk (printf "(lookup-loc ~a ~a)~n" l m)))
  (match m
    [(printf-lang mnil) (printf-lang ERR)]
    [(printf-lang (mcons l0:ident v0:val m0:mem))
     (if (equal? l l0)
         v0
         (lookup-loc l m0))]
    ))

(define/contract (eval-expr e m)
  (-> expr? mem? (or/c err? val?))
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
  (-> integer? context? (or/c err? val?))
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
  (-> config? integer? config?)
  (debug (thunk (printf "(config-add ~a ~a)~n" conf n)))
  (let* ([acc   (conf->acc conf)]
         [m     (conf->mem conf)]
         [acc+n (bonsai-integer (+ acc n))]
         )
    (begin
      (printf-lang (,acc+n ,m))
      )
    ))


; INPUT: a mem, a location, and a value
; OUTPUT: an updated memory with the location mapping to the new value
(define/contract (mem-update m l v)
  (-> mem? ident? val? mem?)
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
  (-> const? integer?)
  (debug (thunk (printf "(constant-length ~a)~n" c)))
  (define res (match c
    [(printf-lang s:string)   (string-length (bonsai-string-value s))]
    [(printf-lang n:integer)  (string-length (number->string (bonsai->number n)))]
    [(printf-lang (pad-by n:natural)) (bonsai->number n)]
    ))
  (debug (thunk (printf "Computed constant-length: ~a~n" res)))
  res)


; INPUT: a config OR behavior conf-or-behav and constant c
; OUTPUT: a behavior consisting of the trace containing n and the upated configuration
(define/contract (print-constant conf-or-behav c)
  (-> (or/c config? behavior?) const? behavior?)
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


; Input: t is either a trace or ERR
(define/contract (print-trace conf t)
  (-> config? (or/c err? trace?) (or/c err? behavior?))
  (debug (thunk (printf "(print-trace ~a ~a)~n" conf t)))
  (define res (match t
    [(printf-lang ERR) (printf-lang ERR)]
    [(printf-lang nil) (printf-lang (nil ,conf))]
    [(printf-lang (cons c:constant t+:trace))
     (print-constant (print-trace conf t+) c)]
    [_ (raise-argument-error 'print-trace "trace?" t)]
    ))
  (debug (thunk (printf "result of print-trace: ~a~n" res)))
  res)


; INPUT: a config conf and a location identifier l
; OUTPUT: an updated configuration that assigns l the value of the accumulator.
(define/contract (print-n-loc conf l)
  (-> config? ident? config?)
  (debug (thunk (printf "(print-n-loc ~a)~n" l)))
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


; returns the contant to be printed, or ERR
; expects ftype to not be equal to `n`
(define/contract (fmt->constant ftype param ctx)
  (-> fmt-type? parameter? context? (or/c err? const?))
  (debug (thunk (printf "(fmt->constant ~a ~a ~a)~n" ftype param ctx)))
  (define res
      (match (cons ftype (lookup-offset (param->offset param) ctx))
        [(cons (printf-lang d) (printf-lang n:integer))
         n]
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
(define/contract (pad-constant c w)
  (-> const? integer? trace?)
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
(define/contract (interp-fmt-elt-safe f ctx)
  (-> fmt-elt? context? (or/c err? behavior?))
  (debug (thunk (printf "(interp-fmt-elt-safe ~a ~a)~n" f ctx)))
  (define conf (context->config ctx))
  (define res (match f
    [(printf-lang s:string)
     (print-constant conf s)]

    ; the width parameter doesn't make a difference for n formats
    [(printf-lang (% p:parameter width n))
     (match (lookup-offset (param->offset p) ctx)
       [(printf-lang (LOC l:ident))
        (printf-lang (nil ,(print-n-loc conf l)))
        ]
       [_ (printf-lang ERR)]
       )]

    ; otherwise, for the 's' and 'd' format types:
    [(printf-lang (% p:parameter NONE ftype:fmt-type))
     (match (fmt->constant ftype p ctx)
       [(printf-lang c:constant)
        (print-constant conf (fmt->constant ftype p ctx))]
       [(printf-lang ERR)
        (printf-lang ERR)]
       )]

    [(printf-lang (% p:parameter w:natural ftype:fmt-type))
     (match (fmt->constant ftype p ctx)
       [(printf-lang c:constant)
        (print-trace conf (pad-constant c (bonsai->number w)))]
       [(printf-lang ERR) (printf-lang ERR)]
       )]

    [(printf-lang (% p:parameter (* o:offset) ftype:fmt-type))
     (match (list (lookup-offset (bonsai->number o) ctx)
                  (fmt->constant ftype p ctx))
       [(list (printf-lang w:integer)
              (printf-lang c:constant))
        (print-trace conf (pad-constant c (bonsai->number w)))]
       [_ (printf-lang ERR)]
       )]

    [_ (raise-argument-error 'interp-fmt-elt-safe "(printf-lang fmt-elt)" f)]
    ))
    
  (debug (thunk (printf "done with interp-fmt-elt-safe: ~a~n" res)))
  res)


(define/contract (interp-fmt f args conf)
  (-> fmt? arglist? config? (or/c err? behavior?))
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
           (printf-lang (,(bonsai-ll-append t1 t2) ,conf++))]
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


; p is the parameter offset as a bonsai number
; ftype is the format type associated with the parameter
(define/contract (parameter-consistent-with-arglist p ftype ctx)
  (-> parameter? fmt-type? context? boolean?)
  (let* ([offset (param->offset p)]
         [arg (lookup-offset offset ctx)])
    (and (< offset (bonsai-ll-length (context->arglist ctx)))
         (match (cons ftype arg)
           [(cons (printf-lang d) (printf-lang integer))       #t]
           [(cons (printf-lang n) (printf-lang (LOC ident))) #t]
           [(cons (printf-lang s) (printf-lang string))      #t]
           [_                                                #f]
           ))))
(define (width-consistent-with-arglist w ctx)
  (-> width? context? boolean?)
  (match w
    [(printf-lang NONE) #t]
    [(printf-lang natural) #t]
    [(printf-lang (* o:offset))
     (and (< (bonsai->number o) (bonsai-ll-length (context->arglist ctx)))
          (bonsai-integer? (lookup-offset (bonsai->number o) ctx)))]
    ))


(define (fmt-consistent-with-arglist? f ctx)
  (define (fmt-elt-consistent-with-arglist? f0)
    (match f0
      [(printf-lang string) #t]

      [(printf-lang (% p:parameter w:width ftype:fmt-type))
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
