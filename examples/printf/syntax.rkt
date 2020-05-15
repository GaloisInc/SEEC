#lang seec
#;(require racket/base)
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(require (only-in racket/base
                  [make-string unsafe:make-string]
                  ))
(require (only-in seec/private/bonsai2
                  bonsai-pretty))

(provide printf-lang
         bonsai->number
         val->number
         val->loc
         conf->acc
         conf->mem
         lookup-offset
         vlist-length
         lookup-loc
         config-add
         mem-update
         interp-fmt-safe
         interp-fmt-unsafe
         fmt?
         ident?
         val?
         const?
         loc?
         vlist?
         mem?
         conf?
         fmt-consistent-with-vlist?
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

(define-language printf-lang
  (fmt ::= list<fmt-elt>)
  (fmt-elt ::= string
               (% parameter width fmt-type))
  (parameter ::= (offset $))
  (width ::= NONE (* offset) natural)
  (offset ::= natural)
  (fmt-type ::= #;s d n)

  (vlist ::= list<val>)
  (mem ::= mnil (mcons ident val mem))
  (val ::= (LOC ident) integer ERR #;(DEREF val)) 
  (ident ::= integer)
  ; a configuration consists of an accumulator and a memory value
  (config ::= (integer mem))
  )

#||||||||||||||||||||||||||||#
#| Projections out of types |#
#||||||||||||||||||||||||||||#


(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    [_ (raise-argument-error 'bonsai->number "bonsai-integer?" n)]
    ))
(define (val->number v)
  (match v
    [(printf-lang n:integer) (bonsai->number n)]
    [_ (raise-argument-error 'val->number "(printf-lang integer)" v)]
    ))
(define (val->loc v)
  (match v
    [(printf-lang (LOC x:ident)) x]
    [_ (raise-argument-error 'val->loc "(printf-lang (LOC ident))" v)]
    ))
(define (conf->mem c)
  (match c
    [(printf-lang (integer m:mem)) m]
    [_ (raise-argument-error 'conf->mem "conf" c)]
    ))
(define (conf->acc c)
  (match c
    [(printf-lang (acc:integer mem)) (bonsai->number acc)]
    [_ (raise-argument-error 'conf->acc "conf" c)]
    ))


#|||||||||||||||||||||||||||||#
#| Operations on printf-lang |#
#|||||||||||||||||||||||||||||#

; INPUT: an integer offset and an argument list args such that offset < length(args)
; OUTPUT: the value mapped to the offset
(define (lookup-offset offset args)
  (match args
    [(printf-lang nil) (printf-lang ERR)]
    [(printf-lang (cons v:val args+:vlist))
     (if (<= offset 0)
         v
         (lookup-offset (- offset 1) args+))]
    )
  )

(define (vlist-length args)
  (match args
    [(printf-lang nil) 0]
    [(printf-lang (cons val args+:vlist))
     (+ 1 (vlist-length args+))]
    [_ (raise-argument-error 'vlist-length "vlist?" args)]
    ))

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
  (let* ([acc   (conf->acc conf)]
         [m     (conf->mem conf)]
         [acc+n (bonsai-integer (+ n acc))])
    (printf-lang (,acc+n ,m))
    ))

; INPUT: a mem, a location, and a value
; OUTPUT: an updated memory with the location mapping to the new value
(define (mem-update m l v)
  (printf-lang (mcons ,l ,v ,m)))

; INPUT: a config conf and an integer n
; OUTPUT: a pair of the string representing n and an updated configuration
(define (print-d-integer conf n)
  (let* ([s (number->string n)]
         [new-conf (config-add conf (string-length s))])
    (list s new-conf)))

; INPUT: a config conf and a location identifier l
; OUTPUT: an updated configuration that assigns l the value of the accumulator.
(define (print-n-loc conf l)
  (let* ([acc (bonsai-integer (conf->acc conf))]
         [acc-val (printf-lang ,acc)]
         [new-mem (mem-update (conf->mem conf) l acc-val)]
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

#;(define (interp-d-safe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang n:integer) (print-d-integer conf (bonsai->number n))]
       [_ ; if the offset does not map to a number, throw an error
        (raise-arguments-error 'interp-d-safe
                               "Offset does not map to a number in the vlist"
                               "offset" (bonsai->number offset)
                               "vlist" args)]
       ))
#;(define (interp-n-safe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (LOC l:ident)) (list (string "") (print-n-loc conf l))]
       [_ ; if the offset does not map to a location, throw an error
        (raise-arguments-error 'interp-n-safe
                               "Offset does not map to a location in the vlist"
                               "offset" (bonsai->number offset)
                               "vlist" args)]
       ))

(define (param->offset param)
  (match param
    [(printf-lang (o:offset $)) (bonsai->number o)]
    ))

; 
(define (interp-ftype-safe ftype param args conf)
  (match (cons ftype (lookup-offset (param->offset param) args))
    ; if the type = 'd', the corresponding argument should be an integer
    ; The function `print-d-integer` is shared between safe and unsafe versions
    [(cons (printf-lang d) (printf-lang n:integer))
     (print-d-integer conf (bonsai->number n))
     ]
    ; if the type = 'n', the correesponding argument should be a location
    ; The function `print-n-loc` is shared between safe and unsafe versions
    [(cons (printf-lang n) (printf-lang (LOC l:ident)))
     (list (string "") (print-n-loc conf l))]
    [_ (raise-arguments-error 'interp-ftype-safe
                              "Offset does not map to a value of the correct type"
                              "fmt-type" (display ftype)
                              "parameter" param
                              "vlist" args
                              )]
    ))

; ensure str-conf-pair has width at least w, and if not, pad the beginning of
; the string by the appropriate number of spaces on the left.
(define (pad-by-width w str-conf-pair)
  (match str-conf-pair
    [(list s conf)
     (cond
       ([<= w (string-length s)] str-conf-pair)
       (else (let* ([remainder (- w (string-length s))]
                    [s+ (string (unsafe:make-string remainder #\space))]
                    [conf+ (config-add conf remainder)])
               (list (string-append s+ s) conf+))))]))
        
    

; INPUT: a format string, an argument list, and a configuration
; OUTPUT: an outputted string and a configuration
(define (interp-fmt-elt-safe f args conf)
  #;(printf "(interp-fmt-elt-safe ~a ~a ~a)~n" (bonsai-pretty f) args conf)
  (match f
    [(printf-lang s:string)
     (let ([s+ (bonsai-string-value s)])
       (begin
         #;(printf "string length of ~a: ~a ~n" (print-string s+) (string-length s+))
         (list s+ (config-add conf (string-length s+)))))]

    [(printf-lang (% p:parameter NONE ftype:fmt-type))
     (interp-ftype-safe ftype p args conf)]
    [(printf-lang (% p:parameter w:natural ftype:fmt-type))
     (pad-by-width (bonsai->number w) (interp-ftype-safe ftype p args conf))]
    [(printf-lang (% p:parameter (* o:offset) ftype:fmt-type))
     (match (lookup-offset (bonsai->number o) args)
       [(printf-lang w:integer)
        (pad-by-width (bonsai->number w) (interp-ftype-safe ftype p args conf))]
       [_ (raise-arguments-error 'interp-fmt-elt-safe
                                 "Offset does not map to a number in the arglist"
                                 "offset" (bonsai->number o)
                                 "vlist" args)]
       )]

    [_ (raise-argument-error 'interp-fmt-elt-safe "(printf-lang fmt-elt)" f)]
    ))
(define (interp-fmt-safe f args conf)
  #;(printf "(interp-fmt-safe ~a ~a ~a)~n" (bonsai-pretty f) args conf)
  (match f
    [(printf-lang nil)
     (list (string "") conf)]
    #;[(printf-lang (cons f:fmt-elt f+:fmt))
     (match-let* ([(list s-1 conf-1) (interp-fmt-elt-safe fmt-elt args conf)]
                  [(list s-2 conf-2) (interp-fmt-safe f+ args conf-1)])
       (cons (string-append s-1 s-2) conf-2))]
    [(printf-lang (cons f1:fmt-elt f+:fmt))
     (match (interp-fmt-elt-safe f1 args conf)
       [(list s-1 conf-1)
        (match (interp-fmt-safe f+ args conf-1)
          [(list s-2 conf-2)
           (list (string-append s-1 s-2) conf-2)])])]

    [_ (raise-argument-error 'interp-fmt-safe "(printf-lang fmt)" f)]
    ))

#;(displayln "Running test case demonstrating match-let failure...")
#;(interp-fmt-safe (printf-lang (++ f-empty f-empty))
                 (printf-lang nil)
                 (printf-lang (0 mnil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an concrete "unsafe" implementation of printf                          ;
;                                                                               ;
; If an argument in the format string is not in scope with respect to the       ;
; argument list, or if it maps to a value of the wrong type, it will return the ;
; empty string and proceed silently.                                            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


#;(define (interp-d-unsafe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang n:integer) (print-d-integer conf (bonsai->number n))]
       [_ ; if the offset does not map to a number, do nothing
        (list (string "") conf)]
       ))
#;(define (interp-n-unsafe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (LOC l:ident)) (list (string "") (print-n-loc conf l))]
       [_ ; if the offset does not map to a location, do nothing
        (list (string "") conf)]
       ))


(define (interp-ftype-unsafe ftype param args conf)
  (match (cons ftype (lookup-offset (param->offset param) args))
    ; if ftype = 'd' and the argument is an integer, call `print-d-integer`
    [(cons (printf-lang d) (printf-lang n:integer))
     (print-d-integer conf (bonsai->number n))
     ]
    ; if ftype = 'd' and the argument is a location, we interpret the location
    ; as an integer value and call `print-d-integer`
    [(cons (printf-lang d) (printf-lang (LOC l:ident)))
     (print-d-integer conf (bonsai->number l))

     ; if ftype = 'n' and the argument is a location, call `print-n-loc`
    [(cons (printf-lang n) (printf-lang (LOC l:ident)))
     (list (string "") (print-n-loc conf l))]

    ; if ftype = 'n' and the argument is an integer, we interpret the integer
    ; value as a location and call `print-n-loc`
    [(cons (printf-lang n) (printf-lang n:integer))
     (list (string "") (print-n-loc conf n))

    ; otherwise, do not throw an error, but execute a no-op.
    [_ (list (string "") conf)]
    ))


; INPUT: a format string, a stack (we assume that the arguments have been pushed
; onto the stack, and a configuration
; OUTPUT: an outputted string and a configuration
(define (interp-fmt-elt-unsafe f args conf)
  (match f

    [(printf-lang s:string)
     (let ([s+ (bonsai-string-value s)])
       (begin
         #;(printf "string length of ~a: ~a ~n" (print-string s+) (string-length s+))
         (list s+ (config-add conf (string-length s+)))))]

    [(printf-lang (% p:parameter NONE ftype:fmt-type))
     (interp-ftype-unsafe ftype p args conf)]
    [(printf-lang (% p:parameter w:natural ftype:fmt-type))
     (pad-by-width (bonsai->number w) (interp-ftype-unsafe ftype p args conf))]
    [(printf-lang (% p:parameter (* o:offset) ftype:fmt-type))
     (match (lookup-offset (bonsai->number o) args)
       [(printf-lang w:integer)
        (pad-by-width (bonsai->number w) (interp-ftype-unsafe ftype p args conf))]
       [_ (list (string "") conf)] ; do nothing
       )]

    [_ (raise-argument-error 'interp-fmt-elt-unsafe "(printf-lang fmt-elt)" f)]
    ))
(define (interp-fmt-unsafe f args conf)
  (match f
    [(printf-lang nil)
     (list (string "") conf)]

    [(printf-lang (cons f1:fmt-elt f+:fmt))
     (match (interp-fmt-elt-unsafe f1 args conf)
       [(list s-1 conf-1)
        (match (interp-fmt-unsafe f+ args conf-1)
          [(list s-2 conf-2)
           (list (string-append s-1 s-2) conf-2)])])]
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
  #;(match x
    [(printf-lang a) #t]
    [(printf-lang b) #t]
    [(printf-lang c) #t]
    [(printf-lang d) #t]
    [(printf-lang e) #t]
    [_ #f]
    ))
(define (val? v)
  (match v
    [(printf-lang val) #t]
    #;[(printf-lang (LOC ident)) #t]
    #;[(printf-lang integer) #t]
    #;[(printf-lang ERR) #t]
    [_ #f]
    ))
(define (const? v)
  (match v
    [(printf-lang integer) #t]
    [_ #f]
    ))
(define (loc? v)
  (match v
    [(printf-lang (LOC integer)) #t]
    [_ #f]
    ))


(define (vlist? args)
  (match args
    [(printf-lang vlist) #t]
    #;[(printf-lang nil) #t]
    #;[(printf-lang (cons v:val args+:vlist)) (and (val? v) (vlist? args+))]
    [_ #f]
    ))

; p is the parameter offset as a bonsai number
; ftype is the format type associated with the parameter
(define (parameter-consistent-with-vlist p ftype args)
  (let* ([offset (param->offset p)]
         [arg (lookup-offset offset args)])
    (and (< offset (bonsai-ll-length args))
         (match ftype
           [(printf-lang d) (const? arg)]
           [(printf-lang n) (loc? arg)]
           ))))
(define (width-consistent-with-vlist w args)
  (match w
    [(printf-lang NONE) #t]
    [(printf-lang natural) #t]
    [(printf-lang (* o:offset))
     (and (< (bonsai->number o) (bonsai-ll-length args))
          (const? (lookup-offset o args)))]
    ))


(define (fmt-consistent-with-vlist? f args)
  (define (fmt-elt-consistent-with-vlist? f0)
    (match f0
      [(printf-lang string) #t]

      [(printf-lang (% p:parameter w:width ftype:fmt-type))
       (and (parameter-consistent-with-vlist p ftype args)
            (width-consistent-with-vlist w args))]
      ))
  (match f
    [(printf-lang nil) #t]
    [(printf-lang (cons f0:fmt-elt f+:fmt))
     (and (fmt-elt-consistent-with-vlist? f0)
          (fmt-consistent-with-vlist? f+ args))]
    ))

#|
    [(printf-lang (%d offset:natural))
     (const? (lookup-offset (bonsai->number offset) args))]
    [(printf-lang (%n offset:natural))
     (loc? (lookup-offset (bonsai->number offset) args))]
    [(printf-lang (++ f1:fmt f2:fmt)) 
     (and (fmt-consistent-with-vlist? f1 args)
          (fmt-consistent-with-vlist? f2 args))]
    ))
|#

(define (mem? m)
  (match m
    [(printf-lang mnil) #t]
    [(printf-lang (mcons x:ident v:val m+:mem))
     (and (ident? x) (val? v) (mem? m+))]
    [_ #f]
    ))

(define (conf? conf)
  (match conf
    [(printf-lang (i:integer m:mem)) (and (bonsai-integer? i) (mem? m))] 
    [_ #f]
    ))
