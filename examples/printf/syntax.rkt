#lang seec
#;(require racket/base)
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))

(require (only-in racket/base
                  [make-string unsafe:make-string]
                  ))


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

(define-language printf-lang
  (fmt ::= list<fmt-elt>)
  (fmt-elt ::= string
               (% parameter $ width fmt-type))
  (width ::= NONE (* offset) natural)
  (parameter ::= offset)
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

(define (interp-d-safe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang n:integer) (print-d-integer conf (bonsai->number n))]
       [_ ; if the offset does not map to a number, throw an error
        (raise-arguments-error 'interp-d-safe
                               "Offset does not map to a number in the vlist"
                               "offset" (bonsai->number offset)
                               "vlist" args)]
       ))
(define (interp-n-safe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (LOC l:ident)) (list (string "") (print-n-loc conf l))]
       [_ ; if the offset does not map to a location, throw an error
        (raise-arguments-error 'interp-n-safe
                               "Offset does not map to a location in the vlist"
                               "offset" (bonsai->number offset)
                               "vlist" args)]
       ))

(define (interp-ftype-safe ftype param args conf)
  (match (cons ftype (lookup-offset (bonsai->number param) args))
    [(cons (printf-lang d) (printf-lang n:integer))
     (print-d-integer conf (bonsai->number n))
     ]
    [(cons (printf-lang n) (printf-lang (LOC l:ident)))
     (list (string "") (print-n-loc conf l))]
    [(cons x y) (raise-arguments-error 'interp-ftype-safe
                                       "Offset does not map to a value of the correct type"
                                       "fmt-type" (display ftype)
                                       "parameter" (bonsai->number param)
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
  (match f
    [(printf-lang s:string)
     (list (bonsai-string-value s) (config-add conf (string-length (bonsai-string-value s))))]

    [(printf-lang (% p:parameter $ NONE ftype:fmt-type))
     (interp-ftype-safe ftype p args conf)]
    [(printf-lang (% p:parameter $ w:natural ftype:fmt-type))
     (pad-by-width (bonsai->number w) (interp-ftype-safe ftype p args conf))]
    [(printf-lang (% p:parameter $ (* o:offset) ftype:fmt-type))
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


(define (interp-d-unsafe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang n:integer) (print-d-integer conf (bonsai->number n))]
       [_ ; if the offset does not map to a number, do nothing
        (list (string "") conf)]
       ))
(define (interp-n-unsafe offset args conf)
  (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (LOC l:ident)) (list (string "") (print-n-loc conf l))]
       [_ ; if the offset does not map to a location, do nothing
        (list (string "") conf)]
       ))


(define (interp-ftype-unsafe ftype param args conf)
  (match (cons ftype (lookup-offset (bonsai->number param) args))
    [(cons (printf-lang d) (printf-lang n:integer))
     (print-d-integer conf (bonsai->number n))
     ]
    [(cons (printf-lang n) (printf-lang (LOC l:ident)))
     (list (string "") (print-n-loc conf l))]
    [_ (list (string "") conf)]
    ))



; INPUT: a format string, a stack (we assume that the arguments have been pushed
; onto the stack, and a configuration
; OUTPUT: an outputted string and a configuration
(define (interp-fmt-elt-unsafe f args conf)
  (match f

    [(printf-lang s:string)
     (list s (config-add conf (string-length s)))]

    [(printf-lang (% p:parameter $ NONE ftype:fmt-type))
     (interp-ftype-unsafe ftype p args conf)]
    [(printf-lang (% p:parameter $ w:natural ftype:fmt-type))
     (pad-by-width (bonsai->number w) (interp-ftype-unsafe ftype p args conf))]
    [(printf-lang (% p:parameter $ (* o:offset) ftype:fmt-type))
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
  (let* ([offset (bonsai->number p)]
         [arg (lookup-offset offset args)])
    (and (< (bonsai->number p) (bonsai-ll-length args))
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

      [(printf-lang (% p:parameter $ w:width ftype:fmt-type))
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
