#lang seec
#;(require racket/base)
(require (only-in racket/base
                  raise-argument-error
                  raise-arguments-error))
(require (file "../string.rkt"))


(provide printf-lang
         bonsai->number
         val->number
         val->loc
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

; Formalizing (for now, only safe) calls to printf

(define-language printf-lang
  (fmt ::= f-empty (%d natural) (%n natural) (++ fmt fmt))
  (vlist ::= anil (acons val vlist))
  (mem ::= mnil (mcons ident val mem))
  (val ::= (LOC ident) (CONST integer) ERR #;(DEREF val)) 
  (ident ::= integer)
  ; a configuration consists of an accumulator and a memory value
  (config ::= (CONF integer mem))
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
    [(printf-lang (CONST n:integer)) (bonsai->number n)]
    [_ (raise-argument-error 'val->number "(printf-lang (CONST integer))" v)]
    ))
(define (val->loc v)
  (match v
    [(printf-lang (LOC x:ident)) x]
    [_ (raise-argument-error 'val->loc "(printf-lang (LOC ident))" v)]
    ))
(define (conf->mem c)
  (match c
    [(printf-lang (CONF integer m:mem)) m]
    [_ (raise-argument-error 'conf->mem "conf" c)]
    ))
(define (conf->acc c)
  (match c
    [(printf-lang (CONF acc:integer mem)) (bonsai->number acc)]
    [_ (raise-argument-error 'conf->acc "conf" c)]
    ))


#|||||||||||||||||||||||||||||#
#| Operations on printf-lang |#
#|||||||||||||||||||||||||||||#

; INPUT: an integer offset and an argument list args such that offset < length(args)
; OUTPUT: the value mapped to the offset
(define (lookup-offset offset args)
  (match args
    [(printf-lang anil) (printf-lang ERR)]
    [(printf-lang (acons v:val args+:vlist))
     (if (<= offset 0)
         v
         (lookup-offset (- offset 1) args+))]
    )
  )

(define (vlist-length args)
  (match args
    [(printf-lang anil) 0]
    [(printf-lang (acons val args+:vlist))
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
    (printf-lang (CONF ,acc+n ,m))
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
         [acc-val (printf-lang (CONST ,acc))]
         [new-mem (mem-update (conf->mem conf) l acc-val)]
         )
    (printf-lang (CONF ,acc ,new-mem))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an abstract "safe" implementation of printf                          ;
;                                                                             ;
; If an argument in the format string is not in scope with respect to the     ;
; argument list, or if it maps to a value of the wrong type, it will throw an ;
; error.                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; INPUT: a format string, an argument list, and a configuration
; OUTPUT: an outputted string and a configuration
(define (interp-fmt-safe f args conf)
  (match f
    [(printf-lang f-empty)
     (list (mk-string "") conf)
     ]

    [(printf-lang (%d offset:natural))
     (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (CONST n:integer)) (print-d-integer conf (bonsai->number n))]
       [_ ; if the offset does not map to a number, throw an error
        (raise-arguments-error 'interp-fmt-safe
                               "Offset does not map to a number in the vlist"
                               "offset" (bonsai->number offset)
                               "vlist" args)]
       )]

    [(printf-lang (%n offset:natural))
     (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (LOC l:ident)) (list (mk-string "") (print-n-loc conf l))]
       [_ ; if the offset does not map to a location, throw an error
        (raise-arguments-error 'interp-fmt-safe
                               "Offset does not map to a location in the vlist"
                               "offset" (bonsai->number offset)
                               "vlist" args)]
       )]

    [(printf-lang (++ f1:fmt f2:fmt))
     #;(match-let* ([(list s-1 conf-1) (interp-fmt-safe f1 args conf)]
                  [(list s-2 conf-2) (interp-fmt-safe f2 args conf-1)])
       (cons (string-append s-1 s-2) conf-2))
     (match (interp-fmt-safe f1 args conf)
       [(list s-1 conf-1) 
        (match (interp-fmt-safe f2 args conf-1)
          [(list s-2 conf-2)
           (list (string-append s-1 s-2) conf-2)
           ])])]

    [_ (raise-argument-error 'interp-fmt-safe "(printf-lang fmt)" f)]
    ))

(displayln "Running test case demonstrating match-let failure...")
(interp-fmt-safe (printf-lang (++ f-empty f-empty))
                 (printf-lang anil)
                 (printf-lang (CONF 0 mnil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Define an concrete "unsafe" implementation of printf                          ;
;                                                                               ;
; If an argument in the format string is not in scope with respect to the       ;
; argument list, or if it maps to a value of the wrong type, it will return the ;
; empty string and proceed silently.                                            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; INPUT: a format string, a stack (we assume that the arguments have been pushed
; onto the stack, and a configuration
; OUTPUT: an outputted string and a configuration
(define (interp-fmt-unsafe f args conf)
  (match f
    [(printf-lang f-empty)
     (list (mk-string "") conf)
     ]

    [(printf-lang (%d offset:natural))
     (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (CONST n:integer)) (print-d-integer conf (bonsai->number n))]
       [_ ; if the offset does not map to a number, do nothing
        (list (mk-string "") conf)]
       )]

    [(printf-lang (%n offset:natural))
     (match (lookup-offset (bonsai->number offset) args)
       [(printf-lang (LOC l:ident)) (list (mk-string "") (print-n-loc conf l))]
       [_ ; if the offset does not map to a location, do nothing
        (list (mk-string "") conf)]
       )]

    [(printf-lang (++ f1:fmt f2:fmt))
     #;(match-let* ([(list s-1 conf-1) (interp-fmt-unsafe f1 args conf)]
                  [(list s-2 conf-2) (interp-fmt-unsafe f2 args conf-1)])
       (cons (string-append s-1 s-2) conf-2))
     (match (interp-fmt-unsafe f1 args conf)
       [(list s-1 conf-1) 
        (match (interp-fmt-unsafe f2 args conf-1)
          [(list s-2 conf-2)
           (list (string-append s-1 s-2) conf-2)
           ])])]

    [_ (raise-argument-error 'interp-fmt-safe "(printf-lang fmt)" f)]
    ))


#|||||||||||||||||||||||||||||||||||||#
#| Classifiers for printf-lang forms |#
#|||||||||||||||||||||||||||||||||||||#

(define (fmt? f)
  (match f
    [(printf-lang f-empty) #t]
    [(printf-lang (%d natural)) #t]
    [(printf-lang (%n natural)) #t]
    [(printf-lang (++ f1:fmt f2:fmt)) (and (fmt? f1) (fmt? f2))]
    [_ #f]
    ))

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
    [(printf-lang (LOC ident)) #t]
    [(printf-lang (CONST integer)) #t]
    [(printf-lang ERR) #t]
    [_ #f]
    ))
(define (const? v)
  (match v
    [(printf-lang (CONST integer)) #t]
    [_ #f]
    ))
(define (loc? v)
  (match v
    [(printf-lang (LOC integer)) #t]
    [_ #f]
    ))


(define (vlist? args)
  (match args
    [(printf-lang anil) #t]
    [(printf-lang (acons v:val args+:vlist)) (and (val? v) (vlist? args+))]
    [_ #f]
    ))


(define (fmt-consistent-with-vlist? f args)
  (match f
    [(printf-lang f-empty) #t]
    [(printf-lang (%d offset:natural))
     (const? (lookup-offset (bonsai->number offset) args))]
    [(printf-lang (%n offset:natural))
     (loc? (lookup-offset (bonsai->number offset) args))]
    [(printf-lang (++ f1:fmt f2:fmt)) 
     (and (fmt-consistent-with-vlist? f1 args)
          (fmt-consistent-with-vlist? f2 args))]
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
    [(printf-lang (CONF i:integer m:mem)) (and (bonsai-integer? i) (mem? m))] 
    [_ #f]
    ))
