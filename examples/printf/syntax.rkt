#lang seec
(require racket/base)


(provide printf-lang
         bonsai->number
         val->number
         val->loc
         conf->mem
         lookup-in-arglist
         arglist-length
         lookup-loc
         config-add
         mem-update
         interp-fmt-safe
         fmt?
         ident?
         val?
         const?
         loc?
         arglist?
         mem?
         conf?
         fmt-consistent-with-arglist?
         )

; Formalizing (for now, only safe) calls to printf

(define-language printf-lang
  (fmt ::= f-empty (%d natural) (%n natural) (++ fmt fmt))
  (arglist ::= anil (acons val arglist))
  (stack ::= snil (scons frame stack))
  (frame ::= fnil (fcons ident ident frame))
  (mem ::= mnil (mcons ident val mem))
  (val ::= (LOC ident) (CONST integer) ERR)
  (ident ::= a b c d e)
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
(define (lookup-in-arglist offset args)
  (match args
    [(printf-lang anil) (printf-lang ERR)]
    [(printf-lang (acons v:val args+:arglist))
     (if (<= offset 0)
         v
         (lookup-in-arglist (- offset 1) args+))]
    )
  )

(define (arglist-length args)
  (match args
    [(printf-lang anil) 0]
    [(printf-lang (acons val args+:arglist))
     (+ 1 (arglist-length args+))]
    [_ (raise-argument-error 'arglist-length "arglist?" args)]
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


; INPUT: a format string, an argument list, and a configuration
; OUTPUT: an outputted string and a configuration
(define (interp-fmt-safe f args conf)
  (match f
    [(printf-lang f-empty)
     (list "" conf)
     ]

    [(printf-lang (%d offset:natural))
     (match (lookup-in-arglist (bonsai->number offset) args)
       [(printf-lang (CONST n:integer))
        (let* ([n+ (bonsai->number n)]
               [len (string-length (number->string n+))]
               [new-conf (config-add conf len)]
               )
          (list (number->string n+) new-conf)
          )]
       [_ ; if the offset does not map to a number, then do nothing
        #;(list "" conf)
        (raise-arguments-error 'interp-fmt-safe
                               "Offset does not map to a number in the arglist"
                               "offset" (bonsai->number offset)
                               "arglist" args)
        ]
       )

     #;(let* ([n (val->number (lookup-in-arglist (bonsai->number offset) args))]
            [len (string-length (number->string n))]
            [new-conf (config-add conf len)]
            )
       (if (conf? new-conf)
           (list (number->string n) new-conf)
           ; else
           (raise-argument-error 'printf-lang "conf? in %d" conf))
       )
     ]

    [(printf-lang (%n offset:natural))
     (match (lookup-in-arglist (bonsai->number offset) args)
       [(printf-lang (LOC l:ident))
        (let* ([acc (bonsai-integer (conf->acc conf))]
               [acc-val (printf-lang (CONST ,acc))]
               [new-mem (mem-update (conf->mem conf) l acc-val)]
               )
          (list "" (printf-lang (CONF ,acc ,new-mem)))
          )]
       [_ ; if the offset does not map to a location, then do nothing
        (list "" conf)]
       )
     ]

    [(printf-lang (++ f1:fmt f2:fmt))
     #;(match-let* ([(list s-1 conf-1) (interp-fmt-safe f1 args conf)]
                  [(list s-2 conf-2) (interp-fmt-safe f2 args conf-1)])
       (cons (string-append s-1 s-2) conf-2))
     #;(let* ([s-conf-1 (interp-fmt-safe f1 args conf)  ]
            [s-1      (car s-conf-1)             ]
            [conf-1   (cdr s-conf-1)             ]
            )
       (let* ([s-conf-2 (interp-fmt-safe f2 args conf-1)]
              [s-2      (car s-conf-2)             ]
              [conf-2   (cdr s-conf-2)             ]
              )
         (list (string-append s-1 s-2) conf-2)))
     (match (interp-fmt-safe f1 args conf)
       [(list s-1 conf-1) 
        (match (interp-fmt-safe f2 args conf-1)
          [(list s-2 conf-2)
           (list (string-append s-1 s-2) conf-2)
           ]
          )
        ]
       )
     ]

    ;[_ (list "" (printf-lang ERR))]
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
  (match x
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


(define (arglist? args)
  (match args
    [(printf-lang anil) #t]
    [(printf-lang (acons v:val args+:arglist)) (and (val? v) (arglist? args+))]
    [_ #f]
    ))


(define (fmt-consistent-with-arglist? f args)
  (match f
    [(printf-lang f-empty) #t]
    [(printf-lang (%d offset:natural))
     (const? (lookup-in-arglist (bonsai->number offset) args))]
    [(printf-lang (%n offset:natural))
     (loc? (lookup-in-arglist (bonsai->number offset) args))]
    [(printf-lang (++ f1:fmt f2:fmt)) 
     (and (fmt-consistent-with-arglist? f1 args)
          (fmt-consistent-with-arglist? f2 args))]
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
    ; do we really need these recursive checks?
    [(printf-lang (CONF i:integer m:mem)) (and (bonsai-integer? i) (mem? m))] 
    [_ #f]
    ))
