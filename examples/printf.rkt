#lang seec
(require racket/base)


; Formalizing (for now, only safe) calls to printf

(define-language printf-lang
  (fmt ::= (%d natural) (%n natural) (++ fmt fmt))
  (arglist ::= anil (acons val arglist))
  (stack ::= snil (scons frame stack))
  (frame ::= fnil (fcons ident ident frame))
  (mem ::= mnil (mcons ident val mem))
  (val ::= (LOC ident) (CONST integer) ERR)
  (ident ::= a b c d e)
  ; a configuration consists of an accumulator and a memory value
  (config ::= (CONF integer mem))
  )

; To install quickcheck, run `raco pkg install quickcheck`

#;(define (choose-bool)
  (make-generator
   (lambda (size rgen)
     (call-with-values
	 (lambda ()
	   (random-integer rgen 0 1))
       (lambda (n _)
	 n)))))


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

(define offset-example 1)
(define arglist-example (printf-lang (acons (LOC a) (acons (CONST 10) anil))))
(printf "Lookup offset ~a \n\t in arglist ~a...\n" offset-example arglist-example)
(displayln (lookup-in-arglist offset-example arglist-example))
(newline)


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

(define loc-example (printf-lang b))
(define mem-example (printf-lang (mcons a (CONST 5) (mcons b (CONST 3) mnil))))
(printf "Lookup location ~a \n\t in mem ~a...\n" loc-example mem-example)
(displayln (lookup-loc loc-example mem-example))
(newline)

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    [_ (raise-argument-error 'bonsai->number "bonsai-integer?" n)]
    ))

;(displayln "TEST")
;(bonsai->number 'cow)
;(newline)

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


; INPUT: a configuration (acc,mem) and a number n
; OUTPUT: a new configuration (acc+n,mem)
(define (config-add conf n)
  (let* ([acc   (conf->acc conf)]
         [m     (conf->mem conf)]
         [acc+n (bonsai-integer (+ n acc))])
    (printf-lang (CONF ,acc+n ,m))
    ))

(define config-example (printf-lang (CONF 0 ,mem-example)))
(printf "Adding 3 to configuration ~a...\n" 
        config-example)
(displayln (config-add config-example 3))
(newline)


; INPUT: a format string, an argument list, and a configuration
; OUTPUT: an outputted string and a configuration
(define (interp-fmt f args conf)
  (match f
    [(printf-lang (%d offset:natural))
     (let* ([n (val->number (lookup-in-arglist (bonsai->number offset) args))]
            [len (string-length (number->string n))]
            [new-conf (config-add conf len)]
            )
       (cons (number->string n) new-conf)
       )]

    [(printf-lang (%n offset:natural))
     (let* ([l (val->loc (lookup-in-arglist (bonsai->number offset) args))]
            [acc (conf->acc conf)]
            [new-mem (printf-lang (mcons ,l (CONST ,acc) ,(conf->mem conf)))]
            )
       (cons "" (printf-lang (CONF ,acc ,new-mem))))
       ]

    [(printf-lang (++ f1:fmt f2:fmt))
     #;(match-let* ([(cons s-1 conf-1) (interp-fmt f1 args conf)]
                     [(cons s-2 conf-2) (interp-fmt f2 args conf-1)])
       (cons (string-append s-1 s-2) conf-2))
     (let* ([s-conf-1 (interp-fmt f1 args conf)  ]
            [s-1      (car s-conf-1)             ]
            [conf-1   (cdr s-conf-1)             ]
            [s-conf-2 (interp-fmt f2 args conf-1)]
            [s-2      (car s-conf-2)             ]
            [conf-2   (cdr s-conf-2)             ]
            )
       (cons (string-append s-1 s-2) conf-2))
     ]

    [_ (raise-argument-error 'interp-fmt "(printf-lang fmt)" f)]
    ))

(define format-string-example 
  (printf-lang (++ (%d 1) (%n 0)))
  ;(printf-lang (%n 0))
  )
(printf "Interpreting format string ~a\n\t with arguments ~a\n\t with config ~a...\n"
        format-string-example
        arglist-example
        config-example)
(displayln (interp-fmt format-string-example arglist-example config-example))
(newline)
