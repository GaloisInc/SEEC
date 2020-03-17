#lang seec
(require racket/base)

; Formalizing (for now, only safe) calls to printf

(define-language printf-lang
  (fmt ::= (%d natural) (%n natural) (++ fmt fmt))
  (arglist ::= anil (acons val arglist))
  (stack ::= snil (scons frame stack))
  (frame ::= fnil (fcons ident loc frame))
  (mem ::= mnil (mcons loc val mem))
  (val ::= (LOC ident) (CONST integer) ERR)
  (ident ::= a b c d e)
  ; a configuration consists of an accumulator and a memory value
  (config ::= (CONF integer mem))
  )

(define (bonsai->number n)
  (match n
    [(bonsai-integer i) i]
    )
  )

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
(define arglist-example (printf-lang (acons (CONST 0) (acons (CONST 10) anil))))
(printf "Lookup offset ~a \n\t in arglist ~a...\n" offset-example arglist-example)
(displayln (lookup-in-arglist offset-example arglist-example))
(newline)

(define (val->number v)
  (match v
    [(printf-lang (CONST n:integer))
     (bonsai->number n)]))

; INPUT: a configuration (acc,mem) and a number n
; OUTPUT: a new configuration (acc+n,mem)
(define (config-add conf n)
  (match conf
    [(printf-lang (CONF acc:integer m:mem))
     (printf-lang (CONF ,(bonsai-integer (+ n (bonsai->number acc))) ,m))]))

(define config-example (printf-lang (CONF 0 mnil)))
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

    [(printf-lang (%n natural)) #t] ; TODO

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
       (cons (string-append s-1 s-2) conf-2))]
    ))

(define format-string-example (printf-lang (++ (%d 1) (%d 0))))
(printf "Interpreting format string ~a\n\t with arguments ~a\n\t with config ~a...\n"
        format-string-example
        arglist-example
        config-example)
(displayln (interp-fmt format-string-example arglist-example config-example))
(newline)
