#lang seec
(require racket/base)

; To install quickcheck, run `raco pkg install quickcheck`
(require quickcheck)

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

(define (fmt? f)
  (match f
    [(printf-lang f-empty) #t]
    [(printf-lang (%d natural)) #t]
    [(printf-lang (%n natural)) #t]
    [(printf-lang (++ f1:fmt f2:fmt)) (and (fmt? f1) (fmt? f2))]
    [_ #f]
    ))
;(fmt? (printf-lang (%d 1)))
;(fmt? (printf-lang (%d ,(bonsai-integer (- 3 2)))))


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

(define (arglist? args)
  (match args
    [(printf-lang anil) #t]
    [(printf-lang (acons v:val args+:arglist)) (and (val? v) (arglist? args+))]
    [_ #f]
    ))

(define (choose-ident)
  (bind-generators
   ([x (choose-integer 0 4)])
   (case x 
     [(0) (printf-lang a)]
     [(1) (printf-lang b)]
     [(2) (printf-lang c)]
     [(3) (printf-lang d)]
     [(4) (printf-lang e)]
     )
  ))

(printf "Choosing an ident generator...\n")
(choose-ident)
(quickcheck (property ([x (choose-ident)]) (ident? x)
                      #;(or (equal? x (printf-lang a))
                          (equal? x (printf-lang b))
                          (equal? x (printf-lang c))
                          (equal? x (printf-lang d))
                          (equal? x (printf-lang e))
                          )
                      )
            )

(define (choose-fmt-1 max-arglength)
  (bind-generators
   ([x (choose-integer 0 1)]
    [offset (choose-integer 0 (- max-arglength 1))]
    )
   (case x
     [(0) (printf-lang (%d ,(bonsai-integer offset)))]
     [(1) (printf-lang (%n ,(bonsai-integer offset)))]
     )
   ))
(quickcheck (property ([f (choose-fmt-1 4)])
                      (match f
                        [(printf-lang (%d natural)) #t]
                        [(printf-lang (%n natural)) #t]
                        [_ #f])
                      ))
(define (choose-fmt-with-length max-arglength fmt-length)
  (cond 
    [(<= fmt-length 0)     (printf-lang f-empty)]
    [(equal? fmt-length 1) (choose-fmt-1 max-arglength)]
    [else (bind-generators
           ([split (choose-integer 1 (- fmt-length 1))]
            [fmt1  (choose-fmt-with-length max-arglength split)]
            [fmt2  (choose-fmt-with-length max-arglength (- fmt-length split))]
            )
           (printf-lang (++ ,fmt1 ,fmt2)))]
    ))
(quickcheck (property ([f (choose-fmt-with-length 4 5)])
                      (fmt? f)
                      ))
(define (choose-fmt max-arglength max-fmt-length)
  (bind-generators
   ([fmt-length (choose-integer 0 (- max-fmt-length 1))])
   (choose-fmt-with-length max-arglength fmt-length)
   ))
(quickcheck (property ([f (choose-fmt-with-length 4 5)])
                      (fmt? f)
                      ))

#;(define (choose gens)
  (bind-generators
   ([i (choose-integer 1 (length gens))]
    [x (list-ref gens i)]
    )
   x
   ))
(define (choose-val max-const)
  (bind-generators 
   ([rand (choose-integer 0 2)]
    [x (choose-ident)]
    [c (choose-integer (- 0 max-const) max-const)]
    )
   (case rand
     [(0) (printf-lang ERR)]
     [(1) (printf-lang (LOC ,x))]
     [(2) (printf-lang (CONST ,(bonsai-integer c)))]
     )))

(quickcheck (property ([v (choose-val 10)])
                      (val? v)))

(define (list->arglist args)
  (if (empty? args)
      (printf-lang anil)
      (printf-lang (acons ,(first args) ,(list->arglist (rest args))))
      ))

(define (choose-arglist-size max-const size)
  (bind-generators
   ([args (choose-list (choose-val max-const) size)])
   (list->arglist args)
   ))
(define (choose-arglist max-const max-size)
  (bind-generators
   ([size (choose-integer 0 max-size)]
    [args (choose-arglist-size max-const size)]
    )
   args
   ))
   

(quickcheck (property ([args (choose-arglist 10 3)])
                      (arglist? args)))


(define (mem? m)
  (match m
    [(printf-lang mnil) #t]
    [(printf-lang (mcons x:ident v:val m+:mem))
     (and (ident? x) (val? v) (mem? m+))]
    [_ #f]
    ))

(define (config? conf)
  (match conf
    ; do we really need these recursive checks?
    [(printf-lang (CONF i:integer m:mem)) (and (bonsai-integer? i) (mem? m))] 
    [_ #f]
    ))

; mem-list is a list of pairs of identifier
(define (list->mem mem-list)
  (if (empty? mem-list)
      (printf-lang mnil)
      (let* ([ident-val (first mem-list)]
             [x (car ident-val)]
             [v (cdr ident-val)]
             [m+ (list->mem (rest mem-list))]
             )
        (printf-lang (mcons ,x ,v ,m+))
        )))
(define (choose-pair gen1 gen2)
  (bind-generators 
   ([x1 gen1]
    [x2 gen2]
    )
   (cons x1 x2)
   ))
(define (choose-mem-size max-const size)
  (bind-generators
   ([mem-list (choose-list (choose-pair (choose-ident) 
                                        (choose-val max-const))
                           size)])
   (list->mem mem-list)
   ))
(define (choose-mem max-const max-size)
  (bind-generators
   ([size (choose-integer 0 max-size)]
    [m (choose-mem-size max-const size)]
    )
   m
   ))



(quickcheck (property ([m (choose-mem 10 3)])
                      (mem? m)))


(define (choose-config max-const mem-size)
  (bind-generators
   ([acc (choose-integer 0 max-const)]
    [m (choose-mem max-const mem-size)]
    )
   (printf-lang (CONF ,(bonsai-integer acc) ,m))
   ))
(quickcheck (property ([conf (choose-config 10 4)])
                      (config? conf)))

(newline)


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
    [(printf-lang f-empty)
     (cons "" conf)
     ]

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
