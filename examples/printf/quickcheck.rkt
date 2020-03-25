#lang seec

; To install quickcheck, run `raco pkg install quickcheck`
(require racket/base
         quickcheck
         (file "syntax.rkt")
         )


#| Generator constructors |#


; A singleton generator that always generates the value v
(define (choice v)
  (bind-generators () v)
  )

; INPUT: a list gens of generators
; OUTPUT: a generator that randomly generates an element from one of the
;         elements of the list
(define (choose gens)
  (bind-generators
   ([i (choose-integer 0 (- (length gens) 1))]
    [x (list-ref gens i)]
    )
   x
   ))

; generate tuples from a pair of generators
(define (choose-pair gen1 gen2)
  (bind-generators 
   ([x1 gen1]
    [x2 gen2]
    )
   (cons x1 x2)
   ))

#||||||||||||||||||||||||||#
#| printf-lang generators |#
#||||||||||||||||||||||||||#

; generate an identifier
(define (choose-ident)
  (choose (list (choice (printf-lang a))
                (choice (printf-lang b))
                (choice (printf-lang c))
                (choice (printf-lang d))
                (choice (printf-lang e))
          )))

(printf "Testing ident generator...\n")
(quickcheck (property ([x (choose-ident)]) (ident? x)))
(newline)

(define (choose-bonsai-nat max-nat)
  (bind-generators
   ([n (choose-integer 0 max-nat)])
   (bonsai-integer n)
   ))
(printf "Testing bonsai-nat generator...\n")
(quickcheck (property ([n (choose-bonsai-nat 10)]) (bonsai-integer? n)))
(newline)

; generate a format string of length 1, with argument offsets less than
; max-arglength
(define (choose-fmt-1 max-arglength)
  (bind-generators
   ([offset (choose-bonsai-nat (- max-arglength 1))]
    [f (choose (list (choice (printf-lang (%d ,offset)))
                     (choice (printf-lang (%n ,offset)))
                     ))]
    )
   f))
(printf "Testing choose-fmt-1 generator...\n")
(quickcheck (property ([f (choose-fmt-1 4)])
                      (match f
                        [(printf-lang (%d natural)) #t]
                        [(printf-lang (%n natural)) #t]
                        [_ #f])
                      ))
(newline)

; generate a format string of length fmt-length, with argument offsets less than
; max-arglength
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

(printf "Testing choose-fmt-with-length...\n")
(quickcheck (property ([f (choose-fmt-with-length 4 5)])
                      (fmt? f)
                      ))
(newline)

; generate a format string of length at most max-fmt-length, with argument
; offsets less than max-arglength
(define (choose-fmt max-arglength max-fmt-length)
  (bind-generators
   ([fmt-length (choose-integer 0 (- max-fmt-length 1))]
    [f          (choose-fmt-with-length max-arglength fmt-length)]
    )
   f
   ))

(printf "Testing choose-fmt...\n")
(quickcheck (property ([f (choose-fmt 4 5)])
                      (fmt? f)
                      ))
(newline)

; generate a value with constants between -max-const and max-const
(define (choose-val max-const)
  (let ([choose-err (choice (printf-lang ERR))]
        [choose-loc 
         (bind-generators ([x (choose-ident)])
                          (printf-lang (LOC ,x)))]
        [choose-const 
         (bind-generators ([n (choose-integer (- 0 max-const) max-const)])
                          (printf-lang (CONST ,(bonsai-integer n))))]
        )
    (choose (list choose-err choose-loc choose-const))
    )
  #;(bind-generators 
   ([rand (choose-integer 0 2)]
    [x (choose-ident)]
    [c (choose-integer (- 0 max-const) max-const)]
    )
   (case rand
     [(0) (printf-lang ERR)]
     [(1) (printf-lang (LOC ,x))]
     [(2) (printf-lang (CONST ,(bonsai-integer c)))]
     ))
  )
(printf "Testing choose-val...\n")
(quickcheck (property ([v (choose-val 10)])
                      (val? v)))
(newline)

;;;;;;;;;;;;;;;;;;;;;;;
; generate an arglist ;
;;;;;;;;;;;;;;;;;;;;;;;

; convert a list of printf-lang values into an arglist
(define (list->arglist args)
  (if (empty? args)
      (printf-lang anil)
      (printf-lang (acons ,(first args) ,(list->arglist (rest args))))
      ))

; generate an argument list of length size
(define (choose-arglist-size max-const size)
  (bind-generators
   ([args (choose-list (choose-val max-const) size)])
   (list->arglist args)
   ))

; generate an argument list of length at most max-size
(define (choose-arglist max-const max-size)
  (bind-generators
   ([size (choose-integer 0 max-size)]
    [args (choose-arglist-size max-const size)]
    )
   args
   ))
   
(printf "Testing choose-arglist...\n")
(quickcheck (property ([args (choose-arglist 10 3)])
                      (arglist? args)))
(newline)


;;;;;;;;;;;;;;;;;;
; generate a mem ;
;;;;;;;;;;;;;;;;;;

; convert a list of ident-value pairs into a printf-lang mem
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
; generate a mem of size exactly size
(define (choose-mem-size max-const size)
  (bind-generators
   ([mem-list (choose-list (choose-pair (choose-ident) 
                                        (choose-val max-const))
                           size)])
   (list->mem mem-list)
   ))
; generate a mem of size at most max-size
(define (choose-mem max-const max-size)
  (bind-generators
   ([size (choose-integer 0 max-size)]
    [m (choose-mem-size max-const size)]
    )
   m
   ))

(printf "Testing choose-mem...\n")
(quickcheck (property ([m (choose-mem 10 3)])
                      (mem? m)))
(newline)


;;;;;;;;;;;;;;;;;;;;;
; generate a config ;
;;;;;;;;;;;;;;;;;;;;;


(define (choose-config max-const mem-size)
  (bind-generators
   ([acc (choose-bonsai-nat max-const)]
    [m (choose-mem max-const mem-size)]
    )
   (printf-lang (CONF ,acc ,m))
   ))

(printf "Testing choose-config...\n")
(quickcheck (property ([conf (choose-config 10 4)])
                      (conf? conf)))

(newline)



#||||||||||||||||||||||||||#
#| printf-lang operations |#
#||||||||||||||||||||||||||#

;;;;;;;;;;;;;;;;;;;;;
; lookup-in-arglist ;
;;;;;;;;;;;;;;;;;;;;;

(printf "Testing lookup-in-arglist...\n")
(define (lookup-in-arglist-property max-const num-args)
  (property ([offset   (choose-integer 0 num-args)]
             [args     (choose-arglist max-const num-args)]
             )
            (val? (lookup-in-arglist offset args))
            ))
(quickcheck (lookup-in-arglist-property 100 10))
(newline)

;;;;;;;;;;;;;;
; lookup-loc ;
;;;;;;;;;;;;;;

(printf "Testing lookup-loc...\n")
(define (lookup-loc-property max-const max-size)
  (property ( [l (choose-ident)]
              [m (choose-mem max-const max-size)]
             )
            (val? (lookup-loc l m))
            ))
(quickcheck (lookup-loc-property 100 10))
(newline)

;;;;;;;;;;;;;;
; mem-update ;
;;;;;;;;;;;;;;

(printf "Testing mem-update...\n")
(define (mem-update-property max-const max-size)
  (property ([l (choose-ident)]
             [m (choose-mem max-const max-size)]
             [v (choose-val max-const)]
             )
            (mem? (mem-update m l v))
            ))
(quickcheck (mem-update-property 100 10))
(newline)

;;;;;;;;;;;;;;
; interp-fmt ;
;;;;;;;;;;;;;;

(printf "Testing interp-fmt...\n")
(define (interp-fmt-property max-const max-arglength max-fmt-length mem-size)
  (property ([f    (choose-fmt max-arglength max-fmt-length)]
             [args (choose-arglist max-const max-arglength)]
             [conf (choose-config max-const mem-size)]
             )
            (match (interp-fmt f args conf)
              [(list str conf)
               (and (string? str) (conf? conf))]
              )
            #;(let* ([res (interp-fmt f args conf)]
                   [str (car res)]
                   [conf (cdr res)]
                   )
              (and (string? str)
                   (conf? conf)
                   )
              )))
(quickcheck (interp-fmt-property 100 10 10 10))
(newline)
