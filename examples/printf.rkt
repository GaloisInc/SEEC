#lang seec

; Formalizing (for now, only safe) calls to printf

(define-language printf-lang
  (fmt ::= (%d natural) (%n natural) (++ fmt fmt))
;  (arglist ::= (ARGS val ..))
;  (stack ::= (ST frame ..))
;  (frame ::= (FR (var . loc) ..))
;  (mem ::= (MEM (loc . val) .. ))
;  (val ::= (LOC ident) (CONST natural) ERR)
  (ident ::= a b c d e)
  )


(define (interp-fmt f)
  (match f
    [(printf-lang (%d n:natural)) n]
    [(printf-lang (%n natural)) #t]
    [(printf-lang (++ f1:fmt f2:fmt)) #t]
    ))

(interp-fmt (printf-lang (%d 5)))
#|

(define lang
  '(; format strings
    [format-string (%d . nat)
         (%n . nat)
         (concat . (fmt . fmt))
         ]
    ; an argument list
    [arglist anil
             (acons . (val . arglist))
             ]
    ; a stack is a list of stack frames
    [stack snil
           (scons . (frame . stack))
           ]
    ; a stack frame is a map from variables to locations
    [frame fnil
           (fcons . (var . (loc . frame)))
           ]
    ; a memory is a map from locations to values
    ; I really wish I could reuse infrastructure for lists/maps
    [mem mnil
         (mmcons . (loc . (val . mem)))
         ]

    ; numbers
    [nat zz
         (b0 . nat)
         (b1 . nat)
         ]
    ; a value is either a constant number, a location, or an error
    [val loc
         (constant . nat)
         err
         ]
    ; can extend identifiers manually?
    [loc (location . ident)]
    [var (variable . ident)]
    [ident a b c d e]
    )
)
(nonterminals! (harvest lang))


(define ZZ (symbol->enum 'zz))
(define B0 (symbol->enum 'b0))
(define B1 (symbol->enum 'b1))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; increment binary numbers
(define (inc n)
  (tree-match n
              'zz (λ () '(B1 . ZZ))
              '(b0 . _) (λ (n+) `(,B1 . ,n+))
              '(b1 . _) (λ (n+) `(,B0 . ,(racket->bonsai (inc n+))))
              )
  )



(define test-nat 
  (racket->bonsai
;   'zz
   '(b0 . zz)
   )
  )

; interpret numbers
(define (eval-nat n)
  (tree-match n
              'zz (λ () 0)
              '(b0 . _) (λ (n+) (* 2 (eval-nat n+)))
              '(b1 . _) (λ (n+) (+ 1 (* 2 (eval-nat n+))))
              )
  )

(define (print-nat n)
  (eval-nat (racket->bonsai n)))


(displayln "Test nat...")
(displayln (eval-nat test-nat))
(displayln "Increment test nat...")
;(displayln (inc test-nat))
(echo (inc test-nat))
(echo (inc (inc test-nat)))
(displayln (inc (inc test-nat)))
;(displayln (eval-nat (racket->bonsai (inc test-nat))))
;(displayln (print-nat (inc 'zz)))
(newline)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; look up an identifier in a stack frame, return a value
(define (lookup-var-in-frame x f)
  (tree-match f
              '(fcons . (_ . (_ . _)))
              (λ (y l f+)
                (if (equal? x y) l (lookup-var-in-frame x f+))
                )
              'fnil
              (λ () (symbol->enum 'err))
              )
  )

(define test-var 
  (racket->bonsai
   '(variable . a)
   )
  )

(define test-frame
  (racket->bonsai
   'fnil
;   '(fcons . ((variable . a) . ((constant . zz) . fnil)))
;   '(fcons (variable . b) (constant . zz) 
;     fcons (variable . a) (constant . zz))
   )
  )

(displayln "Test variable...")
(echo test-var)
(displayln "Test frame...")
(echo test-frame)
(displayln "Look up test variable in test frame...")
(echo (lookup-var-in-frame test-var test-frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; look up a location in memory
(define (lookup-loc-in-mem l m)
  (tree-match m
              '(mmcons . ( _ . (_ . _)))
              (λ (l0 v0 m+)
                (if (equal? l l0) v0 (lookup-loc-in-mem l m+))
                )
              'mnil
              (λ () (symbol->enum 'err))
              )
  )


(define test-loc 
  (racket->bonsai
   '(location . c)
   )
  )

(define test-mem
  (racket->bonsai
;   'mnil
;   '(mmcons . ((location . c) . ((constant . zz) . fnil)))
   '(mmcons (location . b) (constant . zz) 
     mmcons (location . c) (constant . zz))
   )
  )


(displayln "Test location...")
(echo test-loc)
(displayln "Test mem...")
(echo test-mem)
(displayln "Look up test location in test memory...")
(echo (lookup-loc-in-mem test-loc test-mem))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; look up an argument in an arg-list
(define (lookup-in-arglist n args)
  (tree-match args
              '(acons . ( _ . _))
              (λ (v args+)
                (tree-match n
                            'zz (λ () v)
                            '(suc . _) (λ (n+)
                                         (lookup-in-arglist n+ args+))))
              'anil
              (λ () (symbol->enum 'err))
              )
  )
  

#|
(define test-offset 
  (racket->bonsai
   '(suc . zz)
   )
  )

(define test-arglist
  (racket->bonsai
;   'anil
   '(acons (constant . zz) . anil)
   )
  )


(displayln "Test offset...")
(echo test-offset)
(displayln "Test arglist...")
(echo test-arglist)
(displayln "Look up test offset in test arglist...")
(echo (lookup-in-arglist test-offset test-arglist))

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; input:
;   1. a format string
;   2. a list of arguments
;   3. a stack frame
;   4. a memory
;   5. an accumulator tracking the number of characters printed so far
; output:
;   1. a value
;   2. updated memory
;   3. an updated accumulator
#|
(define (eval-fmt-string-safe fmt args f m acc)
  (tree-match fmt
              (%d . _)
              (λ (o) 
|#

|#
