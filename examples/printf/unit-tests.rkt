#lang seec
(require (prefix-in safe:
                    (file "printf-spec.rkt")))
(require (prefix-in unsafe:
                    (file "printf-impl.rkt")))
(require (file "printf-compiler.rkt"))
(require rackunit)
(require rackunit/text-ui)
(require racket/contract)
(require (only-in racket/base
                  parameterize))


(define (check-safe-unsafe-consistent f args conf)
  (check-equal? (compile-behavior (safe:interp-fmt f args conf))
                (unsafe:interp-fmt f (compile-arglist args) (compile-config conf))))


(define/contract (racket->constant x)
  (-> (or/c integer? string?) safe:const?)
  (safe:printf-lang ,x))
(define/contract (mk-trace l)
  (-> (listof (or/c integer? string?)) safe:trace?)
  (list->seec (map racket->constant l)))

(set-bitwidth 64 32)

(define fmt-d-1 (seec-singleton (safe:printf-lang (% ((0 $) (NONE d))))))
(define fmt-s-1 (seec-singleton (safe:printf-lang (% ((0 $) (NONE s))))))
(define fmt-n-1 (seec-singleton (safe:printf-lang (% ((0 $) (NONE n))))))
(define fmt-d-n (seec-cons      (safe:printf-lang "foo ")
                (seec-cons      (safe:printf-lang (% ((0 $) (NONE d))))
                (seec-singleton (safe:printf-lang (% ((1 $) (NONE n))))))))
(define bv-neg-1 (bitvector->natural (integer->bv -1)))
(define fmt-decrement (seec-singleton (unsafe:printf-lang (% ((0 $) (,bv-neg-1 s))))))

(define arglist-0   (safe:printf-lang nil))
(define arglist-d-1 (seec-singleton (safe:printf-lang 32 #;(bv 32))))
(define arglist-s-1 (seec-singleton (safe:printf-lang "hi")))
(define arglist-n-1 (seec-singleton (safe:printf-lang (LOC 0))))
(define arglist-d-n (seec-append arglist-d-1 arglist-n-1))
(define arglist-s-0 (seec-singleton (safe:printf-lang "")))

(define/provide-test-suite safe-correct
 (test-case "%0$d"
   ; printf("%0$d",32)
   (check-equal? (safe:interp-fmt fmt-d-1
                                  arglist-d-1
                                  (safe:make-config-triv 0))
                 (safe:make-behav-triv (mk-trace (list 32)) 2))
   )
 (test-case "hello world"
  ; printf("hello world")
  (check-equal? (safe:interp-fmt (seec-singleton (safe:printf-lang "hello world"))
                                 arglist-0
                                 (safe:make-config-triv 0))
                (safe:make-behav-triv (mk-trace (list (string "hello world")))
                               11))
  )
 (test-case "%0$s"
  ; printf("%0$s","hi")
  (check-equal? (safe:interp-fmt fmt-s-1
                                 arglist-s-1
                                 (safe:make-config-triv 0))
                (safe:make-behav-triv (mk-trace (list (string "hi")))
                               2))
  )
 (test-case "%0$n"
  ; printf("%0$n",Loc 0)
  (check-equal? (safe:interp-fmt fmt-n-1
                                 arglist-n-1
                                 (safe:make-config-triv 0))
                (safe:make-behav (mk-trace (list))
                          0
                          (safe:printf-lang (cons (0 0) nil)))))

 (test-case "%0$d"
  ; printf("%0$d") ==> ERR
  (check-equal? (safe:interp-fmt fmt-d-1
                                 arglist-0
                                 (safe:make-config-triv 0))
                (safe:printf-lang ERR))
  )
 (test-case "%0$d%1$n"
  ; printf("foo %0$d%1$n",32,Loc 0)
  (parameterize ([safe:debug? #f])
    (check-equal? (safe:interp-fmt fmt-d-n
                                   arglist-d-n
                                   (safe:make-config-triv 0))
                  (safe:make-behav (mk-trace (list (string "foo ")
                                            32))
                            6
                            (safe:printf-lang (cons (0 6) nil))))
    )
  )

  (test-case "add argument from memory"
    (define/contract l safe:ident?
      (safe:printf-lang 1))
    (define fmt  (seec-singleton (safe:printf-lang (% ((0 $) ((* 0) d))))))
    (define args (list->seec (list (safe:printf-lang (* (LOC ,l)))
                                        (safe:printf-lang ""))))
    (define/contract m
      safe:mem?
      (safe:printf-lang (cons (,l 3) nil))
      )
    (define behav (safe:interp-fmt fmt
                                   args
                                   (safe:make-config 1 m)))
    (check-equal? (safe:behavior->config behav)
                  (safe:make-config 4 m))
    )


                                                     
)
; TODO: add test cases for padding
(run-tests safe-correct)

(define/provide-test-suite unsafe-correct


 (test-case "%0$Xs"
  ; printf("%0$Xs,"") ==> add X=fmt-decrement (aka -1) to the accumulator
  (check-equal? (unsafe:behavior->config (unsafe:interp-fmt fmt-decrement
                                                            arglist-s-0
                                                            (unsafe:make-config-triv 2)))
                (unsafe:make-config-triv 1))
  )

  (test-case "%0$d"
  ; printf("%0$d","hi") 
  ; note: the character h is encoded as the number 104
  (check-equal? (unsafe:interp-fmt fmt-d-1
                                   (compile-arglist arglist-s-1)
                                   (unsafe:make-config-triv 0))
                (unsafe:make-behav-triv (mk-trace (list 104)) 3))
  )

  #;(test-case "%0$s" ; we took out this conversion in the model
  ; printf("%0$s",32)
  ; note: 32 is the ASCII representation of the space character
  (check-equal? (unsafe:interp-fmt fmt-s-1
                                   (compile-arglist arglist-d-1)
                                   (unsafe:make-config-triv 0))
                (unsafe:make-behav-triv (mk-trace (list (string " ")))
                               1))
  )

  (test-case "%0$n"
  ; printf("%0$n,32)
  (check-equal? (unsafe:interp-fmt fmt-n-1
                                   (compile-arglist arglist-d-1)
                                   (unsafe:make-config-triv 0))
                (unsafe:make-behav (mk-trace (list))
                          0
                          (unsafe:printf-lang (cons (32 (bv 0)) nil))))
  )

  (test-case "%0$d"
  ; printf("%0$d")
  (check-equal? (unsafe:interp-fmt fmt-d-1
                                   (compile-arglist arglist-0)
                                   (unsafe:make-config-triv 0))
                (unsafe:make-behav-triv (mk-trace (list )) 0))
  )

  )
(run-tests unsafe-correct)


(define/provide-test-suite safe-unsafe-consistent
  (check-safe-unsafe-consistent fmt-d-1
                                arglist-d-1
                                (safe:make-config-triv 0))
  (check-safe-unsafe-consistent fmt-s-1
                                arglist-s-1
                                (safe:make-config-triv 0))
  (check-safe-unsafe-consistent fmt-n-1
                                arglist-n-1
                                (safe:make-config-triv 0))
  )
(parameterize ([safe:debug? #f]
               [unsafe:debug? #f]
               )
  (run-tests safe-unsafe-consistent)
  )
