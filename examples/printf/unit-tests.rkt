#lang seec
(require (file "syntax.rkt"))
(require rackunit)
(require rackunit/text-ui)
(require racket/contract)
(require (only-in racket/base
                  parameterize))


(define (check-safe-unsafe-consistent f args conf)
  (check-equal? (interp-fmt-safe f args conf)
                (interp-fmt-unsafe f args conf)))

(define/contract (mk-config n m)
  (-> integer? mem? config?)
  (printf-lang (,(integer->bonsai-bv n) ,m)))
(define (mk-config-triv n)
  (mk-config n (printf-lang mnil)))
(define/contract (mk-behav t n m)
  (-> trace? integer? mem? behavior?)
  (printf-lang (,t ,(mk-config n m))))
(define (mk-behav-triv t n)
  (printf-lang (,t ,(mk-config-triv n))))

(define/contract (list->bonsai-ll l)
  (-> (listof bonsai?) bonsai-linked-list?)
  (cond
    [(empty? l) (printf-lang nil)]
    [else (ll-cons (first l) (list->bonsai-ll (rest l)))]
    ))

(define/contract (racket->constant x)
  (-> (or/c integer? string?) const?)
  (cond
    [(integer? x) (bonsai-integer x)]
    [(string? x)  (bonsai-string  x)]
    ))
(define/contract (mk-trace l)
  (-> (listof (or/c integer? string?)) trace?)
  (list->bonsai-ll (map racket->constant l)))

(set-bitwidth 64 32)

(define fmt-d-1 (ll-singleton (printf-lang (% (0 $) NONE d))))
(define fmt-s-1 (ll-singleton (printf-lang (% (0 $) NONE s))))
(define fmt-n-1 (ll-singleton (printf-lang (% (0 $) NONE n))))
(define fmt-d-n (ll-cons      (printf-lang "foo ")
                (ll-cons      (printf-lang (% (0 $) NONE d))
                (ll-singleton (printf-lang (% (1 $) NONE n))))))
(define bv-neg-1 (bitvector->natural (bonsai-bv-value (integer->bonsai-bv -1))))
(define fmt-decrement (ll-singleton (printf-lang (% (0 $) ,(bonsai-integer bv-neg-1) s))))

(define arglist-0   (printf-lang nil))
(define arglist-d-1 (ll-singleton (printf-lang (bv 32))))
(define arglist-s-1 (ll-singleton (printf-lang "hi")))
(define arglist-n-1 (ll-singleton (printf-lang (LOC 0))))
(define arglist-d-n (bonsai-ll-append arglist-d-1 arglist-n-1))
(define arglist-s-0 (ll-singleton (printf-lang "")))

(define-test-suite safe-correct
 (test-case "%0$d"
   ; printf("%0$d",32)
   (check-equal? (interp-fmt-safe fmt-d-1
                                  arglist-d-1
                                  (mk-config-triv 0))
                 (mk-behav-triv (mk-trace (list 32)) 2))
   )
 (test-case "hello world"
  ; printf("hello world")
  (check-equal? (interp-fmt-safe (ll-singleton (printf-lang "hello world"))
                                 arglist-0
                                 (mk-config-triv 0))
                (mk-behav-triv (mk-trace (list (string "hello world")))
                               11))
  )
 (test-case "%0$s"
  ; printf("%0$s","hi")
  (check-equal? (interp-fmt-safe fmt-s-1
                                 arglist-s-1
                                 (mk-config-triv 0))
                (mk-behav-triv (mk-trace (list (string "hi")))
                               2))
  )
 (test-case "%0$n"
  ; printf("%0$n",Loc 0)
  (check-equal? (interp-fmt-safe fmt-n-1
                                 arglist-n-1
                                 (mk-config-triv 0))
                (mk-behav (mk-trace (list))
                          0
                          (printf-lang (mcons 0 (bv 0) mnil))))
  )
 (test-case "%0$d"
  ; printf("%0$d") ==> ERR
  (check-equal? (interp-fmt-safe fmt-d-1
                                 arglist-0
                                 (mk-config-triv 0))
                (printf-lang ERR))
  )
 (test-case "%0$d%1$n"
  ; printf("foo %0$d%1$n",32,Loc 0)
  (parameterize ([debug? #f])
    (check-equal? (interp-fmt-safe fmt-d-n
                                   arglist-d-n
                                   (mk-config-triv 0))
                  (mk-behav (mk-trace (list (string "foo ")
                                            32))
                            6
                            (printf-lang (mcons 0 (bv 6) mnil))))
    )
  )
 (test-case "%0$Xs"
  ; printf("%0$Xs,"") ==> add X=fmt-decrement (aka -1) to the accumulator
  (check-equal? (behavior->config (interp-fmt-safe fmt-decrement
                                                   arglist-s-0
                                                   (mk-config-triv 2)))
                (mk-config-triv 1))
  )

  (test-case "add argument from memory"
    (define/contract l ident?
      (printf-lang 1))
    (define fmt (ll-singleton (printf-lang (% (0 $) (* 0) d))))
    (define args (ll-cons (printf-lang (* (LOC ,l)))
                 (ll-singleton (printf-lang ""))))
    (define/contract m mem?
      (printf-lang (mcons ,l (bv 1) mnil)))
    (define behav (interp-fmt-safe fmt
                                   args
                                   (mk-config 0 m)))
    (check-equal? (behavior->config behav)
                  (mk-config 1 m))
    )
                                                     
)
; TODO: add test cases for padding
(run-tests safe-correct)

(define-test-suite unsafe-correct

  (test-case "%0$d"
  ; printf("%0$d","hi") 
  ; note: the character h is encoded as the number 104
  (check-equal? (interp-fmt-unsafe fmt-d-1
                                   arglist-s-1
                                   (mk-config-triv 0))
                (mk-behav-triv (mk-trace (list 104)) 3))
  )

  (test-case "%0$s"
  ; printf("%0$s",32)
  ; note: 32 is the ASCII representation of the space character
  (check-equal? (interp-fmt-unsafe fmt-s-1
                                     arglist-d-1
                                     (mk-config-triv 0))
                (mk-behav-triv (mk-trace (list (string " ")))
                               1))
  )

  (test-case "%0$n"
  ; printf("%0$n,32)
  (check-equal? (interp-fmt-unsafe fmt-n-1
                                   arglist-d-1
                                   (mk-config-triv 0))
                (mk-behav (mk-trace (list))
                          0
                          (printf-lang (mcons 32 (bv 0) mnil))))
  )

  (test-case "%0$d"
  ; printf("%0$d")
  (check-equal? (interp-fmt-unsafe fmt-d-1
                                   arglist-0
                                   (mk-config-triv 0))
                (mk-behav-triv (mk-trace (list )) 0))
  )

  )
(run-tests unsafe-correct)


(define-test-suite safe-unsafe-consistent
  (check-safe-unsafe-consistent fmt-d-1
                                arglist-d-1
                                (mk-config-triv 0))
  (check-safe-unsafe-consistent fmt-s-1
                                arglist-s-1
                                (mk-config-triv 0))
  (check-safe-unsafe-consistent fmt-n-1
                                arglist-n-1
                                (mk-config-triv 0))
  )
(run-tests safe-unsafe-consistent)
