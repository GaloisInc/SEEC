#lang seec

(require seec/private/string)
(require (only-in racket/base integer->char))
(require seec/private/bonsai2)
(require racket/math)

; Integers don't handle overflow well, even when current-bitwidth is finite
(define (overflow-tests-int)
  (current-bitwidth 2)
  (define-symbolic x integer?)
  (define sol (solve (assert #;(and (= x 0) (= x 4)) (equal? x (+ x 4)))))
  sol
  )
#;(overflow-tests-int)


; Experiments with bitvectors and overflow
(define (overflow-tests)

  ; I want bitvectors whose width is `current-bitwidth-1`.
  (current-bitwidth 32)
  (define (current-bv-width) (- (current-bitwidth) 1))
  (define bvw? (bitvector (current-bv-width)))
  (define (bvw n) (bv n (current-bv-width)))
  ; in integer->bvw, n *may* be symbolic; see integer->bitvector
  (define (integer->bvw n) (integer->bitvector n bvw?))

  #;(define b (bvw 2))
  #;(printf "(bitvector->integer ~a) ==> ~a~n" b (bitvector->integer b))


  (define-symbolic x bvw?)
  #;(define x (bvw 0))
  (define-symbolic n integer?)
  (assert (>= n 0))
  (define y (integer->bvw n))
  #;(define-symbolic y bvw?)

  (define sol (synthesize #:forall x
                          #:guarantee (assert (equal? (bvadd x y) (bvsub1 x)))))
  #;(define sol (solve (assert (equal? (bvadd x y) (bvsub1 x)))))
  (if (unsat? sol)
      (displayln "Synthesis failed")
      (begin (displayln "Synthesis succeeded")
             (define x-concrete (concretize x sol))
             (displayln "x...")
             (displayln x-concrete)
             ;; (define n-concrete (concretize n sol))
             ;; (displayln "n...")
             ;; (displayln n-concrete)
             (define y-concrete (concretize y sol))
             (displayln "y...")
             (displayln y-concrete)
             (define n-concrete (concretize n sol))
             (displayln "n...")
             (displayln n-concrete)

             (displayln "x+y...")
             (displayln (bvadd x-concrete y-concrete))
             (displayln "x-1")
             (displayln (bvsub1 x-concrete))
             ))
  )
(overflow-tests)

