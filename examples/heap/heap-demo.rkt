#lang seec
(set-bitwidth 4)
(require (file "heap.rkt"))

; This file provides some details on how we expect someone to interact with their model through SEEC in order to find bugs and refine their model and implementation.
;0: easy way to see double free bug:
(define (test-0)
  (begin
    (define s2* (heap-model state 6))
    (assert (valid-state 3 s2*))
    (define a2* (heap-model action 4))
    (define s2+* (interpret-action a2* s2*))
;    (assert (heap-model-valid-interaction i2* s2*))
;    (assert (heap-model-safe-interaction i2* s2*))
    (define sol (solve (assert (not (valid-state 3 s2+*)))))
    (define s2 (concretize s2* sol))
    (define a2 (concretize a2* sol))
    (define s2+ (concretize s2+* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s2)
    (displayln "action a2")
    (displayln a2)
    (displayln "State+:")
    (display-state s2+)
    (displayln (valid-state 3 s2+))))




; 1: we start with a concrete state, and try to find some interaction which results in an invalid state
(define (test-1)
  (begin
    (define s2* d+4*)
    (define i2* (heap-model interaction 4))
    (define s2+* (interpret-interaction i2* s2*))
    (define sol (solve (assert (not (valid-state 3 s2+*)))))
    (define s2 (concretize s2* sol))
    (define i2 (concretize i2* sol))
    (define s2+ (concretize s2+* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s2)
    (displayln "Interaction:")
    (displayln i2)
    (displayln (heap-model-safe-interaction i2 s2))
    (displayln (heap-model-valid-interaction i2 s2))
    (displayln "State+:")
    (display-state s2+)
    (displayln (valid-state 3 s2+))))

; Found "Interaction: ((set 0 2) ((write 0 0)))",
; This breaks the backward pointer of the freelist. We can modify write to only affect allocated blocks:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (valid-write loc h)
  ; compute the location of the "allocated" bit
  (let* ([loc-v (- (+ loc 3) (remainder loc 4))]
         [v-bit (nth loc-v h)])
    (if (equal? v-bit (heap-model 1))
        #t
        #f)))

(define (interpret-action+ a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     (match a
       [(heap-model (write bl:buf-loc bhl:buf-loc))
        (let* ([val (nth b bl)] ; get the value from the buffer
               [hl (nth b bhl)] ; get the pointer from the buffer
               [loc (heap-loc-addr hl)] ; compute the address in the heap          
               [h+ (write h loc val)]) ; overwrite the location in the heap with the value
          (if (valid-write loc h)
              (heap-model (,b ,h+ ,f))
              (assert #f)))]
       [_ (interpret-action a s)])]))

(define (interpret-interaction+ i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction+ i+ (interpret-action+ a s))]
    [(heap-model nil)
     s]))


; 2: repeat test-1, but with the restriction on writes
(define (test-2)
  (begin
    (define s2* d+4*)
    (define i2* (heap-model interaction 4))
    (define s2+* (interpret-interaction+ i2* s2*))
    (define sol (solve (assert (not (valid-state 3 s2+*)))))
    (define s2 (concretize s2* sol))
    (define i2 (concretize i2* sol))
    (define s2+ (concretize s2+* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s2)
    (displayln "Interaction:")
    (displayln i2)
    (displayln (heap-model-safe-interaction i2 s2))
    (displayln (heap-model-valid-interaction i2 s2))
    (displayln "State+:")
    (display-state s2+)
    (displayln (valid-state 3 s2+))))

; Found interaction: ((set 2 1) ((free 2)))
; Which is a double free (we are freeing the first block). We can prevent this by checking the allocated bit on "free" as well

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (valid-free loc h)
  ; compute the location of the "allocated" bit
  (let* ([loc-v (- (+ loc 3) (remainder loc 4))]
         [v-bit (nth loc-v h)])
    (if (equal? v-bit (heap-model 1))
        #t
        #f)))


(define (interpret-action++ a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     (match a
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)]
               [b+ (replace b bl (heap-model null))]
               [h+ (interpret-free h f p)])
          (if (valid-free p h)
              (heap-model (,b+ ,h+ ,p))
              (assert #f)))]
       [_ (interpret-action+ a s)])]))

(define (interpret-interaction++ i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (interpret-interaction++ i+ (interpret-action++ a s))]
    [(heap-model nil)
     s]))

(define (test-3)
  (begin
    (define s2* d+3)
    (define i2* (heap-model interaction 4))
    (define s2+* (interpret-interaction++ i2* s2*))
    (define sol (solve (assert (not (valid-state 3 s2+*)))))
    (define s2 (concretize s2* sol))
    (define i2 (concretize i2* sol))
    (define s2+ (concretize s2+* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s2)
    (displayln "Interaction:")
    (displayln i2)
    (displayln (heap-model-safe-interaction i2 s2))
    (displayln (heap-model-valid-interaction i2 s2))
    (displayln "State+:")
    (display-state s2+)
    (displayln (valid-state 3 s2+))))
