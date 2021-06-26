#lang seec
(require (prefix-in safe:
                    (file "printf-spec.rkt"))
         (only-in (file "printf-spec.rkt") %))
(require (file "printf-impl.rkt")) ; unsafe does not have a prefix for now
(require racket/contract)
(require seec/private/framework)

(require rosette/lib/value-browser) ; debugging

(require (only-in racket/base
                  for/list
                  exact-nonnegative-integer?
                  raise-argument-error
                  raise-arguments-error
                  parameterize))


(set-bitwidth 16 8)
;; Utilities

(define/contract (bv->bool b)
  (-> bv? boolean?)
  #;(not (bvzero? (lsb b)))
  (not (equal? (lsb b) (bv 0 1)))
  )
(define (ptr->bool p conf)
  (let* ([m (conf->mem conf)])
    (match (lookup-loc p m)
      [(printf-lang b:bitvector)
       #;(printf "(ptr->bool ~a -): ~a~n" p b)
       (bv->bool b)]
      )))

; This format sketch bounds the length of the format string, which helps with
; symbolic evaluation size
(define/contract (fmt-elt-sketch n) (-> integer? safe:fmt-elt?)
    (define (fresh-nat)
      (define-symbolic* symbolic-nat integer?)
      (assert (>= symbolic-nat 0))
      symbolic-nat
      )

    (define (symbolic-width)
      (cond
        [(havoc!) (printf-lang NONE)]
        [(havoc!) (printf-lang (* ,(fresh-nat)))]
        [else     (printf-lang ,(fresh-nat))]
        ))
    #;(define (symbolic-fmt-type) (printf-lang s))
    (define (symbolic-fmt-type)
      (cond
        [(havoc!) (printf-lang %s)]
        [(havoc!) (printf-lang %d)]
        [else     (printf-lang %n)]
        ))

    (cond
      [(havoc!) (new-symbolic-string* n)]
      [else     (printf-lang (,(symbolic-fmt-type)
                              (,(fresh-nat) ,(symbolic-width))))]
      ))
(define/contract (fmt-sketch n) (-> exact-nonnegative-integer? safe:fmt?)
    ; Using a list of length 5 of (printf-lang fmt-elt 5) took over 40 min for
    ; find-COMPL and never completed synthesis. Trying with fmt-elt-sketch.
    (list->seec (for/list ([_ n]) (fmt-elt-sketch n)))
    )

;;;;;;;;;;;;;;;;
;; INVARIANTS ;;
;;;;;;;;;;;;;;;;

; This invariant should be maintained both before and after gadgets
(define (wf-acc-spec cfg)
  (-> config? boolean?)
  (bvzero? (lsb (conf->acc cfg))))

(define (COMPL-spec IN OUT prog behav)
    #;(printf "acc before: ~a = ~a~n" (conf->acc (program->config prog))
            (ptr->bool IN (program->config prog)))
    #;(printf "acc after: ~a = ~a~n" (conf->acc (behavior->config behav))
            (ptr->bool OUT (behavior->config behav)))
    (equal? (ptr->bool IN (program->config prog))
            (not (ptr->bool OUT (behavior->config behav)))))


(define (find-COMPL) ; INPUT: p is a pointer to a bitvector encoding a boolean

  (define neg1 (bitvector->natural (integer->bv -1)))
  (define/contract fmt-concrete safe:fmt?
    (list->seec (list (% 0 $ 1 * s)  ; add (* (LOC ,IN)) to the accumulator
                      (% 0 $ neg1 s) ; add -1 to the accumulator
                      (% 2 $ n)      ; write the value of the accumulator to OUT
                      (% 0 $ 1 * s)  ; reverse steps 1 and 2 to reset the accumulator
                      (% 0 $ neg1 s)
                      )))
  (define/contract fmt-concrete-noncomposable safe:fmt?
    (list->seec (list (% 0 $ 1 * s)  ; add (* (LOC ,IN)) to the accumulator
                      (% 0 $ neg1 s) ; add -1 to the accumulator
                      (% 2 $ n)      ; write the value of the accumulator to OUT
                      )))
  (define/contract fmt-concrete-shorter safe:fmt?
    (list->seec (list (% 0 $ 1 * s)  ; add (* (LOC ,IN)) to the accumulator
                      (% 0 $ neg1 s) ; add -1 to the accumulator
                      (% 3 $ n)      ; write the value of the accumulator to OUT
                      (% 0 $ 2 * s)  ; reverse steps 1 and 2 to reset the accumulator
                      )))
  ; Use with args-sketch-long, using OUT as scratch space first
  (define/contract fmt-concrete-reset-first safe:fmt?
    (list->seec (list (% 3 $ n)      ; write accumulator to OUT
                      (% 0 $ 3 * s)  ; add OUT to accumulator, resetting it to 0
                      (% 0 $ 1 * s)  ; add (* (LOC ,IN)) to the accumulator
                      (string "&")   ; add -1 to the accumulator
                      (% 3 $ n)      ; write the value of the accumulator to OUT
                      )))


  (define-symbolic IN   integer?)
  (define-symbolic OUT  integer?)
  (assert (not (equal? IN OUT))) ; It would be ok for these to be equal if we
                                 ; could read OUT back into the accumulator, but
                                 ; since we re-read IN, we can't have
                                 ; overwritten it.

  (define-symbolic b-val integer?)
  (define b (integer->bv b-val))

  #;(define-symbolic acc-val integer?)
  (define acc-val 0)

  (define/contract args-sketch arglist?
    (printf-lang (cons ""
                 (cons (* (LOC ,IN))
                 (cons (LOC ,OUT)
                 nil)))))
  (define/contract args-sketch-long arglist?
    (printf-lang (cons ""
                 (cons (* (LOC ,IN))
                 (cons (* (LOC ,OUT))
                 (cons (LOC ,OUT)
                 nil))))))
  (define/contract config-sketch config?
    (printf-lang (,(integer->bv acc-val)
                  (cons (,IN ,b) nil))))
  (define/contract context-sketch context?
    (printf-lang (,args-sketch ,config-sketch)))
  (define/contract context-sketch-long context?
    (printf-lang (,args-sketch-long ,config-sketch)))


  (define g (find-gadget printf-impl
                         (λ (prog behav) (and (COMPL-spec IN OUT prog behav)
                                              #;(wf-acc-spec (behavior->config behav))))
                         #:expression (fmt-sketch 5)
;                         #:expression fmt-concrete-reset-first
;                         #:expression-where (λ (f) (equal? f fmt-concrete))
                         #:context context-sketch-long
;                         #:context-where (λ (ctx) (wf-acc-spec (context->config ctx)))
                         #:context-where (λ (ctx) (not (equal? IN OUT)))
                         #:fresh-witness #f
                         #:forall (list acc-val IN OUT b-val)
                         ))
  (display-gadget g displayln)
  )
#;(time (find-COMPL))
; Result (after moving to more compact fmt-elt representation):
;
; Expression "ww__o"         ; print an odd number of characters to change the parity of acc
;            (%s (0 (* 1)))  ; add 1
;            (%n (2 24580))  ; write result to OUT (width gets ignored)
;            (%s (0 (* 1)))  ; reset accumulator by repeating steps 1-2
;            "q?@?_"
; is a gadget for the provided specification, as witnessed by behavior
;    (("ww__o" ("" ((pad-by 5) ("" ("q?@?_"))))) ((bv #x0f 8) ((0 (bv #x05 8)) ((0 (bv #x00 8))))))
; in context
;    (("" ((* (LOC 0)) ((LOC 0)))) ((bv #x00 8) ((0 (bv #x00 8)))))

;cpu time: 35306 real time: 117273 gc time: 3039
; 117273 ms ~ 2 min
;
;
;
; Before moving to more compact fmt-elt representation:
;
; Expression ((% ((2 $) (NONE d))) ; When converting a string to an integer, will print "0"
;            ((% ((2 $) ((* 1) s)))
;            ((% ((0 $) (0 n)))
;            ("?____"
;            ((% ((2 $) ((* 1) s))))))))
; is a gadget for the provided specification, as witnessed by behavior (("?____") ((bv #x05 8) ((0 (bv #x00 8)))))
; in context (((bv #x00 8)) ((bv #x00 8)))

; cpu time: 43975 real time: 330707 gc time: 3841
; 330707ms = 5.5 min
;
; With compact representation, with longer argument list, time: 2.5min. I
; thought this would be shorter than comperable short argument list (2 min)
; because the symbolic format string could be shorter (4 rather than 5), but
; they are pretty comperable or this is longer.
;
;
; Without any wf-acc-spec constraints at all:
; Expression  (% 3 $ n)      ; first reset the accumulator by writing acc to OUT...
;             (% 0 $ 2 * s)  ; ... and reading it back in, resetting it to 0
;             (% 0 $ 1 * s)  ; then add IN to accumulator
;             "/??0?"        ; negate the value
;             (% 3 $ n)      ; write result to OUT
; is a gadget for the provided specification, as witnessed by behavior
;     Trace:       ("" "" "/??O?")
;     Accumulator: (bv #x05 8
;     Memory:      ((0 (bv #x05 8)) ((0 (bv #x00 8)) ((0 (bv #x00 8)))))))
; in context 
;     Args:        ("" (* (LOC IN)) (* (LOC OUT)) (LOC OUT))
;     Accumulator: (bv #x00 8)
;     Memory:      (0 (bv #x00 8))
;
; cpu time: 29533 real time: 1071817 gc time: 2824
; 1071817 ms = 17 min


#;(define-grammar printf-decoder #:extends fmt-string
  (decoder ::= (bit natural)        ; select ith bit from the bitvector
               (and decoder decoder)
               (or decoder decoder)
               (not decoder)
               )
  )



(define (COMPL IN OUT)
  (-> ident? ident? (cons/c safe:fmt? arglist?))

  (assert (not (equal? IN OUT)))

  (define COMPL-fmt (list->seec (list (% 2 $ 1 * s) #;(printf-lang (% ((2 $) ((* 1) s))))
                                      (% 2 $ 3 d) #;(printf-lang (% ((2 $) (3 d))))
                                      (% 0 $ n) #;(printf-lang (% ((0 $) (1 n)))) ; the padding on %n is ignored
                                      (printf-lang "?w?_w")
                                      (% 2 $ 1 * s) #;(printf-lang (% ((2 $) ((* 1) s))))
                                      )))
  (define COMPL-args (list->seec (list (printf-lang (LOC ,OUT))
                                       (printf-lang (* (LOC ,IN)))
                                       (printf-lang ""))))

  (cons COMPL-fmt COMPL-args)
  )

(define (XOR-spec IN1 IN2 OUT prog behav)
    (equal? (ptr->bool OUT (behavior->config behav))
            (xor (ptr->bool IN1 (program->config prog))
                 (ptr->bool IN2 (program->config prog))
                 )))

(define (find-XOR)

  (define-symbolic IN1 IN2 OUT integer?)
  (assert (and (not (equal? OUT IN1))
               (not (equal? OUT IN2))))

  (define-symbolic in1 in2 (bitvector (get-bv-width)))
  (define-symbolic acc-val integer?)
  
  (define/contract args-sketch arglist?
    (list->seec (list (printf-lang (LOC ,OUT))
                      (printf-lang (* (LOC ,OUT)))
                      (printf-lang (* (LOC ,IN1)))
                      (printf-lang (* (LOC ,IN2)))
                      (printf-lang "")
                      )))
  (define/contract config-sketch config?
    (printf-lang (,(integer->bv acc-val)
                  (cons (,IN1 ,in1)
                  (cons (,IN2 ,in2)
                   nil)))))
  (define/contract context-sketch context?
    (printf-lang (,args-sketch ,config-sketch)))

  (define/contract fmt-concrete safe:fmt?
    (list->seec (list (% 3 $ 1 * s) ; Add in1 to accumulator
                      (% 3 $ 2 * s) ; Add in2 to accumulator
                      (% 0 $ n)     ; Write result to OUT
                      (% 3 $ 1 * s) ; Uncompute the result
                      (% 3 $ 2 * s)
                      )))

  (define g (find-gadget printf-impl
                         (λ (prog behav) (and (XOR-spec IN1 IN2 OUT prog behav)
                                              #;(wf-acc-spec (behavior->config behav))))
;                         #:expr fmt-concrete
                         #:expression (fmt-sketch 5)
                         #:context context-sketch
;                         #:context-where (λ (ctx) (wf-acc-spec (context->config ctx)))
                         #:forall (list acc-val IN1 IN2 OUT in1 in2)
                         ))
  (display-gadget g displayln)

  )
(time (find-XOR))
; Result
;
; Expression ((% ((3 $) ((* 1) s))) ; add in1 to accumulator
;            ((% ((3 $) ((* 2) s))) ; add in2 to accumulator
;            ((% ((0 $) (2 n)))     ; write result to output
;            ((% ((3 $) ((* 2) s))) ; repeat steps 1 and 2 to reset the accumulator
;            ((% ((3 $) ((* 1) s)))
;            )))))
; is a gadget for the provided specification, as witnessed by behavior (((bv #x00 8) ((0 ""))))
; in context (((bv #x00 8) ((0 ""))))


; cpu time: 58063 real time: 1470925 gc time: 4747
; 1470925 ms == 24.5 min

;
; Without wf-acc-spec constraints:
; Expression (%n (0 NONE))
;            (%s (4 (* 3)))
;            (%s (4 (* 2)))
;            (%s (4 (* 1)))
;            (%n (0 NONE))
; is a gadget for the provided specification, as witnessed by behavior (((bv #x00 8) ((0 (bv #x00 8)) ((0 (bv #x00 8))))))
; in context (((bv #x00 8)) ((bv #x00 8)))

; cpu time: 49287 real time: 19002175 gc time: 4703
; 19002175 ms = 5 hours :o
;
(define (XOR IN1 IN2 OUT)
  (-> ident? ident? ident? (cons/c safe:fmt? arglist?))

  (assert (not (equal? IN1 OUT)))
  (assert (not (equal? IN2 OUT)))

  (define XOR-fmt (list->seec (list (% 3 $ 1 * s) ; add in1 to accumulator
                                    (% 3 $ 2 * s) ; add in2 to accumulator
                                    (% 0 $ n)     ; write result to OUT...
                                                  ; the padding on %n is ignored
                                    (% 3 $ 2 * s) ; repeat steps 1 and 2 to reset
                                    (% 3 $ 1 * s) ; the accumulator
                                    )))
  (define XOR-args (list->seec (list (printf-lang (LOC ,OUT))
                                     (printf-lang (* (LOC ,IN1)))
                                     (printf-lang (* (LOC ,IN2)))
                                     (printf-lang ""))))
  (cons XOR-fmt XOR-args)
  )

(define (find-COMPL-and-XOR)
  (define-symbolic IN0 IN1 IN2 OUT integer?)
  (assert (and (not (equal? OUT IN0))
               (not (equal? OUT IN1))
               (not (equal? OUT IN2))))

  (define-symbolic in0 in1 in2 (bitvector (get-bv-width)))
  (define-symbolic acc-val integer?)
  
  (define/contract args-sketch arglist?
    (list->seec (list (printf-lang (LOC ,OUT))
                      (printf-lang (* (LOC ,IN0)))
                      (printf-lang (* (LOC ,IN1)))
                      (printf-lang (* (LOC ,IN2)))
                      (printf-lang "")
                      )))
  (define/contract config-sketch config?
    (printf-lang (,(integer->bv acc-val)
                  (cons (,IN0 ,in0)
                  (cons (,IN1 ,in1)
                  (cons (,IN2 ,in2)
                   nil))))))
  (define/contract context-sketch context?
    (printf-lang (,args-sketch ,config-sketch)))

  (define COMPL-fmt (fmt-sketch 5))
  #;(define COMPL-fmt (list->seec (list (printf-lang (% ((3 $) ((* 1) s)))) ; add IN1
                                      (printf-lang (% ((3 $) (3 d)))) ; add 3
                                      (printf-lang (% ((0 $) (1 n)))) ; the padding on %n is ignored
                                      (printf-lang "?w?_w")               ; add 3
                                      (printf-lang (% ((3 $) ((* 1) s)))) ; add IN1
                                      )))
  (define XOR-fmt   (fmt-sketch 5))
  #;(define XOR-fmt (list->seec (list (printf-lang (% ((3 $) ((* 2) s)))) ; add in1 to accumulator
                                    (printf-lang (% ((3 $) ((* 3) s)))) ; add in2 to accumulator
                                    (printf-lang (% ((0 $) (2 n))))     ; write result to OUT...
                                                                        ; the padding on %n is ignored
                                    (printf-lang (% ((3 $) ((* 3) s)))) ; repeat steps 1 and 2 to reset
                                    (printf-lang (% ((3 $) ((* 2) s)))) ; the accumulator
                                    )))


  (define COMPL-prog (make-program COMPL-fmt args-sketch config-sketch))
  (define XOR-prog   (make-program XOR-fmt   args-sketch config-sketch))

  (define COMPL-result (interp-fmt COMPL-fmt args-sketch config-sketch))
  (define XOR-result   (interp-fmt XOR-fmt args-sketch config-sketch))

  (define sol (synthesize
               #:forall (list OUT IN0 IN1 IN2 in0 in1 in2 acc-val)
               #:assume (assert (wf-acc-spec (context->config context-sketch)))
               #:guarantee
                 (assert (and (wf-acc-spec (behavior->config COMPL-result))
                              (wf-acc-spec (behavior->config XOR-result))
                              (COMPL-spec IN0 OUT COMPL-prog COMPL-result)
                              (XOR-spec IN1 IN2 OUT XOR-prog XOR-result)
                              ))))
  (if (unsat? sol)
      (displayln "Failed to synthesize")
      (begin
        (displayln "Synthesis succeeded")
        (printf "COMPL-fmt: ~a~n~n" (concretize COMPL-fmt sol))
        (printf "XOR-fmt: ~a~n~n"   (concretize XOR-fmt sol))
        ))
  )
#;(time (find-COMPL-and-XOR))
; Wanted to see if it would take more or less time to synthesize both COMPL and
; XOR together compared to synthesizing them separately.
