#lang seec
(require (prefix-in safe:
                    (file "printf-spec.rkt")))
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



; It usually makes sense to define functions in the printf grammar that take
; three arguments: a format string, an argument list, and a configuration. This
; function converts such a function into one that accepts a [printf-lang]
; program, consisting of the same parts in a different order.
#;(define/contract (printf-uncurry f)
  (-> (-> fmt? arglist? config? any)
      (-> (cons/c context? fmt?) any))
  (λ (p)
    (match p
      [(cons (printf-lang (args:arglist cfg:config)) fmt)
       (f fmt args cfg)])))



(define/contract (bv-add-integer b x)
  (-> bv? integer? bv?)
  #;(printf "(bv-add-integer ~a ~a)~n" b x)
  (bvadd b (integer->bv x))
  )

(define/contract (add-constant-spec c p res)
  (-> integer? printf-program? behavior? boolean?)
  #;(printf "(add-constant-spec ~a ~a ~a)~n" c p res)
  (let* ([acc (conf->acc (program->config p))]
         [acc+ (conf->acc (behavior->config res))]
         )
    #;(printf "add-constant-spec: acc: ~a~n" acc)
    #;(printf "add-constant-spec: acc+: ~a~n" acc+)
    #;(printf "add-constant-spec: acc+c: ~a~n" (bv-add-integer acc c))
    (equal? acc+ (bv-add-integer acc c))
    ))
(define/contract (safe:add-constant-spec c p res)
  (-> integer? safe:printf-program? safe:behavior? boolean?)
  #;(printf "(add-constant-spec ~a ~a ~a)~n" c p res)
  (let* ([acc  (safe:conf->acc (safe:program->config p))]
         [acc+ (safe:conf->acc (safe:behavior->config res))]
         )
    (equal? acc+ (+ acc c))
    ))


(define (symbolic? e)
  (not (equal? (symbolics e) (list ))))


(define (find-increment-gadget)
  (define g (find-gadget safe:printf-spec
                         ((curry safe:add-constant-spec) 1)
                         #;(λ (input-program result-behavior)
                           (let* ([acc-before (conf->acc (program->config input-program))]
                                  [acc-after  (conf->acc (behavior->config result-behavior))])
                             (= acc-after (+ 1 acc-before))))
;                         #:count 3
                         ))
  (display-gadget g displayln)
  )
#;(find-increment-gadget)



(define (find-add-constant-gadget c)

  (define g (find-gadget printf-impl
                         ((curry add-constant-spec) c)
                         #:expr-bound 5
                         #:context-bound 3
                         ; NOTE: will not find gadget without this context-constraint. WHY????
                         #:context-constraint (λ (ctx) (match (context->arglist ctx)
                                                         [(printf-lang (cons "" arglist)) #t]
                                                         [_ #f]))
                         ))
  (display-gadget g displayln)
  )
#;(find-add-constant-gadget -1)
; -1 == 16383

(define (find-add-argument-gadget)

  (printf "Attempting to synthesize an add-argument gadget~n~n")

  (define/contract f-concrete safe:fmt?
    (printf-lang (cons (% ((1 $) ((* 0) s))) nil)))
  (define/contract f-bad safe:fmt?
    (printf-lang (cons (% ((0 $) (1 d)))
                 (cons (% ((0 $) ((* 0) d))) nil))))
  (define/contract f-bad-2 safe:fmt?
    (printf-lang (cons (% ((1 $) (16383 d)))
                 (cons (% ((0 $) (NONE d))) nil))))

  (define/contract (args-concrete y-val) (-> integer? arglist?)
    (printf-lang (cons ,(integer->bv y-val) (cons "" nil))))
  (define/contract (args-bad y-val) (-> integer? arglist?)
    (printf-lang (cons ,(integer->bv y-val)
                 (cons ,(integer->bv y-val) nil))))
  (define/contract (args-bad-2 y-val) (-> integer? arglist?)
    (printf-lang (cons ,(integer->bv y-val)
                 (cons (* ,(integer->bv 0))
                 nil))))

  (define/contract (context-concrete y-val)
    (-> integer? context?)
    (printf-lang (,(args-concrete y-val)
                  ((bv 0) nil))))


  (define/contract (arglist-constraint ctx idx y-val)
    (-> context? integer? integer? boolean?)
    #;(begin
      (define m (conf->mem (context->config ctx)))
      (define y-bv (integer->bv y-val))
      (define (constraint args)
        (match args
          [(printf-lang nil) #f]
          [(printf-lang (cons e:expr args+:arglist))
           (or (equal? (eval-expr e m) y-bv)
               (constraint args+)
               )]
          ))
      (define res (constraint (context->arglist ctx)))
      res
      )
    (equal? (lookup-offset idx ctx)
            (printf-lang ,(integer->bv y-val)))
    )

  #;(parameterize ([debug? #t])
    (interp-fmt f-concrete
                       (args-concrete 3)
                       (printf-lang ((bv 0) nil))))

  (define-symbolic x-val integer?)
  (define-symbolic acc-val integer?)

  (define args-symbolic (printf-lang arglist 4))
  (define context-symbolic
    (printf-lang (,args-symbolic
                  (,(integer->bv acc-val)
                   nil))))

  ; One of the biggest problems is that we will sometimes synthesize a bogus
  ; answer, like e.g. %0$d... ??? maybe it still has to do with bitvectors??
  (display-gadget
   (find-gadget printf-impl
                       ((curry add-constant-spec) x-val)
;                       #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
;                                                                    (program->context p)))
                       ; This valid constraint is not *necessarily* good for printf-impl
                       #:expr-bound 6
;                       #:expr-constraint (λ (e) (equal? e f-concrete))
                       #:context-bound 4 ; must be at least 4
                       #:context (context-concrete x-val) ;context-symbolic
                       #:context-constraint (λ (ctx)
                                              (and (arglist-constraint ctx 0 x-val)
                                                   ; NOTE: no symbolic variables
                                                   ; (like a symbolic index)
                                                   ; should appear in these
                                                   ; constraints. ALSO: we don't
                                                   ; want to quantify over the
                                                   ; entire context, since we
                                                   ; want to figure out what x
                                                   ; and s should be!
                                                   (equal? ctx (context-concrete x-val))
                                                   ))
                       #:fresh-witness #f
                       #:debug #f
                       #:forall (list x-val acc-val)
                       )
   displayln)
  (displayln "Done")
  )
#;(find-add-argument-gadget)
; NOTE: still doesn't work for context-symbolic...


(define (find-load-gadget)

  (define/contract f-concrete safe:fmt?
    (printf-lang (cons (% ((0 $) ((* 1) s))) nil)))
  (define args+ (printf-lang arglist 2))
  (define/contract (args-concrete l) (-> ident? arglist?)
    (printf-lang (cons "" (cons (* (LOC ,l)) nil #;,args+))))
  (define m+ (printf-lang mem 2))
  (define/contract (mem-concrete l y-val)
    (-> ident? integer? mem?)
    (printf-lang (cons (,l ,(integer->bv y-val)) ,m+)))

    
  (define/contract (context-concrete l y-val acc-val)
    (-> ident? integer? integer? context?)
    (printf-lang (,(args-concrete l)
                  (,(integer->bv acc-val)
                   ,(mem-concrete l y-val)
                   ))))

  #;(parameterize ([debug? #t])
    (define res (interp-fmt-unsafe f-concrete (args-concrete 128) (printf-lang ((bv 0) nil))))
    (define spec (add-constant-spec 128 (make-program f-concrete (args-concrete 128)
                                                 (printf-lang ((bv 0) nil)))
                                    res))
    (printf "spec: ~a~n" spec)
    )

  (define-symbolic x-val integer?)
  (define-symbolic acc-val integer?)
  (define-symbolic l-val integer?)
  (define/contract l ident? (printf-lang ,l-val))

  #;(define l-val (printf-lang ident 1))
  (display-gadget
   (find-gadget printf-impl
                       ((curry add-constant-spec) x-val)
                       #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
                                                                    (program->context p)))
                       #:expr-bound 6
;                       #:expr f-concrete
;                       #:expr-constraint (λ (f) (equal? f f-concrete))
                       #:context-bound 6
                       ; NOTE: I found it easier to provide this "concrete"
                       ;   context with symbolic variables in it, than to
                       ;   provide a completely symbolic context and constrain
                       ;   it. Not only did the completely symbolic version take
                       ;   multiple minutes as opposed to less than 1 minute,
                       ;   but it provided a bogus answer. Debugging this would
                       ;   be useful, but in the meantime providing sketches is
                       ;   a reasonable compromise.
                       #:context (context-concrete l x-val acc-val)
                       #:fresh-witness #f
                       #:forall (list l-val x-val acc-val)
                       )
   displayln)
  )
#;(time (find-load-gadget))


(define (find-add-mem-gadget)

  (define/contract f-concrete safe:fmt?
    (printf-lang (cons (% ((3 $) ((* 0) s))) ; first  add value1 to the accumulator
                 (cons (% ((3 $) ((* 1) s))) ; second add value2 to the accumulator
                 (cons (% ((2 $) (NONE n)))  ; then write the result to the target location
                       nil)))))
  (define/contract (args-structure l1 l2 l3 args+)
    (-> ident? ident? ident? arglist? arglist?)
    (printf-lang (cons (* (LOC ,l1))
                 (cons (* (LOC ,l2))
                 (cons (LOC ,l3)
                 ,args+)))))
  (define/contract (mem-structure l1 x1 l2 x2 m+)
    (-> ident? integer? ident? integer? mem? mem?)
    (printf-lang (cons (,l1 ,(integer->bv x1))
                 (cons (,l2 ,(integer->bv x2))
                 ,m+))))

  (define (add-mem-spec l1 l2 l3 p b)
      ; 1. look up the bitvector value of l1 in the memory of p
      ; 2. look up the bitvector value of l2 in the memory of p
      ; 3. look up the bitvector value of l3 in the memory of b
      ; 4. check if l3 = l1+l2
    (let* ([cfg (context->config (program->context p))]
           [m   (conf->mem cfg)]
           [m+  (conf->mem (behavior->config b))])
      (match (list (lookup-loc l1 m)
                   (lookup-loc l2 m)
                   (lookup-loc l3 m+))
        [(list (printf-lang x1:bitvector)
               (printf-lang x2:bitvector)
               (printf-lang x3:bitvector))
         (equal? x3 (bvadd x1 x2))]
        )))


  
  #;(parameterize ([debug? #t])
    (define l1-concrete (bonsai-integer 1))
    (define l2-concrete (bonsai-integer 2))
    (define l3-concrete (bonsai-integer 3))
    (define conf (printf-lang ((bv 0) ,(mem-structure l1-concrete 1 l2-concrete 2 (printf-lang nil)))))
    ; the result should be (bv 3)
    (define res (interp-fmt f-concrete
                                   (args-structure l1-concrete l2-concrete l3-concrete
                                                   (printf-lang (cons "" nil)))
                                   conf))
    (define spec (add-mem-spec l1-concrete l2-concrete l3-concrete
                               (make-program f-concrete
                                             (args-structure l1-concrete l2-concrete l3-concrete
                                                   (printf-lang (cons "" nil)))
                                             conf)
                               res))
    (printf "spec: ~a~n" spec)
    )

  (define-symbolic l1-val integer?)
  (define-symbolic l2-val integer?)
  (define-symbolic l3-val integer?)
  (define l1 (printf-lang ,l1-val)) ; Note: when I made l1, l2, and l3 purely
                                      ; symbolic and quantified over them, I got
                                      ; bogus answers
  (define l2 (printf-lang ,l2-val))
  (define l3 (printf-lang ,l3-val))
  (define-symbolic x1-val integer?)
  (define-symbolic x2-val integer?)
  #;(define-symbolic z-val integer?)

  (define args-symbolic
    (printf-lang (cons (* (LOC ,l1))
                 (cons (* (LOC ,l2))
                 (cons (LOC ,l3)
                 ,(printf-lang arglist 2))))))
  (define mem-symbolic
    (printf-lang (cons (,l1 ,(integer->bv x1-val))
                 (cons (,l2 ,(integer->bv x2-val))
                 ,(printf-lang mem 1)))))

  (define context-structure
    (printf-lang (,args-symbolic ; arglist
                  ((bv 0) ; we will start with bv 0 here
                   ,mem-symbolic))))


  (define sol (find-gadget printf-impl
                       (λ (p b) (add-mem-spec l1 l2 l3 p b))
                       #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
                                                                    (program->context p)))
                       #:expr-bound 7
                       #:context context-structure
                       ; NOTE: SEEC is not very good at synthesizing maps based
                       ; on specifications of their contexts... e.g. on what lookup-loc does
                       #:fresh-witness #f
                       #:forall (list l1-val l2-val l3-val x1-val x2-val)
                       ))
    (display-gadget sol displayln)
  )
#;(time (find-add-mem-gadget))
; NOTE: Z3 currently takes a long time with this case, perhaps needs debugging


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Weird machine primitives ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (find-add-a-c)
  ; Increment by a constant
  ;
  ; Increment the accumulator by a constant value N
  ;
  ; result of (find-add-constant-gadget N) while quantifying over N

  #;(define/contract f-concrete
    safe:fmt?
    (printf-lang (cons (% ((1 $) ((* 0) s))) nil)))
  #;(define f-result
    (printf-lang (cons (% ((1 $) ((* 0) s)))
                 (cons (% ((1 $) (7424 s)))
                 nil))))

  (define-symbolic N integer?)

  (define-symbolic acc-val integer?) ; initial accumulator
  (define/contract ctx-sketch
    context?
    (printf-lang ((cons ,(integer->bv N) (cons "" nil)) ; arglist
                  (,(integer->bv acc-val) nil))))       ; config

  (define g (find-gadget printf-impl
                         ((curry add-constant-spec) N)
                         #:expr-bound 6
                         #:context ctx-sketch
                         #:forall (list N acc-val)
                         ))
  (display-gadget g displayln)
  )
#;(find-add-a-c)
;
; Result:
;
; Expression ((% ((1 $) ((* 0) s))))
; is a gadget for the provided specification, as witnessed by behavior (((bv #x00 8) ((0 ""))))
; in context (((bv #x00 8) ((0 ""))))

; Return a pair of a format string and an argument list
(define (add-c N)
  (define add-c-fmt (printf-lang (cons (% ((1 $) ((* 0) s)))
                                 nil)))

  (define add-c-args (printf-lang (cons ,(integer->bv N) (cons "" nil))))

  (cons add-c-fmt add-c-args)
  )



(define/contract (lookup-in-mem-spec l x p res)
  (-> ident? integer? printf-program? behavior? boolean?)
  (let* ([m (conf->mem (behavior->config res))])
    (match (lookup-loc l m)
      [(printf-lang v:bitvector) (equal? v (integer->bv x))]
      [_ #f])))

(define (find-store-a)
  ; Indirect write
  ;
  ; Write the current accumulator to the location in memory pointed to by p, a
  ; stack-allocated pointer


  (define concrete-fmt (printf-lang (cons (% ((0 $) (NONE n)))
                                     nil)))

  (define-symbolic ptr integer?)
  (define-symbolic acc-val integer?)

  (define/contract ctx-sketch
    context?
    (printf-lang ((cons (LOC ,ptr) nil)            ; arglist
                  (,(integer->bv acc-val) nil))))  ; config

  (define g (find-gadget printf-impl
                         ((curry lookup-in-mem-spec) ptr acc-val)
                         #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
                                                                      (program->context p)))
                         #:expr-bound 6
                         #:context ctx-sketch
                         #:fresh-witness #f
                         #:forall (list ptr acc-val)))
  (display-gadget g displayln)
  )
#;(find-store-a)
;
; Result:
; Expression ("" ((% ((0 $) (NONE n)))))
; is a gadget for the provided specification, as witnessed by behavior (("") ((bv #x00 8) ((0 (bv #x00 8)))))
; in context (((LOC 0)) ((bv #x00 8)))

; Return a pair of a format string and an argument list
(define (store-a ptr)
  (define store-a-fmt (printf-lang (cons ""
                                   (cons (% ((0 $) (NONE n)))
                                   nil))))

  (define store-a-args (printf-lang (cons (LOC ,ptr) nil)))

  (cons store-a-fmt store-a-args)
  )

(define (find-add-a-len)
  ; Indirect length read
  ;
  ; Add the length of a string to the accumulator

  (define/contract concrete-fmt
    safe:fmt?
    (printf-lang (cons (% ((0 $) (NONE s))) nil)))

  (define-symbolic str-len integer?)
  (assert (<= 0 str-len (max-str-len)))
  (define str (printf-lang string (max-str-len)))
  (assert (equal? (string-length str) str-len))

  (define-symbolic acc-val integer?)

  (define/contract ctx-sketch
    context?
    (printf-lang ((cons ,str nil)                  ; arglist
                  (,(integer->bv acc-val) nil))))  ; config

  (define g (find-gadget printf-impl
                         (λ (p res) (add-constant-spec str-len p res))
                         #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
                                                                      (program->context p)))
                         #:expr-bound 6
                         #:context ctx-sketch
                         #:forall (list str-len str acc-val)
                         ))
  (display-gadget g displayln)
  )
#;(find-add-a-len)
;
; Result:
; Expression ("" ((% ((0 $) (NONE s)))))
; is a gadget for the provided specification, as witnessed by behavior (("" ("   ")) ((bv #x03 8)))
; in context (("   " ((bv #x00 8) ("@"))) ((bv #x00 8)))

; Return a pair of a format string and an argument list
(define/contract (add-a-len s)
  (-> string? (cons/c safe:fmt? arglist?))
  (define store-a-fmt (printf-lang (cons ""
                                   (cons (% ((0 $) (NONE s)))
                                   nil))))

  (define store-a-args (printf-lang (cons ,s nil)))

  (cons store-a-fmt store-a-args)
  )


(define (find-add-a)
  ; Direct read
  ;
  ; Add a value to the accumulator

  (define/contract concrete-fmt
    safe:fmt?
    (printf-lang (cons (% ((1 $) ((* 0) s))) nil)))

  (define-symbolic x-val integer?)
  (define-symbolic acc-val integer?)

  (define/contract ctx-sketch
    context?
    (printf-lang ((cons ,(integer->bv x-val) (cons "" nil)) ; arglist
                  (,(integer->bv acc-val) nil))))  ; config

  (define g (find-gadget printf-impl
                         (λ (p res) (add-constant-spec x-val p res))
                         #:valid (λ (p) (fmt-consistent-with-arglist? (program->fmt p)
                                                                      (program->context p)))
                         #:expr-bound 6
                         #:context ctx-sketch
                         #:forall (list x-val acc-val)
                         ))
  (display-gadget g displayln)
  )
#;(find-add-a)
;
; Result:
; Expression ((% ((1 $) ((* 0) s))))
; is a gadget for the provided specification, as witnessed by behavior (("@@") ((bv #x02 8) ((17762 " "))))
; in context (((bv #x00 8) ("@@" (" "))) ((bv #x00 8) ((17762 " "))))

; Return a pair of a format string and an argument list
(define/contract (add-a x)

  ; Note: to make add-a more abstract, we could require that it provide both a
  ; concrete offset of the empty string, AND the concrete offset of x on the
  ; stack
  ;
  ; Or we could synthesize all these gadgets with respect to a global argument
  ; list/stack layout... e.g. given a particular stack layout, what format
  ; strings will we need for each call?

  (-> integer? (cons/c safe:fmt? arglist?))

  (define store-a-fmt (printf-lang (cons (% ((1 $) ((* 0) s)))
                                   (cons ""
                                   nil))))

  (define store-a-args (printf-lang (cons ,(integer->bv x) nil)))

  (cons store-a-fmt store-a-args)
  )

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
    (define-symbolic* symbolic-offset integer?)
    (assert (>= symbolic-offset 0))

    #;(define (symbolic-width) (printf-lang NONE))
    (define (symbolic-width)
      (define-symbolic* symbolic-nat integer?)
      (assert (>= symbolic-nat 0))
      (cond
        [(havoc!) (printf-lang NONE)]
        [(havoc!) (printf-lang (* ,symbolic-nat))]
        [else     (printf-lang ,symbolic-nat)]
        ))
    #;(define (symbolic-fmt-type) (printf-lang s))
    (define (symbolic-fmt-type)
      (cond
        [(havoc!) (printf-lang s)]
        [(havoc!) (printf-lang d)]
        [else     (printf-lang n)]
        ))

    (cond
      [(havoc!) (new-symbolic-string n)]
      [else     (printf-lang (% ((,symbolic-offset $) (,(symbolic-width) ,(symbolic-fmt-type)))))]
      ))
(define/contract (fmt-sketch n) (-> exact-nonnegative-integer? safe:fmt?)
    ; Using a list of length 5 of (printf-lang fmt-elt 5) took over 40 min for
    ; find-COMPL and never completed synthesis. Trying with fmt-elt-sketch.
    (list->seec (for/list ([_ n]) (fmt-elt-sketch n)))
    )
; This invariant should be maintained both before and after gadgets
(define (wf-acc-spec cfg)
    (-> config? boolean?)
    (bvzero? (lsb (conf->acc cfg))))

(define (COMPL-spec IN OUT prog behav)
    #;(printf "acc before: ~a~n" (conf->acc (program->config prog)))
    #;(printf "acc after: ~a~n" (conf->acc (behavior->config behav)))
    (equal? (ptr->bool IN (program->config prog))
            (not (ptr->bool OUT (behavior->config behav)))))


(define (find-COMPL) ; INPUT: p is a pointer to a bitvector encoding a boolean

  (define neg1 (bitvector->natural (integer->bv -1)))
  (define/contract fmt-concrete safe:fmt?
    (printf-lang (cons (% ((2 $) ((* 1) s))) ; add (* (LOC ,IN)) to the accumulator
                 (cons (% ((2 $) (,neg1 s))) ; add -1 to the accumulator
                 (cons (% ((0 $) (NONE  n))) ; write the value of the accumulator to OUT
                 (cons (% ((2 $) ((* 1) s))) ; reverse steps 1 and 2 to reset the accumulator
                 (cons (% ((2 $) (,neg1 s)))
                 nil)))))))

  (define-symbolic IN   integer?)
  (define-symbolic OUT  integer?)
  (assert (not (equal? IN OUT))) ; It would be ok for these to be equal if we
                                 ; could read OUT back into the accumulator, but
                                 ; since we re-read IN, we can't have
                                 ; overwritten it.

  (define-symbolic b-val integer?)
  (define b (integer->bv b-val))

  (define-symbolic acc-val integer?)

  (define/contract args-sketch arglist?
    (printf-lang (cons (LOC ,OUT)
                 (cons (* (LOC ,IN))
                 (cons ""
                 nil)))))
  (define/contract config-sketch config?
    (printf-lang (,(integer->bv acc-val)
                  (cons (,IN ,b) nil))))
  (define/contract context-sketch context?
    (printf-lang (,args-sketch ,config-sketch)))


  (define g (find-gadget printf-impl
                         (λ (prog behav) (and (COMPL-spec IN OUT prog behav)
                                              (wf-acc-spec (behavior->config behav))))
                         #:expr (fmt-sketch 5)
;                         #:expr-constraint (λ (f) (equal? f fmt-concrete))
                         #:context context-sketch
                         #:context-constraint (λ (ctx) (wf-acc-spec (context->config ctx)))
                         #:forall (list acc-val IN OUT b-val)
                         ))
  (display-gadget g displayln)
  )
(time (find-COMPL))
; Result:
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


(define (COMPL IN OUT)
  (-> ident? ident? (cons/c safe:fmt? arglist?))

  (assert (not (equal? IN OUT)))

  (define COMPL-fmt (list->seec (list (printf-lang (% ((2 $) ((* 1) s))))
                                      (printf-lang (% ((2 $) (3 d))))
                                      (printf-lang (% ((0 $) (1 n)))) ; the padding on %n is ignored
                                      (printf-lang "?w?_w")
                                      (printf-lang (% ((2 $) ((* 1) s))))
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
    (list->seec (list (printf-lang (% ((3 $) ((* 1) s)))) ; Add in1 to accumulator
                      (printf-lang (% ((3 $) ((* 2) s)))) ; Add in2 to accumulator
                      (printf-lang (% ((0 $) (NONE n))))  ; Write result to OUT
                      (printf-lang (% ((3 $) ((* 1) s)))) ; Uncompute the result
                      (printf-lang (% ((3 $) ((* 2) s)))) ; 
                      )))

  (define g (find-gadget printf-impl
                         (λ (prog behav) (and (XOR-spec IN1 IN2 OUT prog behav)
                                              (wf-acc-spec (behavior->config behav))))
;                         #:expr fmt-concrete
                         #:expr (fmt-sketch 5)
                         #:context context-sketch
                         #:context-constraint (λ (ctx) (wf-acc-spec (context->config ctx)))
                         #:forall (list acc-val IN1 IN2 OUT in1 in2)
                         ))
  (display-gadget g displayln)

  )
#;(time (find-XOR))
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
(define (XOR IN1 IN2 OUT)
  (-> ident? ident? ident? (cons/c safe:fmt? arglist?))

  (assert (not (equal? IN1 OUT)))
  (assert (not (equal? IN2 OUT)))

  (define XOR-fmt (list->seec (list (printf-lang (% ((3 $) ((* 1) s)))) ; add in1 to accumulator
                                    (printf-lang (% ((3 $) ((* 2) s)))) ; add in2 to accumulator
                                    (printf-lang (% ((0 $) (2 n))))     ; write result to OUT...
                                                                        ; the padding on %n is ignored
                                    (printf-lang (% ((3 $) ((* 2) s)))) ; repeat steps 1 and 2 to reset
                                    (printf-lang (% ((3 $) ((* 1) s)))) ; the accumulator
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
