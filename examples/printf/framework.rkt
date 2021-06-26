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
                         #:expression-size 5
                         #:context-size 3
                         ; NOTE: will not find gadget without this context-where. WHY????
                         #:context-where (λ (ctx) (match (context->arglist ctx)
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
    (seec-singleton (% 1 $ 0 * s))
    #;(printf-lang (cons (% ((1 $) ((* 0) s))) nil)))
  (define/contract f-bad safe:fmt?
    (list->seec (list (% 0 $ 1 d)
                      (% 0 $ 0 * d)))
    #;(printf-lang (cons (% ((0 $) (1 d)))
                 (cons (% ((0 $) ((* 0) d))) nil))))
  (define/contract f-bad-2 safe:fmt?
    (list->seec (list (% 1 $ 15383 d)
                      (% 0 $ d)
                      ))
    #;(printf-lang (cons (% ((1 $) (16383 d)))
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
                       #:expression-size 6
;                       #:expression-where (λ (e) (equal? e f-concrete))
                       #:context-size 4 ; must be at least 4
                       #:context (context-concrete x-val) ;context-symbolic
                       #:context-where (λ (ctx)
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
    (seec-singleton (% 0 $ 1 * s))
    #;(printf-lang (cons (% ((0 $) ((* 1) s))) nil)))
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
                       #:expression-size 6
;                       #:expression f-concrete
;                       #:expression-where (λ (f) (equal? f f-concrete))
                       #:context-size 6
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
    (list->seec (list (% 3 $ 0 * s) ; first  add value1 to the accumulator
                      (% 3 $ 1 * s) ; second add value2 to the accumulator
                      (% 2 $ n)     ; then write the result to the target location
                      ))
    #;(printf-lang (cons (% ((3 $) ((* 0) s))) ; first  add value1 to the accumulator
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
                       #:expression-size 7
                       #:context context-structure
                       ; NOTE: SEEC is not very good at synthesizing maps based
                       ; on specifications of their contexts... e.g. on what lookup-loc does
                       #:fresh-witness #f
                       #:forall (list l1-val l2-val l3-val x1-val x2-val)
                       ))
    (display-gadget sol displayln)
  )
#;(time (find-add-mem-gadget))

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
    (seec-singleton (% 1 $ 0 * s)))
  (define f-result
    (list->seec (list (% 1 $ 0 * s)
                      (% 1 $ 7424 s)
                      )))

  (define-symbolic N integer?)

  (define-symbolic acc-val integer?) ; initial accumulator
  (define/contract ctx-sketch
    context?
    (printf-lang ((cons ,(integer->bv N) (cons "" nil)) ; arglist
                  (,(integer->bv acc-val) nil))))       ; config

  (define g (find-gadget printf-impl
                         ((curry add-constant-spec) N)
                         #:expression-size 6
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
  (define add-c-fmt (seec-singleton (% 1 $ 0 * s))
    #;(printf-lang (cons (% ((1 $) ((* 0) s)))
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


  (define concrete-fmt (seec-singleton (% 0 $ n))
    #;(printf-lang (cons (% ((0 $) (NONE n)))
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
                         #:expression-size 6
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
  (define store-a-fmt 
    (list->seec (list (string "")
                      (% 0 $ n)))
    #;(printf-lang (cons ""
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
    (seec-singleton (% 0 $ s))
    #;(printf-lang (cons (% ((0 $) (NONE s))) nil)))

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
                         #:expression-size 6
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
  (define store-a-fmt 
    (list->seec (string "")
                (% 0 $ s))
    #;(printf-lang (cons ""
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
    (seec-singleton (% 1 $ 0 * s))
    #;(printf-lang (cons (% ((1 $) ((* 0) s))) nil)))

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
                         #:expression-size 6
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

  (define store-a-fmt
    (list->seec (list (% 1 $ 0 * s)
                      (string "")))
    #;(printf-lang (cons (% ((1 $) ((* 0) s)))
                   (cons ""
                   nil))))

  (define store-a-args (printf-lang (cons ,(integer->bv x) nil)))

  (cons store-a-fmt store-a-args)
  )
