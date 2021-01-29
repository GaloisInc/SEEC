#lang seec
(set-bitwidth 4)
(require racket/format)
(require racket/contract)
(provide (all-defined-out))
(require (file "heap.rkt"))
;
; Shadow-Heap models to work with heap-model from heap.rkt
;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NO-FREELIST
;;
;; This shadow model does away with the freelist,
;; instead representing the heap as an infinitely growing list of payload
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-grammar no-freelist #| TODO: try this #:extends heap-model |#
  (pointer ::= (natural natural) null)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer)
  (payload ::= list<value> empty)
  (buf ::= list<value>)
  (heap ::= list<payload>)
  (state ::= (buf heap))
  ;; copied from heap.rkt
  (buf-loc ::= natural)
  (action ::=
          (set buf-loc nnvalue) ; Set element at buf-loc in buffer to nnvalue
          (read buf-loc buf-loc) ; place the element at pointer (1)buf-loc in heap into the buffer at (2)buf-loc
          (write buf-loc buf-loc); place the element at (1)buf-loc in buffer into the heap pointer (2)buf-loc
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc natural)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= list<action>)
  (observation ::=
               (get buf-loc))
  (total-interaction ::= ; perform interaction, then get nth value from buffer
                     (interaction observation))

  )


(define empty-payload
  (heap-model (cons 0 (cons 0 nil))))

; NOTE: could limit free to offset 0
(define (no-freelist-free h hl)
  (match hl
    [(no-freelist (p:natural o:natural))
     (replace h p (no-freelist empty))]))

(define (no-freelist-alloc h)
  (let* ([l (length h)]
         [h+ (snoc h empty-payload)])
    (cons (no-freelist ,l) h+)))

; return the value at location hl in h
(define (no-freelist-read h hl)
  (match hl
    [(no-freelist (p:natural o:natural))
     (let* ([pl (nth h p)]
            [val (nth pl o)])
     val)]))

; write val at location hl in h
(define (no-freelist-write h hl val)
  (match hl
    [(no-freelist (p:natural o:natural))
     (let* ([pl (nth h p)]
            [pl+ (replace pl o val)]
            [h+ (replace h p pl+)])
       h+)]))


(define (no-freelist-init b-len)
  (no-freelist (,(repeat (no-freelist 0) b-len) nil)))

;; heap-model.action -> no-freelist.state -> no-freelist.state
(define (no-freelist-action a s)
  (match s
    [(no-freelist (b:buf h:heap))
      (match a
        [(heap-model (free hbl:buf-loc))
         (let* ([hl (nth b hbl)]
                [b+ (replace b hbl (no-freelist null))]
                [h+ (no-freelist-free h hl)])
           (no-freelist (,b+ ,h+)))]
        [(heap-model (alloc bl:buf-loc n:natural)) ; ignores n for now
         (let* ([ph+ (no-freelist-alloc h)]
                [b+ (replace b bl (no-freelist (,(car ph+) 0)))])
         (no-freelist (,b+ ,(cdr ph+))))]
        [(heap-model (set bl:buf-loc val:nnvalue))
         (let* ([b+ (replace b bl val)])
         (no-freelist (,b+ ,h)))]
        [(heap-model (read hbl:buf-loc bl:buf-loc))
         (let* ([hl (nth b hbl)]
               [val (no-freelist-read h hl)]
               [b+ (replace b bl val)])
         (no-freelist (,b+ ,h)))]
        [(heap-model (write bl:buf-loc hbl:buf-loc))
         (let* ([val (nth b bl)]
                [hl (nth b hbl)]
                [h+ (no-freelist-write h hl val)])
         (no-freelist (,b ,h+)))])]))
        
;; heap-model.interaction -> no-freelist.state -> no-freelist.state
(define (no-freelist-interaction i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (no-freelist-interaction i+ (no-freelist-action a s))]
    [(heap-model nil)
     s]))

(define (no-freelist-observation o s)
  (match o 
    [(no-freelist (get n:natural))
     (match s
       [(no-freelist (b:buf any))
        (nth b n)])]))

(define (no-freelist-total-interaction ig s)
  (match ig
    [(no-freelist (i:interaction o:observation))
     (let ([s+ (no-freelist-interaction i s)])
       (no-freelist-observation o s+))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Validity predicate for no-freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; heap -> pointer -> boolean
; true if the pointer is wellscoped in heap
(define (no-freelist-scoped-pointer? h p)
  ;(displayln "Is pointer well scoped?")
  ;(displayln p)
  (match p
    [(no-freelist null)
     #t]
    [(no-freelist (l:natural o:natural))
     ; checks if l is smaller than the length of h
     (if (< (seec-length h) l)
         #f
         (let ([v (nth h l)])          
           ; checks if o is smaller than the size of the l-th entry in h
           (match v
             [(no-freelist v:list<any>)
              (not (< (seec-length v) o))]
             [(no-freelist any)
              #f])))]))

; heap -> buf -> boolean
(define (no-freelist-valid-buf h b)
  (match b
    [(no-freelist nil)
     #t]
    [(no-freelist (cons p:pointer b+:buf))
     (and (no-freelist-scoped-pointer? h p)
          (no-freelist-valid-buf h b+))]
    [(no-freelist (cons any b+:buf))
     (no-freelist-valid-buf h b+)]))

(define (no-freelist-valid-heap full-h h)
  (match h
    [(no-freelist nil)
     #t]
    [(no-freelist (cons p:pointer h+:heap))
     (and (no-freelist-scoped-pointer? full-h p)
          (no-freelist-valid-heap full-h h+))]
    [(no-freelist (cons any h+:heap))
      (no-freelist-valid-heap full-h h+)]))

; heap -> heap -> boolean  

(define (no-freelist-valid-state s)
  (match s
    [(no-freelist (b:buf h:heap))
     (and
      (no-freelist-valid-buf h b)
      (no-freelist-valid-heap h h))]))
    


(define-language no-freelist-lang
  #:grammar no-freelist
  #:expression interaction #:size 4
  #:context state #:size 8 #:where no-freelist-valid-state
  #:link cons
  #:evaluate (uncurry no-freelist-interaction))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing no-freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (print-nf-pointer p)
  (match p
    [(heap-model (n:natural o:natural))
     (format "<~a,~a>" n o)]
    [(heap-model null)
     "null"]))

(define (print-nf-nnvalue nv)
  (format "~a" nv))

(define (print-nf-value v)
  (match v
    [(no-freelist nv:nnvalue)
     (print-nf-nnvalue nv)]
    [(no-freelist p:pointer)
     (print-nf-pointer p)]))

(define (print-nf-payload p)
  (match p
    [(no-freelist empty)
     "empty"]
    [(no-freelist vs:list<value>)
     (print-list print-nf-value vs)]))

(define (display-nf-buf b)
    (define (display-nf-buf+ b addr)
    (match b
      [(no-freelist nil)
       (displayln "")]
      [(no-freelist (cons h:value b+:buf))
       (displayln (format "~a > ~a"
                          (~a addr #:width 2)
                          (print-nf-value h)))
       (display-nf-buf+ b+ (+ addr 1))]))
  (display-nf-buf+ b 0))

(define (display-nf-heap h)
  (define (display-nf-heap+ h addr)
    (match h
      [(no-freelist nil)
       (displayln "")]
      [(no-freelist (cons p:payload h+:heap))
       (displayln (format "~a > ~a"
                          (~a addr #:width 2)
                          (print-nf-payload p)))
       (display-nf-heap+ h+ (+ addr 1))]))
  (display-nf-heap+ h 0))

(define (display-nf-state s)
  (match s
    [(no-freelist (b:buf h:heap))
     (begin
       (displayln "BUFFER:")
       (display-nf-buf b)
       (displayln "HEAP (no-freelist model):")
       (display-nf-heap h)
       )]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING no-freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define nf (no-freelist-init 4))
(define nf++ (no-freelist-action aa1 (no-freelist-action aa0 nf)))
(define nf+4* (no-freelist-action af1 (no-freelist-action af0 nf++)))


(define nf+3 (no-freelist-action as nf++))
(define nf+4 (no-freelist-action aw nf+3))
(define nf+5 (no-freelist-action ar nf+4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMBOLIC TESTING no-freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define o0* (no-freelist observation 2))
(define h0* (no-freelist buf 5))


(define (nf-test0)
  (begin
    (define b0* (no-freelist buf 4))
    (define h0* (no-freelist heap 5))
    (define s0* (no-freelist (,b0* ,h0*)))
    (define s0+* (no-freelist state 6))
    (define i0* (no-freelist interaction 4))
    (define o0* (no-freelist observation 2))
    (define d0+* (no-freelist-interaction i0* nf+5))
    (define beh0* (no-freelist-observation o d0+*))
    (define sol (verify #:guarantee (assert (not (equal? beh0* 5)))))
    (define s0 (concretize s0* sol))
    (define d0+ (concretize d0+* sol))
    (define i0 (concretize i0* sol))
    (define o0 (concretize o0* sol))
    (define beh0 (concretize beh0* sol))
    (displayln "State:")
    (display-nf-state s0)
    (displayln "Interaction:")
    (displayln i0)
    (displayln "Observation:")
    (displayln o0)
    (displayln "Behavior:")
    (displayln beh0)))


; Testing the synthesis of an interaction to make a symbolic no-freelist.state similar (shallow) to a heap-model.state
(define (nf-test1)
  (begin
    (define b0* (heap-model buf 4))
    (define h0* (heap-model heap 5))
    (define fp0* (heap-model pointer 1))
    (define s1* (heap-model (,b0* ,h0* ,fp0*)))
    (assert (no-freelist-valid-state s1*))
    (define i1* (no-freelist interaction 4))
    (define s1+* (no-freelist-interaction i1* s1*))
    (define sol (verify #:guarantee (assert (not (shallow-nf-state-eq s1* d+5)))))
    (define s1 (concretize s1* sol))
    (define s1+ (concretize s1+* sol))
    (define i1 (concretize i1* sol))
    (displayln "State pre:")
    (display-nf-state s1)
    (displayln "Interaction:")
    (displayln i1)
    (displayln "State post:")
    (display-nf-state s1+)
    (displayln "Shallow eq:")
    (displayln (shallow-nf-state-eq s1 d+5 #:debug #t))
    (displayln "Deep eq:")
    (displayln (deep-nf-state-eq s1 d+5))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; COMPILING  no-freelist into heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; no-freelist.value -> heap-model.value
(define (compile-nf-value v)
  (match v
    [(no-freelist (l:natural o:natural)) ; heap loc: l * (word size) + o + 1
     (heap-model ,(+ (* l 4) (+ o 1)))]   ; NOTE: if we wanted variable size chunks, we would need the heap here and keep the size of empty chunks
    [(no-freelist any) ; anything else is same in both model
     v]))

    
;; no-freelist.buf -> heap-model.buf 
(define (compile-nf-buf b)
  (match b
    [(no-freelist nil)
     (heap-model nil)]
    [(no-freelist (cons v:value b+:buf))
     (heap-model (cons ,(compile-nf-value v) ,(compile-nf-buf b+)))]))

;; no-freelist.payload -> heap-model.heap -> heap-model.heap
;; add the payload in from of the heap
(define (compile-nf-payload v)
  (match v
    [(no-freelist empty)
     (repeat (heap-model null) 4)]
    [(no-freelist l:list<value>)
     (let* ([v1 (compile-nf-value (head l))]
            [v2 (compile-nf-value (head (tail l)))])
       (heap-model (cons 2 (cons ,v1 (cons ,v2 (cons 1 nil))))))]))


;; no-freelist.heap -> heap-model.heap)
(define (compile-nf-heap h)
  (match h
      [(no-freelist nil)
       (heap-model nil)]
      [(no-freelist (cons v:payload h+:heap))
       (let* ([v+ (compile-nf-payload v)]
              [hp (compile-nf-heap h+)])
         (append v+ hp))]))


;;  no-freelist.state -> heap-model.state
(define (compile-nf-state s)
  (match s
    [(no-freelist (b:buf h:heap))
     (let* ([b+ (compile-nf-buf b)]
            [h+ (compile-nf-heap h)])
       (heap-model (,b+ ,h+ null)))]))

;; compare nnvalues out of shadow-heap.value and heap-model.value
;; returns #:default (#t) if nf-v is a pointer
(define/contract shallow-nf-val-eq
  (->* (any/c any/c)
       (#:debug boolean?
        #:default boolean?)
       boolean?)
  (lambda (nf-v
           v
           #:debug [d #f]
           #:default [def #t])
    (begin
      ;(displayln "in shallow-nf-val-eq")
      (match nf-v
        [(no-freelist nf-i:integer)
         (match v
           [(heap-model i:integer)
            (equal? nf-i i)]
           [(heap-model any)
            #f])]
        [(no-freelist any)
         def]))))


;; shallow (compare non-pointer value) buffer equality
(define/contract shallow-nf-buf-eq
  (->* (any/c any/c)
       (#:debug boolean?)
       boolean?)
  (lambda (nf-b
           b
           #:debug [d #f])
    (begin
      (match nf-b
        [(no-freelist nil)
         (match b
           [(heap-model nil)
            #t]
           [(heap-model any)
            #f])]
        [(no-freelist (cons nf-v:value nf-b+:buf))
         (match b
           [(heap-model (cons v:value b+:buf))
            (and               
             (shallow-nf-val-eq nf-v v #:debug d)
             (shallow-nf-buf-eq nf-b+ b+ #:debug d))]
           [(heap-model any)
            #f])]))))

;; shallow (buffer only) equality
(define/contract shallow-nf-state-eq
  (->* (any/c any/c)
       (#:debug boolean?)
       boolean?)
  (lambda (nf-s s
                #:debug [d #f])
    (begin
      (match nf-s
        [(no-freelist (nf-b:buf any))
         (match s
           [(heap-model (b:buf any any))
            (shallow-nf-buf-eq nf-b b #:debug d)])]))))

;; compare the value in buf zero w
(define (buf-z-nf-eq nf-s s)
  (match nf-s
    [(no-freelist (nf-b:buf any))
     (match s
       [(heap-model (b:buf any any))
        (shallow-nf-val-eq (nth nf-b 0) (nth b 0) #:default #f)])]))


(define-compiler nf-to-heap-compiler
  #:source no-freelist-lang
  #:target heap-lang
  #:behavior-relation buf-z-nf-eq
  #:context-relation shallow-nf-state-eq
  #:compile (lambda (x) x))




;; Deep equality (i.e. heap equality, following pointers), fuel is needed for symbolic reasoning
(define max-fuel 5)

; no-freelist.heap-loc: (l o)
; heap-model.heap-loc: n
(define (deep-nf-pointer-eq+ fuel nf-h h l o n)
  (if (equal? fuel 0)
      #t
      (let* ([nf-pl (nth nf-h l)]
             [nf-v (nth nf-pl o)]
             [v (nth h n)])
        (deep-nf-val-eq (- fuel 1) nf-h h nf-v v))))

(define (deep-nf-pointer-eq fuel nf-h h nf-p p)
  (match nf-p
    [(no-freelist (l:natural o:natural))
     (match p
       [(heap-model n:natural)
        (deep-nf-pointer-eq+ fuel nf-h h l o n)]
       [(heap-model any)
        #f])]
    [(no-freelist null)
     (match p
       [(heap-model null)
        #t]
       [(heap-model any)
        #f])]))



;; compare nnvalues out of shadow-heap.value and heap-model.value
(define (deep-nf-val-eq fuel nf-h h nf-v v)
  (match nf-v
    [(no-freelist nf-i:integer)
     (match v
       [(heap-model i:integer) ; note that this is potentially a heap-loc, but we have no way to distinguish this in heap-model
        (equal? nf-i i)]
       [(heap-model any)
        #f])]
    [(no-freelist nf-p:pointer)
     (match v
       [(heap-model p:pointer)
        (deep-nf-pointer-eq fuel nf-h h nf-p p)])]))


;; deep (compare all value) buffer equality
;;; indexed by heaps
(define (deep-nf-buf-eq nf-h h nf-b b)
  (match nf-b
    [(no-freelist nil)
       (match b
         [(heap-model nil)
          #t]
         [(heap-model any)
          #f])]
    [(no-freelist (cons nf-v:value nf-b+:buf))
       (match b
         [(heap-model (cons v:value b+:buf))
          (and               
           (deep-nf-val-eq max-fuel nf-h h nf-v v)
           (deep-nf-buf-eq nf-h h nf-b+ b+))]
         [(heap-model any)
          #f])]))

;; deep (buffer only) equality
(define (deep-nf-state-eq nf-s s)
  (match nf-s
    [(no-freelist (nf-b:buf nf-h:heap))
     (match s
       [(heap-model (b:buf h:heap any))
        (deep-nf-buf-eq nf-h h nf-b b)])]))
#|
;; Testing synthesis with the no-freelist to heap-model compiler
; Make a schema for a heap-model.state with buf = 4 and state of size 8
(define b* (heap-model buf 4))
(define h* (heap-model heap 8))
(define fp* (heap-model pointer 1))
(define s* (heap-model (,b* ,h* ,fp*)))
(define s+* (heap-model state 8))

; Make a schema for a no-freelist.state with buf = 4 and state of max size 5?
(define nfb* (no-freelist buf 4))
(define nfh* (no-freelist heap 5))
(define nfs* (no-freelist (,nfb* ,nfh*)))
(define nfs+* (no-freelist state 8))

; find a context and a total interaction that evaluates to 4
(define ti* (heap-model total-interaction 4))
(define (ex1)
  (begin
    (define beh* (interpret-total-interaction ti* s+*))
    (define nf-beh* (no-freelist-total-interaction ti* nfs+*))
    ;(assert (equal? nf-b* 5))
    (define sol (verify #:guarantee (assert (equal? beh* nf-beh*))))
    sol))
|#
#;(find-changed-component nf-to-heap-compiler
                        #:source-context nfs*
                        #:target-context s*)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FREELIST model
;;
;; Demonstration of a model that carries less info than the full one:
;; This shadow model only keeps track of the freelist
;; and ignores the payload/buffer
;; this is only maintainable with additional state being carried -- transling free hbl into free n
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-grammar freelist
    (action ::=
          (free natural) ; free the object natural if it is allocated
          alloc) ; allocate an object
  (interaction ::= list<action>)
   (state ::= (list<natural>) ; list of free blocks
          ))

;; freelist.action -> freelist.state -> freelist.state
(define (freelist-action a s)
  (match a
    [(freelist (free n:natural))
     (freelist (cons ,n ,s))]
    [(freelist alloc)
     (match s
       [(freelist nil)
        s]
       [(freelist (cons any s+:any))
        s+])
     ]))

    
;; freelist.interaction -> freelist.state -> freelist.state
(define (freelist-interaction i s)
  (match i
    [(freelist (cons a:action i+:interaction))
     (freelist-interaction i+ (freelist-action a s))]
    [(freelist nil)
     s]))


;; heap-model.action -> heap-model.state -> #f + freelist.action
(define (freelist-shadow-action a s)
  (match s
    [(heap-model (b:buf h:heap f:pointer))
     (match a
       [(heap-model (free bl:buf-loc))
        (let* ([p (nth b bl)])
          (freelist (free ,p)))]
       [(heap-model (alloc bl:buf-loc n:natural))
         (freelist alloc)]
       [_ #f])]))

;; heap-action.action -> heap-model.state X freelist.state -> heap-model.state X freelist.state
(define (heap-and-freelist-action a sfs )
  (let* ([s (car sfs)]
         [fs (cdr sfs)]
         [s+ (interpret-action a s)]
         [af (freelist-shadow-action a s)]
         [fs+ (if af
                  (freelist-action af fs)
                  fs)])
    (cons s+ fs+)))

;; heap-model.interaction -> heap-model.state -> freelist.state -> heap-model.state X freelist.state
(define (freelist-shadow-interaction i s fs)  
  (match i
    [(heap-model (cons a:action i+:interaction))
     (let* ([s+ (interpret-action a s)]
            [af (freelist-shadow-action a s)]
            [fs+ (if af
                     (freelist-action af fs)
                     fs)])
       (interpret-interaction i+ s+ fs+))]
    [(heap-model nil)
     (cons s fs)]))


(define (heap-and-freelist-interaction i sfs)
  (freelist-shadow-interaction i (car sfs) (cdr sfs)))

(define (init-freelist)
  (freelist nil))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; COMPILING heap-model to freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; heap-model.state -> freelist.state
(define (compile-heap-to-freelist s)
  (define (compile-into-freelist h p )
    (match p
      [(heap-model null)
       (freelist nil)]
      [(heap-model n:natural)
       (let* ([new-p (nth h n)]
              [rest (compile-into-freelist h new-p)])
         (freelist (cons ,n ,rest)))]))
  (match s
    [(heap-model (any h:heap p:pointer))
                 (compile-into-freelist h p)]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (display-f-state fs)
  (match fs
    [(freelist nil)
     (displayln "")]
    [(freelist (cons n:natural fs+:any))
     (displayln n)
     (display-f-state fs+)]))


(define (display-hf-state sfs)
  (displayln "Full State:")
  (display-state (car sfs))
  (displayln "")
  (displayln "Freelist Shadow Model:")
  (display-f-state (cdr sfs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define df (cons (init-state 4 2) (init-freelist)))

(define df++ (heap-and-freelist-action aa1 (heap-and-freelist-action aa0 df)))
(define df+4* (heap-and-freelist-action af1 (heap-and-freelist-action af0 df++)))


(define df+3 (heap-and-freelist-action as df++))
(define df+4 (heap-and-freelist-action aw df+3))
(define df+5 (heap-and-freelist-action ar df+4))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; PREDICATES for freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; freelist.state -> natural
(define (freelist-size fs)
  (seec-length fs))


(define (f-test0)
  (begin
    (define f0* (freelist state 4))
    (define sol (solve (= (freelist-size f0*) 2)))    
    (if sol
        (begin
          (define f0 (concretize f0* sol))
          (display-f-state f0))
        (displayln "unsat"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Relating the heap-model freelist with the shadow freelist
;; no need for fuel since fl is a finite list?
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (freelist-shadow? h f fs)
  (match fs
    [(freelist nil)
     (match f
       [(heap-model null) #t]
        [(heap-model any) #f])]
    [(freelist (cons n:natural fs+:any))
     (let* ([f+ (nth h f)])
       (and (equal? f n)
            (freelist-shadow? h f+ fs+)))]))

(define (freelist-state-shadow? s fs)
  (match s
    [(heap-model (any h:heap f:pointer))
     (freelist-shadow? h f fs)]))

(define heap-and-freelist-shadow? (uncurry freelist-state-shadow?))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMBOLIC TESTING df-state-shadow
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (df-test0)
  (begin
    (define b0* (heap-model buf 4))
    (define h0* (heap-model heap 5))
    (define fp0* (heap-model pointer 1))
    (define s0* (heap-model (,b0* ,h0* ,fp0*)))
    (define i0* (heap-model interaction 4))
    (define ns0* (freelist state 4))
    (define df0* (cons s0* ns0*))
    ;(assert (heap-and-freelist-shadow? df0*))
    (define df0+* (heap-and-freelist-interaction i0* df0*))
    (define sol (solve (not (= (freelist-size (cdr df0+*)) (freelist-length 3 (car df0+*))))))
    (define df0 (concretize df0* sol))
    (define i0 (concretize i0* sol))
    (define df0+ (concretize df0+* sol))
    (displayln "State pre:")
    (display-hf-state df0)
    (displayln "Interaction:")
    (displayln i0)
    (displayln "State post:")
    (display-hf-state df0+)))


