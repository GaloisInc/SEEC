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
  (action ::=
          (set buf-loc nnvalue) ; Set element at buf-loc in buffer to nnvalue
          (read buf-loc buf-loc) ; place the element at pointer (1)buf-loc in heap into the buffer at (2)buf-loc
          (write buf-loc buf-loc); place the element at (1)buf-loc in buffer into the heap pointer (2)buf-loc
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc natural)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= ; list of actions
               (action interaction)
               nop)
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
    [(heap-model (a:action i+:interaction))
     (no-freelist-interaction i+ (no-freelist-action a s))]
    [(heap-model nop)
     s]))

(define (no-freelist-observation o s)
  (match o 
    [(no-freelist (get n:natural))
     (match s
       [(no-freelist (b:buf any any))
        (nth b n)])]))

(define (no-freelist-total-interaction ig s)
  (match ig
    [(no-freelist (i:interaction o:observation))
     (let ([s+ (no-freelist-interaction i s)])
       (no-freelist-observation o s+))]))


(define-language no-freelist-lang
  #:grammar no-freelist
  #:expression interaction #:size 4
  #:context state #:size 8
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
;; always #t if nf-v is a pointer
(define (shallow-nf-val-eq nf-v v)
  (match nf-v
    [(no-freelist nf-i:integer)
     (match v
       [(heap-model i:integer)
        (equal? nf-i i)]
       [(heap-model any)
        #f])]
    [(no-freelist any)
     #t]))


;; shallow (compare non-pointer value) buffer equality
(define (shallow-nf-buf-eq nf-b b)
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
           (shallow-nf-val-eq nf-v v)
           (shallow-nf-buf-eq nf-b+ b+))]
         [(heap-model any)
          #f])]))

;; shallow (buffer only) equality
(define (shallow-nf-state-eq nf-s s)
  (match nf-s
    [(no-freelist (nf-b:buf any))
     (match s
       [(heap-model (b:buf any any))
        (shallow-nf-buf-eq nf-b b)])]))


(define-compiler nf-to-heap-compiler
  #:source no-freelist
  #:target heap-model
  #:behavior-relation equal?
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
  (interaction ::= (action interaction)
               nop)
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
    [(freelist (a:action i+:interaction))
     (freelist-interaction i+ (freelist-action a s))]
    [(freelist nop)
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
    [(heap-model (a:action i+:interaction))
     (let* ([s+ (interpret-action a s)]
            [af (freelist-shadow-action a s)]
            [fs+ (if af
                     (freelist-action af fs)
                     fs)])
       (interpret-interaction i+ s+ fs+))]
    [(heap-model nop)
     (cons s fs)]))

(define (init-freelist)
  (freelist nil))

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

(define df-state-shadow? (uncurry freelist-state-shadow?))
