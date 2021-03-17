#lang seec
(set-bitwidth 4)

(require racket/format)
(require seec/private/util)
(require seec/private/monad)

;(require racket/contract)
(provide (all-defined-out))
(require (file "heap.rkt"))
;
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HEAP-STRUCT
;;
;; This model aims at given more structure to the heap, without representing the freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-grammar heap-struct 
  (pointer ::= (natural natural) null)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer)
  (payload ::= empty (integer integer))
  (buf ::= (value value))
  (heap ::= list<payload>) ;(payload payload))
  (state ::= (buf heap))
  (action ::=
          (set buf-loc nnvalue) ; Set element at buf-loc in buffer to nnvalue
          (read buf-loc buf-loc) ; place the element at pointer (1)buf-loc in heap into the buffer at (2)buf-loc
          (write buf-loc buf-loc); place the element at (1)buf-loc in buffer into the heap pointer (2)buf-loc
          (free buf-loc) ; free the object at the pointer held in buf-loc in buffer
          (alloc buf-loc natural)) ; alloc an object with n blocks, placing its pointer in buffer at buf-loc
  (interaction ::= list<action>)
)

(define empty-payload
  (heap-struct (0 0)))

(define (heap-struct-free h hl)
  (match hl
    [(heap-struct (p:natural o:natural))
     (replace h p (heap-struct empty))]))

(define (heap-struct-alloc h)
  (let* ([l (length h)]
         [h+ (enqueue h empty-payload)])
    (cons (heap-struct ,l) h+)))

(define (get-nth-pair o pl)
  (match pl
    [(heap-struct (v0:any v1:any))
     (match o
       [(heap-struct 0)
        v0]
       [(heap-struct 1)
        v1])]))

(define (seec-pair-to-list p)
  (match p
    [(heap-struct (v0:any v1:any))
     (heap-struct (cons ,v0 (cons ,v1 nil)))]))

; return the value at location hl in h
(define (heap-struct-read h hl)
  (match hl
    [(heap-struct (p:natural o:natural))
     (let* ([pl (nth h p)])
       (get-nth-pair o pl))]))


(define (replace-nth-pair o pl val)
  (match pl
    [(heap-struct (v0:any v1:any))
     (match o
       [(heap-struct 0)
        (heap-struct (,val ,v1))]
       [(heap-struct 1)
        (heap-struct (,v1 ,val))])]))


; write val at location hl in h
(define (heap-struct-write h hl val)
  (match hl
    [(heap-struct (p:natural o:natural))
     (let* ([pl (get-nth-pair h p)]
            [pl+ (replace-nth-pair pl o val)]
            [h+ (replace-nth-pair h p pl+)])
       h+)]))


;; heap-model.action -> heap-struct.state -> heap-struct.state
(define (heap-struct-action a s)
  (match s
    [(heap-struct (b:buf h:heap))
      (match a
        [(heap-model (free hbl:buf-loc))
         (let* ([hl (get-nth-pair b hbl)]
                [b+ (replace-nth-pair b hbl (heap-struct null))]
                [h+ (heap-struct-free h hl)])
           (heap-struct (,b+ ,h+)))]
        [(heap-model (alloc bl:buf-loc n:natural)) ; ignores n for now
         (let* ([ph+ (heap-struct-alloc h)]
                [b+ (replace b bl (heap-struct (,(car ph+) 0)))])
         (heap-struct (,b+ ,(cdr ph+))))]
        [(heap-model (set bl:buf-loc val:nnvalue))
         (let* ([b+ (replace b bl val)])
         (heap-struct (,b+ ,h)))]
        [(heap-model (read hbl:buf-loc bl:buf-loc))
         (let* ([hl (get-nth-pair b hbl)]
               [val (heap-struct-read h hl)]
               [b+ (replace-nth-pair b bl val)])
         (heap-struct (,b+ ,h)))]
        [(heap-model (write bl:buf-loc hbl:buf-loc))
         (let* ([val (get-nth-pair b bl)]
                [hl (get-nth-pair b hbl)]
                [h+ (heap-struct-write h hl val)])
         (heap-struct (,b ,h+)))])]))
        
;; heap-model.interaction -> heap-struct.state -> heap-struct.state
(define (heap-struct-interaction i s)
  (match i
    [(heap-model (cons a:action i+:interaction))
     (heap-struct-interaction i+ (heap-struct-action a s))]
    [(heap-model nil)
     s]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing heap-struct
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (print-hs-pointer p)
  (match p
    [(heap-model (n:natural o:natural))
     (format "<~a,~a>" n o)]
    [(heap-model null)
     "null"]))

(define (print-hs-nnvalue nv)
  (format "~a" nv))

(define (print-hs-value v)
  (match v
    [(heap-struct nv:nnvalue)
     (print-hs-nnvalue nv)]
    [(heap-struct p:pointer)
     (print-hs-pointer p)]))

(define (print-hs-payload p)
  (match p
    [(heap-struct empty)
     "empty"]                  
    [(heap-struct (v0:value v1:value))
     (format "(~a ~a)"
                        (print-hs-value v0)
                        (print-hs-value v1))]))


(define (display-hs-buf h)
  (match h
    [(heap-struct (p0:value p1:value))
     (displayln (format "0 > ~a"
                        (print-hs-value p0)))
     (displayln (format "1 > ~a"
                        (print-hs-value p1)))]))

(define (display-hs-heap h)
  (define (display-hs-heap+ h addr)
    (match h
      [(heap-struct nil)
       (displayln "")]
      [(heap-struct (cons p:payload h+:heap))
       (displayln (format "~a > ~a"
                          (~a addr #:width 2)
                          (print-hs-payload p)))
       (display-hs-heap+ h+ (+ addr 1))]))
  (display-hs-heap+ h 0))

(define (display-hs-state s)
  (match s
    [(heap-struct (b:buf h:heap))
     (begin
       (displayln "BUFFER:")
       (display-hs-buf b)
       (displayln "HEAP (heap-struct model):")
       (display-hs-heap h)
       )]))

;; heap-struct.buf -> heap-model.buf 
(define (compile-hs-buf b)
  (match b
    [(heap-struct (n1:integer n2:integer))
     (heap-model (cons ,n1 (cons ,n2  nil)))]))

;; heap-struct.payload -> heap-model.heap -> heap-model.heap
;; add the payload in from of the heap
(define (compile-hs-payload v)
  (match v
    [(heap-struct empty)
     (heap-model (cons 0 (cons 2 (cons null (cons null nil)))))]
    [(heap-struct (v1:integer v2:integer))
       (heap-model (cons 1 (cons 2 (cons ,v1 (cons ,v2 nil)))))]))

(define (make-wild n)
  (if (< 0 n)
      (let* ([size (- (* n 4) 2)]
             [payload (repeat (heap-model 0) size)])
        (heap-model (cons 0 (cons ,size ,payload))))
      (heap-model nil)))


; n is the size (in block) of the resulting heap.
;; natural -> heap-struct.heap -> heap-model.heap)
(define/debug (compile-hs-heap-wild n h)
  (match h
      [(heap-struct nil)
       (make-wild n)]
      [(heap-struct (cons v:payload h+:heap))
       (let* ([v+ (compile-hs-payload v)]
              [hp (compile-hs-heap-wild (- n 1) h+)])
         (append v+ hp))]))

;;  natural -> heap-struct.state -> heap-model.state
(define (compile-hs-state-wild n s)
  (match s
    [(heap-struct (b:buf h:heap))
     (let* ([b+ (compile-hs-buf b)]
;            [h+ (seec-pair-to-list h)]
            [h+ (compile-hs-heap-wild n h)])
       (heap-model (,b+ ,h+ null)))]))





(define (head-or-null l)
  (match l
    [(heap-struct nil)
     (heap-struct null)]
    [(heap-struct (cons hd:any any))
     hd]))
     

;; Trying to compile a heap-struct into a heap with a freelist.
; input: a partial heap, the index into the heap (number of blocks), a stack of freelist block (list<natural>) 
; Returns: a partial heap and backward pointer 
(define/debug #:suffix (compile-hs-heap-freelist+ h total-block curr-block bwd)
  (match h
    [(heap-struct nil)
     (let* ([wild-size (- total-block curr-block)]
            [wild (make-wild wild-size)])                  
       (cons wild (heap-model null)))]
    [(heap-struct (cons empty h+:heap)) ; free block
     (let* ([p-addr (+ (* curr-block 4) 2)]
            [ret (compile-hs-heap-freelist+ h+ total-block (+ curr-block 1) (heap-model ,p-addr))]
            [ret-h (car ret)]
            [ret-fwd (cdr ret)]
            [new-h (heap-model (cons 0 (cons 2 (cons ,ret-fwd (cons ,bwd ,ret-h)))))])
            (cons new-h (heap-model ,p-addr)))]
    [(heap-struct (cons v:payload h+:heap)) ; non-free block
     (let* ([v+ (compile-hs-payload v)]
            [ret (compile-hs-heap-freelist+ h+ total-block (+ curr-block 1) bwd)]
            [ret-h (car ret)]
            [ret-fwd (cdr ret)]
            [new-h (append v+ ret-h)])
       (cons new-h ret-fwd))]))
            
(define (compile-hs-heap-freelist n h)
  (compile-hs-heap-freelist+ h n 0 (heap-model null)))
      
                  

(define (compile-hs-state-freelist n s)
  (match s
    [(heap-struct (b:buf h:heap))
     (let* ([b+ (compile-hs-buf b)]
;            [h+ (seec-pair-to-list h)]
            [ret (compile-hs-heap-freelist n h)]
            [ret-h (car ret)]
            [ret-p (cdr ret)])
       (heap-model (,b+ ,ret-h ,ret-p)))]))




(define (test-freelist s)
  (parameterize ([debug? #t])
    (compile-hs-state-freelist 2 s)))

(define (test-wild s)
  (parameterize ([debug? #t])
    (compile-hs-state-wild 2 s)))

;;; EQUALITY
; shallow value equality
; #t on pointers
(define/debug (eq-hs-shallow-value hv v)
  (match hv
    [(heap-struct i:integer)
     (match v
       [(heap-model iv:integer)
        (equal? i iv)]
       [any 
        #f])]
    [(heap-struct p:pointer)
     #t]))

; deep value equality
; #t on pointers
(define/debug (eq-hs-deep-pointer hp p hh h)
  (define (eq-hs-deep-pointer+ l o i hh h)
    (do v <- opt-nth h i
        p <- opt-nth hh l
        (match p
          [(heap-struct empty) #f]
          [(heap-struct (i0:integer i1:integer))
           (match o
             [(heap-struct 0)
              (equal? v i0)]
             [(heap-struct 1)
              (equal? v i1)]
             [any #f])])))
  (match hp
    [(heap-struct null)
     (match p
       [(heap-model null)
        #t]
       [any
        #f])]
    [(heap-struct (l:natural o:natural))
     (match p
       [(heap-model i:natural)
        (let ([r (eq-hs-deep-pointer+ l o i hh h)])
          (if (failure? r)
              #f
              r))]
       [any
        #f])]))

(define/debug (eq-hs-deep-value hv v hh h)
  (match hv
    [(heap-struct hi:integer)
     (match v
       [(heap-model i:integer)
        (equal? hi i)]
       [any 
        #f])]
    [(heap-struct hp:pointer)
     (match v
       [(heap-model p:pointer)
        (eq-hs-deep-pointer hp p hh h)]
       [any 
        #f])]))



; shallow buffer equality
(define/debug #:suffix (eq-hs-shallow-buf hb b)
  (match hb
    [(heap-struct (v0:value v1:value))
     (match b
       [(heap-model (cons b0:value (cons b1:value nil)))
        (and (eq-hs-shallow-value v0 b0)
             (eq-hs-shallow-value v1 b1))]
       [any
        #f])]))

; deep buffer equality
(define/debug #:suffix (eq-hs-deep-buf hb b hh h)
  (match hb
    [(heap-struct (v0:value v1:value))
     (match b
       [(heap-model (cons b0:value (cons b1:value nil)))
        (and (eq-hs-deep-value v0 b0 hh h)
             (eq-hs-deep-value v1 b1 hh h))]
       [any
        #f])]))

(define (eq-hs-shallow-state hs s)
  (match hs
    [(heap-struct (nf-b:buf nf-h:heap))
     (match s
       [(heap-model (b:buf h:heap any))
        (eq-hs-shallow-buf nf-b b)])]))

(define (eq-hs-deep-state hs s)
  (match hs
    [(heap-struct (nf-b:buf nf-h:heap))
     (match s
       [(heap-model (b:buf h:heap any))
        (eq-hs-deep-buf nf-b b nf-h h)])]))

; compare a heap-struct.payload with a heap-model.block
(define/debug #:suffix (eq-struct-payload p bl)
  (match p
    [(heap-struct empty)
     (match bl
       [(heap-model (cons 0 (cons 2 (cons any (cons any nil)))))
        #t]
       [(heap-model any)
        #f])]
    [(heap-struct (v1:integer v2:integer))
     (match bl
       [(heap-model (cons 1 (cons 2 (cons b1:integer (cons b2:integer nil)))))
        (and (equal? v1 b1)
             (equal? v2 b2))]
       [(heap-model any)
        #f])]
    [any
     #f]))

(define/debug #:suffix (eq-struct-heap hs h)
  (match hs
    [(heap-struct nil)
     (match h
       [(heap-model nil)
        #t]
       [(heap-model (cons 0 (cons size:natural h+:heap))) ; TODO: handle trailing wildarea
        (equal? size (length h+))]
       [(heap-model any)
        #f])]
    [(heap-struct (cons p:payload hs+:heap))
     (and (eq-struct-payload p (first-nth 4 h))
          (eq-struct-heap hs+ (skip 4 h)))]
    [any
     #f]))

(define/debug #:suffix (eq-struct-heap-state ss s)
  (match ss
    [(heap-struct (any hs:heap))
     (match s
        [(heap-model (any h:heap any))
         (eq-struct-heap hs h)]
        [any #f])]    
    [any #f]))

(define (test-eq-shs ss s)
  (parameterize ([debug? #t]) (eq-struct-heap-state ss s)))

;;; DECOMPILE A HEAP
#|(define (decompile-heap h)
  (match h
    [(heap-model nil)
     (heap-struct nil)]
    [(heap-model (cons in-use:natural h+:heap))
     (match h+
       [(heap-model (cons 2 h++:heap))
        (match h++
          [(heap-model 
    [(heap-model any) *fail*]))|#


(define (syn-freelist-length)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-freelist 2 nf-s*))
    (define sol (solve (assert (equal? (freelist-length 3 s*) 1))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)))))

; find an action that breaks the freelist
(define (new-heap-syn-test-freelist)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-freelist 2 nf-s*))
    (define a* (heap-model action 3)) 
    (define s+* (interpret-action a* s*))
    (define sol (solve (assert (not (valid-state-block s+*)))))
;    (define sol (solve (assert (not (valid-freelist-state-af 3 s+*)))))
    ;(define sol (solve (assert (not (valid-state 3 s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (display "valid block?: ")
          (parameterize ([debug? #t]) (valid-state-block s+))))))


; find an action that breaks the freelist
(define (new-heap-syn-test-wild)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-wild 2 nf-s*))
    (define a* (heap-model action 3)) 
    (define s+* (interpret-action a* s*))
    (define sol (solve (assert (not (valid-state-block s+*)))))
;    (define sol (solve (assert (not (valid-freelist-state-af 3 s+*)))))
    ;(define sol (solve (assert (not (valid-state 3 s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (display "valid block?: ")
          (parameterize ([debug? #t]) (valid-state-block s+))))))



(define (new-heap-syn-test-wild-i)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-wild 2 nf-s*))
    (define a* (heap-model interaction 4)) 
    (define s+* (interpret-interaction a* s*))
    (define sol (solve (assert (not (valid-state-block s+*)))))
;    (define sol (solve (assert (not (valid-freelist-state 3 s+*)))))
    ;(define sol (solve (assert (not (valid-state 3 s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (display "valid block?: ")
          (parameterize ([debug? #t]) (valid-freelist-state 3 s+))))))


(define (test-1)
  (begin
    (define s2* d+4*)
    (define i2* (heap-model interaction 4))
    (define s2+* (interpret-interaction i2* s2*))
    (define sol (solve (assert (not (valid-freelist-state-af 3 s2+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (define s2 (concretize s2* sol))
          (define i2 (concretize i2* sol))
          (define s2+ (concretize s2+* sol))
          (clear-asserts!)
          (displayln "State:")
          (display-state s2)
          (displayln "Interaction:")
          (displayln i2)
          (display "Safe Interaction?: ")
          (displayln (heap-model-safe-interaction i2 s2))
          (display "Valid Interaction?: ")
          (displayln (heap-model-valid-interaction i2 s2))
          (displayln "State+:")
          (display-state s2+)
          (display "Valid state+? ")
          (displayln (valid-state 3 s2+))))))




(define nf-b (heap-struct (0 0)))
(define nf-h (heap-struct (cons empty (cons (9 10) nil)))) ;(empty (9 10))))
(define nf (heap-struct (,nf-b ,nf-h)))
(define nfs-w (compile-hs-state-wild 2 nf))
(define nfs-f (compile-hs-state-freelist 2 nf))


#;(define-language struct-lang
  #:grammar heap-struct
  #:expression interaction #:size 3
  #:context state #:size 6
  #:link (lambda (e c) (cons (compile-hs-state-wild c) e))
  #:evaluate (uncurry interpret-interaction))




;;;;;; OSB Mar 16 lang
;;; Source exp is heap-struct state
;;; Source context is heap-struct action
;;; target exp is heap-model state
;;; target context is heap-model action
(define-language struct-ss-lang
  #:grammar heap-struct
  #:expression state #:size 4
  #:context action #:size 2
  #:link cons
  #:evaluate (uncurry heap-struct-interaction))

(define-language struct-lang
  #:grammar heap-struct
  #:expression state #:size 4
  #:context action #:size 2
  #:link cons
  #:evaluate (uncurry heap-struct-action))

(define-compiler heap-struct-ss-compiler
  #:source struct-ss-lang
  #:target new-heap-ss-lang
  #:behavior-relation eq-struct-heap-state
  #:context-relation equal?
  #:compile (lambda (x) (compile-hs-state-freelist 2 x)))



; looking for some heap-struct.state nf and heap-model.action a s.t.
; target behavior = (interpret-action a (compile s))
; find a target behavior (s+) s.t. no nf-new is equivalent
(define (test-hs-compiler)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-freelist 2 nf-s*))
    (define a* (heap-model action 3))
    (define s+* (interpret-action a* s*))
    (define nf-new* (heap-struct state 6)) ; have to be bigger than nf-s* since allocated block have more depth, should fix it
    (define sol (synthesize
                 #:forall nf-new*
                 #:guarantee (assert (not (eq-struct-heap-state nf-new* s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (define nf-new (concretize nf-new* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)))))


(define (test-compiler-heap)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-freelist 2 nf-s*))
    (define a* (heap-model action 3))
    (define nf-s+* (heap-struct-action a* nf-s*))
    (define s+* (interpret-action a* s*))
    (define nf-new* (heap-struct state 4))
    (define sol (solve (assert (not (eq-struct-heap-state nf-s+* s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (define nf-s+ (concretize nf-s+* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (displayln "New State+:")
          (display-hs-state nf-s+)))))

(define (test-compiler-shallow)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-freelist 2 nf-s*))
    (define a* (heap-model action 3))
    (define nf-s+* (heap-struct-action a* nf-s*))
    (define s+* (interpret-action a* s*))
    (define sol (solve (assert (not (eq-hs-shallow-state nf-s+* s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (define nf-s+ (concretize nf-s+* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (displayln "New State+:")
          (display-hs-state nf-s+)))))

 (define (test-compiler-deep)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-freelist 2 nf-s*))
    (define a* (heap-model action 3))
    (define nf-s+* (heap-struct-action a* nf-s*))
    (define s+* (interpret-action a* s*))
    (define sol (solve (assert (not (eq-hs-deep-state nf-s+* s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (define nf-s+ (concretize nf-s+* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (displayln "New State+:")
          (display-hs-state nf-s+)))))

 (define (test-compiler-deep-i)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-hs-state-freelist 2 nf-s*))
    (define a* (heap-model interaction 4))
    (define nf-s+* (heap-struct-interaction a* nf-s*))
    (define s+* (interpret-interaction a* s*))
    (define sol (solve (assert (not (eq-hs-deep-state nf-s+* s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define s+ (concretize s+* sol))
          (define nf-s+ (concretize nf-s+* sol))
          (displayln "NF-state:")
          (display-hs-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (displayln "New State+:")
          (display-hs-state nf-s+)))))


(define (cc-hs-compiler)
  (display-changed-component (find-changed-component heap-struct-ss-compiler) displayln))

(define (wc-hs-compiler)
  (display-changed-component (find-weird-component heap-struct-ss-compiler) displayln))
