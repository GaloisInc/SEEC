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
  (buf ::= (integer integer))
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
    [(heap-struct nv:nnvalue)
     (print-nf-nnvalue nv)]
    [(heap-struct p:pointer)
     (print-nf-pointer p)]))

(define (print-nf-payload p)
  (match p
    [(heap-struct empty)
     "empty"]                  
    [(heap-struct (v0:value v1:value))
     (format "(~a ~a)"
                        (print-nf-value v0)
                        (print-nf-value v1))]))


(define (display-nf-buf h)
  (match h
    [(heap-struct (p0:integer p1:integer))
     (displayln (format "0 > ~a"
                        p0))
     (displayln (format "1 > ~a"
                        p1))]))

(define (display-nf-heap h)
  (define (display-nf-heap+ h addr)
    (match h
      [(heap-struct nil)
       (displayln "")]
      [(heap-struct (cons p:payload h+:heap))
       (displayln (format "~a > ~a"
                          (~a addr #:width 2)
                          (print-nf-payload p)))
       (display-nf-heap+ h+ (+ addr 1))]))
  (display-nf-heap+ h 0))

(define (display-nf-state s)
  (match s
    [(heap-struct (b:buf h:heap))
     (begin
       (displayln "BUFFER:")
       (display-nf-buf b)
       (displayln "HEAP (heap-struct model):")
       (display-nf-heap h)
       )]))

;; heap-struct.buf -> heap-model.buf 
(define (compile-nf-buf b)
  (match b
    [(heap-struct (n1:integer n2:integer))
     (heap-model (cons ,n1 (cons ,n2  nil)))]))

;; heap-struct.payload -> heap-model.heap -> heap-model.heap
;; add the payload in from of the heap
(define (compile-nf-payload v)
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
(define/debug (compile-nf-heap-wild n h)
  (match h
      [(heap-struct nil)
       (make-wild n)]
      [(heap-struct (cons v:payload h+:heap))
       (let* ([v+ (compile-nf-payload v)]
              [hp (compile-nf-heap-wild (- n 1) h+)])
         (append v+ hp))]))

;;  natural -> heap-struct.state -> heap-model.state
(define (compile-nf-state-wild n s)
  (match s
    [(heap-struct (b:buf h:heap))
     (let* ([b+ (compile-nf-buf b)]
;            [h+ (seec-pair-to-list h)]
            [h+ (compile-nf-heap-wild n h)])
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
(define/debug #:suffix (compile-nf-heap-freelist+ h total-block curr-block bwd)
  (match h
    [(heap-struct nil)
     (let* ([wild-size (- total-block curr-block)]
            [wild (make-wild wild-size)])                  
       (cons wild (heap-model null)))]
    [(heap-struct (cons empty h+:heap)) ; free block
     (let* ([p-addr (+ (* curr-block 4) 2)]
            [ret (compile-nf-heap-freelist+ h+ total-block (+ curr-block 1) (heap-model ,p-addr))]
            [ret-h (car ret)]
            [ret-fwd (cdr ret)]
            [new-h (heap-model (cons 0 (cons 2 (cons ,ret-fwd (cons ,bwd ,ret-h)))))])
            (cons new-h (heap-model ,p-addr)))]
    [(heap-struct (cons v:payload h+:heap)) ; non-free block
     (let* ([v+ (compile-nf-payload v)]
            [ret (compile-nf-heap-freelist+ h+ total-block (+ curr-block 1) bwd)]
            [ret-h (car ret)]
            [ret-fwd (cdr ret)]
            [new-h (append v+ ret-h)])
       (cons new-h ret-fwd))]))
            
(define (compile-nf-heap-freelist n h)
  (compile-nf-heap-freelist+ h n 0 (heap-model null)))
      
                  

(define (compile-nf-state-freelist n s)
  (match s
    [(heap-struct (b:buf h:heap))
     (let* ([b+ (compile-nf-buf b)]
;            [h+ (seec-pair-to-list h)]
            [ret (compile-nf-heap-freelist n h)]
            [ret-h (car ret)]
            [ret-p (cdr ret)])
       (heap-model (,b+ ,ret-h ,ret-p)))]))




(define (test-freelist s)
  (parameterize ([debug? #t])
    (compile-nf-state-freelist 2 s)))

(define (test-wild s)
  (parameterize ([debug? #t])
    (compile-nf-state-wild 2 s)))

;;; EQUALITY

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
        #t]
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
    (define s* (compile-nf-state-freelist 2 nf-s*))
    (define sol (solve (assert (equal? (freelist-length 3 s*) 1))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (displayln "NF-state:")
          (display-nf-state nf-s)
          (displayln "State:")
          (display-state s)))))

; find an action that breaks the freelist
(define (new-heap-syn-test-freelist)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-nf-state-freelist 2 nf-s*))
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
          (display-nf-state nf-s)
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
    (define s* (compile-nf-state-wild 2 nf-s*))
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
          (display-nf-state nf-s)
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
    (define s* (compile-nf-state-wild 2 nf-s*))
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
          (display-nf-state nf-s)
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
(define nfs-w (compile-nf-state-wild 2 nf))
(define nfs-f (compile-nf-state-freelist 2 nf))


#;(define-language struct-lang
  #:grammar heap-struct
  #:expression interaction #:size 3
  #:context state #:size 6
  #:link (lambda (e c) (cons (compile-nf-state-wild c) e))
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
  #:compile (lambda (x) (compile-nf-state-freelist 2 x)))



; looking for some heap-struct.state nf and heap-model.action a s.t.
; target behavior = (interpret-action a (compile s))
; find a target behavior (s+) s.t. no nf-new is equivalent
(define (test-hs-compiler)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-nf-state-freelist 2 nf-s*))
    (define a* (heap-model action 3))
    (define s+* (interpret-action a* s*))
    (define nf-new* (heap-struct state 4))
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
          (display-nf-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)))))


(define (test-compiler)
  (begin
    (define nf-s* (heap-struct state 4))
    (define s* (compile-nf-state-freelist 2 nf-s*))
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
          (display-nf-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "State+:")
          (display-state s+)
          (displayln "New State+:")
          (display-nf-state nf-s+)))))


    


(define (cc-hs-compiler)
  (display-changed-component (find-changed-component heap-struct-ss-compiler) displayln))

(define (wc-hs-compiler)
  (display-changed-component (find-weird-component heap-struct-ss-compiler) displayln))
