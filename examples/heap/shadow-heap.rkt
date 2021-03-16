#lang seec
(set-bitwidth 4)

(require racket/format)
(require seec/private/util)
(require seec/private/monad)

;(require racket/contract)
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
  (payload ::= list<value>)
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
     (replace h p (no-freelist nil))]))

(define (no-freelist-alloc h)
  (let* ([l (length h)]
         [h+ (enqueue h empty-payload)])
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
         (do v <- (nth h l)
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
  #:link snoc
  #:evaluate (uncurry no-freelist-interaction))


(define-language no-freelist-ss-lang
  #:grammar no-freelist
  #:expression action #:size 2
  #:context state #:size 8 #:where no-freelist-valid-state
  #:link snoc
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
(define nf+ (no-freelist-action aa0 nf))
(define nf++ (no-freelist-action aa1 nf+))
(define nf+3* (no-freelist-action af0 nf++))
(define nf+4* (no-freelist-action af1 nf+3*))


(define nf+3 (no-freelist-action as nf++))
(define nf+4 (no-freelist-action aw nf+3))
(define nf+5 (no-freelist-action ar nf+4))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMBOLIC TESTING no-freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define o0* (no-freelist observation 2))
(define h0* (no-freelist buf 5))

; trying to synthesize a no-freelist.state which is the same as a concrete state
; works in 2.9s (now 18s????, 03/10 [7.5] 20s)
(define (nf-test0)
  (begin
;    (define b0* (no-freelist buf 4))
;    (define h0* (no-freelist heap 5))
;    (define s1* (no-freelist (,b0* ,h0*)))
    (define s1* (no-freelist state 7))
    ;    (assert (no-freelist-valid-state s1*))
    ;    (define sol (solve (assert (equal? s1* (no-freelist-init 4)))))
;    (define concr (no-freelist-init 4))
    (define concr nf+5)
    (define sol (solve (assert (equal? s1* concr))))
    (define s1 (concretize s1* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-nf-state s1)
    (displayln "Ref:")
    (display-nf-state concr)               
    (display "Equal to concr? ")
    (displayln (equal? s1 concr))
    (display "Done nf-test0 ")
    ))
;(nf-test0)


; Trying to synthesize a state which is shallowly equal to a concrete heap-model.state
; works in 3s (mar 5), 19s on mar 10 [7.5]
; Note that this could be trivially solved by having s1*'s heap be all pointers
(define (nf-test1)
  (begin
;    (define b0* (no-freelist buf 4))
;    (define h0* (no-freelist heap 5))
;    (define s1* (no-freelist (,b0* ,h0*)))
    (define s1* (no-freelist state 7))
;    (assert (no-freelist-valid-state s1*))
    (define sol (solve (assert (shallow-nf-state-eq s1* d+5))))
    (define s1 (concretize s1* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-nf-state s1)
    (display "Shallow eq: ")
    (displayln (shallow-nf-state-eq s1 d+5))
    (display "Deep eq: ")
    (displayln (deep-nf-state-eq s1 d+5))
    (display "Done nf-test1 ")
    ))

; Trying to synthesize a heap-model.state which is shallowly equal to a concrete no-freelist.state
; works in 5.1s (19s on mar 5)
; 
(define (nf-test1+)
  (begin
    (define s1* (heap-model state 7))
    (assert (valid-state 3 s1*))
    ;    (assert (no-freelist-valid-state s1*))
    ;    (define sol (solve (assert (equal? s1* (no-freelist-init 4)))))
;    (define concr (no-freelist-init 4))
    (define concr nf+5)
    (define sol (solve (assert (shallow-nf-state-eq concr s1*))))
    (define s1 (concretize s1* sol))
    (clear-asserts!)
    (displayln "Synthesized State:")
    (display-state s1)
    (displayln "Concrete State:")
    (display-nf-state concr)
    (display "Shallow eq: ")
    (parameterize ([debug? #f])      
      (displayln (shallow-nf-state-eq concr s1)))
    (display "Deep eq: ")
    (parameterize ([debug? #f])      
      (displayln (deep-nf-state-eq concr s1)))
    (display "Done nf-test1+")))


;Trying to synthesize a state which is equivalent to a concrete heap-model.state
; works in 100s (3/9) 29s (3/10 on racket 7.5)
(define (nf-test2)
  (begin
    (define s2* (no-freelist state 7))
    ;    (assert (no-freelist-valid-state s1*))
    ;    (define sol (solve (assert (equal? s1* (no-freelist-init 4)))))
;    (define concr (no-freelist-init 4))
    (define concr d+4*)
    (define sol (solve (assert (deep-nf-state-eq s2* concr))))
    (define s2 (concretize s2* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-nf-state s2)
    (displayln "Ref:")
    (display-state concr)
    (display "Deep eq: ")
    (displayln (deep-nf-state-eq s2 concr))
    (display "Done nf-test2 ")
    ))

;Trying to synthesize a heap-model.state which is equivalent to a concrete no-freelist.state
; works in 18 s (3/10 on 7.5)
(define (nf-test2+)
  (begin
    (define s2* (heap-model state 7))
    (assert (valid-state 3 s2*))
    ;    (assert (no-freelist-valid-state s1*))
    ;    (define sol (solve (assert (equal? s1* (no-freelist-init 4)))))
;    (define concr (no-freelist-init 4))
    (define concr nf+5)
    (define sol (solve (assert (deep-nf-state-eq concr s2*))))
    (define s2 (concretize s2* sol))
    (clear-asserts!)
    (displayln "State:")
    (display-state s2)
    (displayln "Concrete:")
    (display-nf-state concr)
    (display "Deep eq: ")
    (displayln (deep-nf-state-eq concr s2))
    (display "Done nf-test2+ ")
    ))

; synthesize state, interaction and behavior to achieve a certain behavior (obs = 5)
; works in 32s (3/10 7.5)
(define (nf-test3)
  (begin
    (define s3* (no-freelist state 6))
    (define i3* (no-freelist interaction 4))
    (define o3* (no-freelist observation 2))
    (define d3+* (no-freelist-interaction i3* s3*))
    (define beh3* (no-freelist-observation o3* d3+*))
    (define sol (solve (assert (equal? beh3* 5))))
    (define s3 (concretize s3* sol))
    (define d3+ (concretize d3+* sol))
    (define i3 (concretize i3* sol))
    (define o3 (concretize o3* sol))
    (define beh3 (concretize beh3* sol))
    (displayln "State:")
    (display-nf-state s3)
    (displayln "Interaction:")
    (displayln i3)
    (displayln "Observation:")
    (displayln o3)
    (displayln "Behavior:")
    (displayln beh3)))


; 113s (3/11)
(define (nf-test4-)
  (begin
    (define nfs* (no-freelist state 6))
    (define s* (heap-model state 9))
    (assert (valid-state 3 s*))
    (define sol (solve (assert (deep-nf-state-eq nfs* s*))))
    (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (define nfs (concretize nfs* sol))
          (define s (concretize s* sol))
          (displayln "NF State:")
          (display-nf-state nfs)
          (displayln "State:")
          (display-state s)
          (display "Done nf-test4- ")))))
    
(define (nf-test4)
  (begin
    (define nfs* (no-freelist state 6))
    (define s* (heap-model state 9))
    (assert (valid-state 3 s*))
    (assert (deep-nf-state-eq nfs* s*))
    (define a* (heap-model action 2))
    (define nfs+* (no-freelist-action a* nfs*))
    (define s+* (interpret-action a* s*))
    (define sol (solve (assert (not (deep-nf-state-eq nfs+* s+*)))))
        (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (define nfs (concretize nfs* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define nfs+ (concretize nfs+* sol))
          (define s+ (concretize s+* sol))
          (displayln "NF State:")
          (display-nf-state nfs)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "NF State+:")
          (display-nf-state nfs+)
          (displayln "State+:")
          (display-state s+)
          (display "Done nf-test4 ")))))


(define (nf-test4-compiled)
  (begin
    (define nfs* (no-freelist state 6))
    (assert (no-freelist-valid-state nfs*))
    (define s* (compile-nf-state-wild 2 nfs*))
;    (assert (valid-state 3 s*)) ; should be taken care of by the assert on nfs*
    (define a* (heap-model action 2))
    (define nfs+* (no-freelist-action a* nfs*))
    (define s+* (interpret-action a* s*))
    (define sol (solve (assert (not (deep-nf-state-eq nfs+* s+*)))))
        (if (unsat? sol)
        (displayln "UNSAT")
        (begin
          (define clist (concretize (list nfs* s* a* nfs+* s+*) sol))
          (define nfs (first clist))
          (define s (second clist))
          (define a (third clist))
          (define nfs+ (fourth clist))
          (define s+ (fifth clist))
          (displayln "NF State:")
          (display-nf-state nfs)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "NF State+:")
          (display-nf-state nfs+)
          (displayln "State+:")
          (display-state s+)
          (displayln "Deep EQ?")
          (parameterize ([debug? #t])      
            (displayln (deep-nf-state-eq nfs+ s+)))
          (display "Done nf-test4-compiled ")))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; COMPILING  no-freelist into heap-model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; no-freelist.value -> heap-model.value
(define (compile-nf-value v)
  (match v
    [(no-freelist (l:natural o:natural)) ; heap loc: l * (word size) + o + 2
     (heap-model ,(+ (* l 4) (+ o 2)))]   ; NOTE: if we wanted variable size chunks, we would need the heap here and keep the size of empty chunks
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
    [(no-freelist nil)
     (heap-model (cons 0 (cons 2 (cons null (cons null nil)))))]
    [(no-freelist l:list<value>)
     (let* ([v1 (compile-nf-value (head l))]
            [v2 (compile-nf-value (head (tail l)))])
       (heap-model (cons 1 (cons 2 (cons ,v1 (cons ,v2 nil))))))]))


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



(define (make-wild n)
  (if (equal? n 0)
      (heap-model nil)
      (let* ([size (- (* n 4) 2)]
             [payload (repeat (heap-model 0) size)])
        (heap-model (cons 0 (cons ,size ,payload))))))

; n is the size (in block) of the resulting heap.
;; natural -> no-freelist.heap -> heap-model.heap)
(define (compile-nf-heap-wild n h)
  (if (< n 0) #f
  (match h
      [(no-freelist nil)
       (make-wild n)]
      [(no-freelist (cons v:payload h+:heap))
       (let* ([v+ (compile-nf-payload v)]
              [hp (compile-nf-heap-wild (- n 1) h+)])
         (append v+ hp))])))

;;  natural -> no-freelist.state -> heap-model.state
(define (compile-nf-state-wild n s)
  (match s
    [(no-freelist (b:buf h:heap))
     (let* ([b+ (compile-nf-buf b)]
            [h+ (compile-nf-heap-wild n h)])
       (heap-model (,b+ ,h+ null)))]))


(define (head-or-null l)
  (match l
    [(no-freelist nil)
     (no-freelist null)]
    [(no-freelist (cons hd:any any))
     hd]))
     

;; Trying to compile a no-freelist into a heap with a freelist.
; input: a partial heap, the index into the heap (number of blocks), a stack of freelist block (list<natural>) 
; Returns: a partial heap and backward pointer 
(define/debug #:suffix (compile-nf-heap-freelist+ h total-block curr-block bwd)
  (match h
    [(no-freelist nil)
     (let* ([wild-size (- total-block curr-block)]
            [wild (if (< 0 wild-size)
                      (make-wild wild-size)
                      (heap-model nil))])
       (cons wild (heap-model null)))]
    [(no-freelist (cons nil h+:heap)) ; free block
     (let* ([p-addr (+ (* curr-block 4) 2)]
            [ret (compile-nf-heap-freelist+ h+ total-block (+ curr-block 1) (heap-model ,p-addr))]
            [ret-h (car ret)]
            [ret-fwd (cdr ret)]
            [new-h (heap-model (cons 0 (cons 2 (cons ,ret-fwd (cons ,bwd ,ret-h)))))])
            (cons new-h (heap-model ,p-addr)))]
    [(no-freelist (cons v:payload h+:heap)) ; non-free block
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
    [(no-freelist (b:buf h:heap))
     (let* ([b+ (compile-nf-buf b)]
            [ret (compile-nf-heap-freelist n h)]
            [ret-h (car ret)]
            [ret-p (cdr ret)])
       (heap-model (,b+ ,ret-h ,ret-p)))]))

(define (test-freelist s)
  (parameterize ([debug? #t])
    (compile-nf-state-freelist 2 s)))

;; compare nnvalues out of shadow-heap.value and heap-model.value
;; returns def if nf-v is a non-null pointer compared to an integer
(define/debug #:suffix (shallow-nf-val-eq+ nf-v v def)  
    (begin
      (match nf-v
        [(no-freelist nf-i:integer)
         (match v
           [(heap-model i:integer)
            (equal? nf-i i)]
           [(heap-model any)
            #f])]
        [(no-freelist null)
         (match v
           [(heap-model null)
            #t]
           [(heap-model any)
            #f])]
        [(no-freelist (l:natural o:natural))
         (match v
           [(heap-model null)
            #f]
           [(heap-model any)
            def])])))
 
(define shallow-nf-val-eq
  (lambda (nf-v
           v
           #:default [def #t])
    (shallow-nf-val-eq+ nf-v v def)))

;; shallow (compare non-pointer value) buffer equality
(define/debug #:suffix (shallow-nf-buf-eq nf-b b)
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
             (shallow-nf-val-eq nf-v v)
             (shallow-nf-buf-eq nf-b+ b+))]
           [(heap-model any)
            #f])])))

;; shallow (buffer only) equality
(define/debug #:suffix (shallow-nf-state-eq nf-s s)
    (begin
      (match nf-s
        [(no-freelist (nf-b:buf any))
         (match s
           [(heap-model (b:buf any any))
            (shallow-nf-buf-eq nf-b b)])])))

;; compare the value in buf zero w
(define/debug #:suffix (buf-z-nf-deep-eq nf-s s)
  (match nf-s
    [(no-freelist (nf-b:buf nf-h:heap))
     (match s
       [(heap-model (b:buf h:heap any))
        (do nfb-z <- (opt-nth nf-b 0)
            b-z <- (opt-nth b 0)
            (deep-nf-val-eq 10 nf-h h nfb-z b-z))])]))


;; compare the value in buf zero w
(define/debug #:suffix (buf-z-nf-eq nf-s s)
  (match nf-s
    [(no-freelist (nf-b:buf any))
     (match s
       [(heap-model (b:buf any any))
        (do nfb-z <- (opt-nth nf-b 0)
            b-z <- (opt-nth b 0)
            (shallow-nf-val-eq nfb-z b-z #:default #f))])]))






;; Deep equality (i.e. heap equality, following pointers), fuel is needed for symbolic reasoning
(define max-fuel 5)

; no-freelist.heap-loc: (l o)
; heap-model.heap-loc: n
; this may fail, but it is caught in eq
(define/debug #:suffix (deep-nf-pointer-eq+ fuel nf-h h l o n)
  (if (equal? fuel 0)
      #t
      (do nf-pl <- (opt-nth nf-h l)
          nf-v <- (opt-nth nf-pl o)
          v <- (opt-nth h n)
          (deep-nf-val-eq (- fuel 1) nf-h h nf-v v))))

(define/debug #:suffix (deep-nf-pointer-eq fuel nf-h h nf-p p)               
;  (displayln "deep-nf-pointer-eq")
  (match nf-p
    [(no-freelist (l:natural o:natural))
     (match p
       [(heap-model n:natural)
        (let ([r (deep-nf-pointer-eq+ fuel nf-h h l o n)])
            (if (failure? r)
                #f
                r))]
       [(heap-model any)
        #f])]
    [(no-freelist null)
     (match p
       [(heap-model null)
        #t]
       [(heap-model any)
        #f])]))



;; compare nnvalues out of shadow-heap.value and heap-model.value
(define/debug #:suffix (deep-nf-val-eq fuel nf-h h nf-v v)
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
(define/debug #:suffix (deep-nf-buf-eq nf-h h nf-b b)
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
(define/debug #:suffix (deep-nf-state-eq nf-s s)
  (match nf-s
    [(no-freelist (nf-b:buf nf-h:heap))
     (match s
       [(heap-model (b:buf h:heap any))
        (deep-nf-buf-eq nf-h h nf-b b)])]))

(define/debug #:suffix (compare-payload+ p l)
    (match p
      [(no-freelist (cons nv:nnvalue p+:payload))
       (match l
         [(heap-model (cons nv-l:nnvalue l+:heap))
          (and (equal? nv nv-l)
               (compare-payload+ p+ l+))]
         [any
          #f])]
       [(no-freelist (cons v:pointer p+:payload))
                     (match l
                       [(heap-model (cons v-l:pointer l+:heap))
                        ; at the moment, we ignore the pointers here
                        (compare-payload+ p+ l+)]
                       [any
                        #f])]
      [(no-freelist nil)
       (match l
         [(heap-model nil)
          #t]
         [any
          #f])]
      [any
       #f]))


(define/debug #:suffix (compare-payload p in-use l)
  (match in-use
    [(heap-model 0)
     (match p
       [(no-freelist nil)
        #t]
       [any
        #f])]
    [(heap-model 1)
     (compare-payload+ p l)]
    [any
     #f]))


;; true if the "in-use" portion of each heap is equal
(define/debug #:suffix (heap-eq nf-h h)
  (match nf-h
    [(no-freelist (cons p:payload nf-h+:heap))
     (match h
       [(heap-model (cons in-use:natural h+:heap))
        (match h+
          [(heap-model (cons size:natural h+2:heap))
           (and
            (compare-payload p in-use (first-nth size h+2))
            (heap-eq nf-h+ (skip size h+2)))]
          [any
           #f])]
       [any
        #f])]
    [(no-freelist nil)
     (match h
       [(heap-model nil)
        #t])]
    [any
     #f]))

(define (state-heap-eq nf-s s)
    (match nf-s
    [(no-freelist (nf-b:buf nf-h:heap))
     (match s
       [(heap-model (b:buf h:heap any))
        (heap-eq nf-h h)])]))



;; Testing synthesis with the no-freelist to heap-model compiler
; Make a schema for a heap-model.state with buf = 4 and state of size 8
(define b* (heap-model buf 4))
(define h* (heap-model heap 8))
(define fp* (heap-model pointer 1))
(define s* (heap-model (,b* ,h* ,fp*)))
(define st* (heap-model state 5))
; Make a schema for a no-freelist.state with buf = 4 and state of max size 5?
(define nfb* (no-freelist buf 4))
(define nfh* (no-freelist heap 5))
(define nf-s* (no-freelist (,nfb* ,nfh*)))
(define nf-st* (no-freelist state 4))

; find a context and a total interaction that evaluates to 4
(define ti* (heap-model total-interaction 4))
(define (ex1)
  (begin
    (define s+* (interpret-interaction ti* s*))
    (define nf-s+* (no-freelist-interaction ti* nf-s*))
    ;(assert (equal? nf-b* 5))
    (define sol (solve (assert (buf-z-nf-eq nf-s+* s+*))))
    (if sol
        (displayln "Success")
        (displayln "Unsat"))))


(define (ex2)
  (begin
;    (define st+* (interpret-interaction ti* st*))
;    (define nf-st+* (no-freelist-interaction ti* nfst*))
    ;(assert (equal? nf-b* 5))
    (define sol (solve (assert (buf-z-nf-eq nf-st* st*))))
    (if sol
        (displayln "Success")
        (displayln "Unsat"))))

; define a small state and no-freelist state that have equivalent values in 0th slot
; didn't terminate on 3/10
(define (ex2-mini)
  (define b-mini (heap-model state 4))
  (define nf-mini (no-freelist state 4))
  (define i-mini (heap-model action 2))
  (define b+-mini (interpret-action i-mini b-mini))
  (define nf+-mini (no-freelist-action i-mini nf-mini))
  (define sol (solve (assert (buf-z-nf-eq nf+-mini b+-mini))))
  (if sol
      (displayln "Success")
      (displayln "Unsat")))
  
;(ex2-mini)
#;(find-changed-component nf-to-heap-compiler
                        #:source-context nfs*
                        #:target-context s*)

(define-compiler nf-to-heap-compiler
  #:source no-freelist-lang
  #:target heap-lang
  #:behavior-relation deep-nf-state-eq ;buf-z-nf-eq
  #:context-relation shallow-nf-state-eq
  #:compile (lambda (x) x))


(define-compiler nf-to-heap-ss-compiler
  #:source no-freelist-ss-lang
  #:target heap-ss-lang
  #:behavior-relation deep-nf-state-eq ;buf-z-nf-eq
  #:context-relation shallow-nf-state-eq
  #:compile (lambda (x) x))

; 1/11 Did not changed changed component
(define (fsyn-ex1)
  (display-changed-component
   (find-changed-component nf-to-heap-ss-compiler)
   displayln))


(define (test-cb-c concr-n concr-s)
  (display-changed-component
   (find-changed-component nf-to-heap-compiler #:source-context concr-n #:target-context concr-s)
   displayln))


;(define (syn-ex1)
;  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Testing with nf-to-heap 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-language new-nf-lang
  #:grammar no-freelist
  #:expression state #:size 6
  #:context interaction #:size 4
  #:link cons
  #:evaluate (uncurry no-freelist-interaction))

(define-compiler new-nf-to-heap
  #:source new-nf-lang
  #:target new-heap-lang
  #:behavior-relation state-heap-eq;deep-nf-state-eq ;buf-z-nf-eq
  #:context-relation equal?
  #:compile (lambda (x) compile-nf-state-wild 2 x))



(define-language new-nf-ss-lang
  #:grammar no-freelist
  #:expression state #:size 5
  #:context action #:size 3
  #:link cons
  #:evaluate (uncurry no-freelist-interaction))

(define-compiler new-nf-to-ss-heap
  #:source new-nf-ss-lang
  #:target new-heap-ss-lang
  #:behavior-relation deep-nf-state-eq ;buf-z-nf-eq
  #:context-relation equal?
  #:compile (lambda (x) compile-nf-state-wild 2 x))


(define (size-two-payload p)
  (let* ([size (length p)])
    (or (equal? size 0)
        (equal? size 2))))

(define (size-two-heap h)
  (match h
    [(no-freelist nil)
     #t]
    [(no-freelist (cons p:payload h+:heap))
     (and (size-two-payload p)
          (size-two-heap h+))]))

(define (size-two-state s)
  (match s
    [(no-freelist (b:buf h:heap))
     (size-two-heap h)]))

; this should be unsat
(define (new-heap-syn-test)
  (begin
    (define nf-s* (no-freelist state 8))
    (assert (size-two-state nf-s*)) ; at the moment, we only compile states with block size 2
    (define s* (compile-nf-state-wild 2 nf-s*))
    (define sol (solve (assert (not (state-heap-eq nf-s* s*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (displayln "NF-state:")
          (display-nf-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Heap equal?: ")
          (parameterize ([debug? #t]) (state-heap-eq nf-s s))))))

(define (new-heap-syn-test+)
  (begin
    (define nf-s* (no-freelist state 8))
    (define s* (compile-nf-state-wild 2 nf-s*))
    (define sol (solve (assert (state-heap-eq nf-s* s*))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (displayln "NF-state:")
          (display-nf-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Heap equal?: ")
          (parameterize ([debug? #t]) (state-heap-eq nf-s s))))))


; find an action that breaks state-heap-eq
(define (new-heap-syn-test2)
  (begin
    (define nf-s* (no-freelist state 4))
    (define s* (compile-nf-state-wild 2 nf-s*))
    (assert (size-two-state nf-s*))
    (define a* (heap-model action 3)) 
    (define nf-s+* (no-freelist-action a* nf-s*))
    (define s+* (interpret-action a* s*))
    (define sol (solve (assert (not (state-heap-eq nf-s+* s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define nf-s+ (concretize nf-s+* sol))
          (define s+ (concretize s+* sol))
          (displayln "NF-state:")
          (display-nf-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Action: ")
          (displayln a)
          (displayln "NF-state+:")
          (display-nf-state nf-s+)
          (displayln "State+:")
          (display-state s+)
          (display "Heap equal?: ")
          (parameterize ([debug? #t]) (state-heap-eq nf-s+ s+))))))


(define (syn-freelist-length)
  (begin
    (define nf-s* (no-freelist state 4))
    (define s* (compile-nf-state-freelist 2 nf-s*))
    (define sol (solve (assert (equal? (freelist-length 3 s*) 2))))
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
    (define nf-s* (no-freelist state 4))
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


(define (new-heap-syn-break-freelist)
  (begin
    (define nf-s* (no-freelist state 6))
    (define s* (compile-nf-state-wild 2 nf-s*))
    (define a* (heap-model interaction 4)) 
    (define nf-s+* (no-freelist-interaction a* nf-s*))
    (define s+* (interpret-interaction a* s*))
    (define sol (solve (assert (not (valid-freelist-state-af 3 s+*)))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define nf-s (concretize nf-s* sol))
          (define s (concretize s* sol))
          (define a (concretize a* sol))
          (define nf-s+ (concretize nf-s+* sol))
          (define s+ (concretize s+* sol))
          (displayln "NF-state:")
          (display-nf-state nf-s)
          (displayln "State:")
          (display-state s)
          (display "Interaction: ")
          (displayln a)
          (displayln "NF-state+:")
          (display-nf-state nf-s+)
          (displayln "State+:")
          (display-state s+)
          (display "Heap equal?: ")
          (parameterize ([debug? #t]) (valid-freelist-state 3 s+))))))



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
  (state ::= list<natural>) ; list of free blocks
         )

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
          (if p 
              (freelist (free ,p))
                        #f))]
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

(define-language freelist-ss-lang
  #:grammar freelist
  #:expression action #:size 2
  #:context state #:size 3
  #:link snoc
  #:evaluate (uncurry freelist-interaction))

(define-language freelist-lang
  #:grammar freelist
  #:expression interaction #:size 4
  #:context state #:size 3
  #:link snoc
  #:evaluate (uncurry freelist-interaction))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; COMPILING heap-model to freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; heap-model.state -> (freelist.state + #f)
(define (compile-heap-to-freelist s)
  (define (compile-into-freelist h p )
    (match p
      [(heap-model null)
       (freelist nil)]
      [(heap-model n:natural)
       (let* ([new-p (nth h n)]
              [rest (compile-into-freelist h new-p)])
         (if (and new-p
                  rest)
             (freelist (cons ,n ,rest))
             #f))]))
  (match s
    [(heap-model (any h:heap p:pointer))
                 (compile-into-freelist h p)]))



; heap-model.action-hl -> Failure freelist.action
(define (compile-action-hl a)
  (match a
    [(heap-model (free h:heap-loc))
     (freelist (free ,h))]
    [(heap-model (alloc any any))
     (freelist alloc)]
    [(heap-model a:action-hl)
     *fail*]))


(define (compile-interaction-hl i)
  (match i
    [(heap-model nil)
     (freelist nil)]
    [(heap-model (cons a:action-hl i+:interaction-hl))
     (let ([af (compile-action-hl a)])
       (if (failure? af)
           (compile-interaction-hl i+)
           (freelist (cons ,af ,(compile-interaction-hl i+)))
           ))]))
     


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (display-f-state fs)
  (define (display-f-state+ fs)
    (match fs
      [(freelist nil)
       (displayln "")]
      [(freelist (cons n:natural fs+:any))
       (displayln n)
       (display-f-state+ fs+)]))
  (displayln "Freelist:")
  (display-f-state+ fs))


(define (display-hf-state sfs)
  (displayln "Full State:")
  (display-state (car sfs))
  (displayln "")
  (displayln "Freelist Shadow Model:")
  (display-f-state (cdr sfs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; TESTING freelist
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define f (freelist (cons 2 nil)))
(define f+ (freelist (cons 6 ,f)))
(define f++ (freelist (cons 10 ,f+)))

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
  (length fs))


; works!
(define (f-test0)
  (begin
    (define f0* (freelist state 4))
    (define sol (solve (assert (equal? (freelist-size f0*) 2))))
    (if sol
        (begin
          (define f0 (concretize f0* sol))
          (display-f-state f0))
        (displayln "unsat"))))

; Find a symbolic freelist equal to a concrete one
(define (f-test1)
  (begin
    (define concr f)
    (define f1* (freelist state 4))
    (define sol1 (solve (assert (equal? f1* concr))))
    (if sol1
        (begin
          (define f1 (concretize f1* sol1))
          (display-f-state f1))
        (displayln "unsat"))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Relating the heap-model freelist with the shadow freelist
;; no need for fuel since fl is a finite list
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (freelist-shadow? h f fs)
  (match fs
    [(freelist nil)
     (match f
       [(heap-model null) #t]
        [(heap-model any) #f])]
    [(freelist (cons n:natural fs+:any))
     (let* ([in-use (nth h (- f 2))]
            [size (nth h (- f 1))]
            [f+ (nth h f)])
       (and (equal? in-use (heap-model 0))
            (< 1 size)
            (equal? f n)
            (freelist-shadow? h f+ fs+)))]))

(define (freelist-state-shadow? s fs)
  (match s
    [(heap-model (any h:heap f:pointer))
     (freelist-shadow? h f fs)]))

(define heap-and-freelist-shadow? (uncurry freelist-state-shadow?))

(define-compiler heap-to-freelist
  #:source heap-hl-lang
  #:target freelist-lang
  #:behavior-relation freelist-state-shadow?
  #:context-relation freelist-state-shadow?
  #:compile compile-interaction-hl)

(define-compiler heap-to-ss-freelist
  #:source heap-ss-hl-lang
  #:target freelist-ss-lang
  #:behavior-relation freelist-state-shadow?
  #:context-relation freelist-state-shadow?
  #:compile (lambda (x) (ofail (compile-action-hl x))))



; (display-changed-component (find-changed-component heap-to-freelist) displayln)
; found write in the freelist in 61.5s
#| 
Expression ((free 2) ((write 3 2)))
 has behavior ((0 (null (-4 (0)))) (0 (2 (0 (null)))) 2)
 in source-level context ((0 (null (-4 (0)))) (0 (2 (0 (0)))) null)

Compiles to ((free 2))
 with emergent behavior (2)
 in target-level context *null* 
|#
;also found double free:
#|
Expression ((free 2))
 has behavior ((0) (0 (2 (2 (2)))) 2)
 in source-level context ((0) (0 (2 (null (null)))) 2)

Compiles to ((free 2))
 with emergent behavior (2 (2))
 in target-level context (2)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYMBOLIC TESTING df-state-shadow
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; synthesize the shadow freelist of a concrete heap-model.state
; works (34 seconds) 17s (3/10 on 7.5)
(define (df-test0)
  (begin
    (define concr d+4*)
    (define f0* (freelist state 4))
    (define sol (solve (assert (freelist-state-shadow? concr f0*))))
    (define f0 (concretize f0* sol))
    (displayln "State:")
    (display-state concr)
    (displayln "Freelist:")
    (displayln f0)
    (display "Shadows?:")
    (displayln (freelist-state-shadow? concr f0))
    (display "Done df-test0 ")
    ))


; synthesize a heap-model.state given a concrete freelist
; works in 20s (3/10 on 7.5)
(define (df-test0+)
  (begin
    (define concr f)
    (define d0* (heap-model state 6))
    (assert (valid-state 3 d0*))
    (define sol (solve (assert (freelist-state-shadow? d0* concr))))
    (define d0 (concretize d0* sol))
    (displayln "State:")
    (display-state d0)
    (displayln "Freelist:")
    (displayln concr)
    (display "Shadows?:")
    (displayln (freelist-state-shadow? d0 concr))
    (display "Done df-test0+ ")
    ))



;;;; HEAP-NO-TO-FREELIST-DEMO

(define-compiler heap-no-to-freelist
  #:source heap-hl-no-lang
  #:target freelist-lang
  #:behavior-relation freelist-state-shadow?
  #:context-relation freelist-state-shadow?
  #:compile compile-interaction-hl)

(define (demo-test) (display-changed-component (find-changed-component heap-no-to-freelist) displayln))

;(display-changed-component (find-changed-component heap-no-to-freelist) displayln)
; finds a free on a block which is too small
#|Expression ((free 2))
 has behavior ((0 (0 (null (null)))) 2)
in source-level context ((0 (0 (0 (0)))) null) |#

; correction: changing free to make sure the block is big enough
(define (interpret-free+ h f p)
  (match p
    [(heap-model n:natural)
     (do size <- (nth h (- n 1))
       (match size
         [(heap-model sz:natural)
          (if (< size 2)
              (assert #f)
          (do h+ <- (replace h (- n 2) (heap-model 0))
              h++ <- (replace h+ n f)
              h+++ <- (replace h++ (+ n 1) (heap-model null))
              (match f ; update the whole fp head to point to new head
                [(heap-model null)
               h+++]
                [(heap-model nf:natural)
                 (do h+4 <- (replace h+++ (+ nf 1) p)
                     h+4)])))]
         [_
          ;(displayln "trying to free a block which wasn't allocated")
          ;(cons f h)
          (assert #f)
          ]))]))


; break the freelist by writing to the size block directly. 
#| Expression ((free 2) ((write 0 1)))
 has behavior ((-6 (0 (null))) (0 (-6 (null (null)))) 2)
 in source-level context ((-6 (0 (null))) (0 (2 (7 (4)))) null)
|#
; etc
