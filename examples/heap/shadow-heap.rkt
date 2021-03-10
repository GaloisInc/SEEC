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
    (display "Done nf-test2+")
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
