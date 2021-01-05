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
(define-grammar no-freelist
  (pointer ::= (natural natural) null)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer)
  (payload ::= list<value> empty)
  (buf ::= list<value>)
  (heap ::= list<payload>)
  (state ::= (buf heap)))


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

