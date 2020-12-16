#lang seec
(set-bitwidth 4)
(require racket/format)
(require racket/contract)
(provide (all-defined-out))
(require (file "heap.rkt"))
;
; Shadow-Heap models to work with heap-model from heap.rkt
;
;

;; This shadow model does away with the freelist,
;; instead representing the heap as an infinitely growing list of payload
(define-grammar no-freelist
  (pointer ::= natural null)
  (offset ::= natural)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer)
  (payload ::= list<value> empty)
  (cell ::= nnvalue null (pointer offset))
  (buf ::= list<cell>)
  (heap ::= list<payload>)
  (state ::= (buf heap)))


(define empty-payload
  (heap-model (cons null (cons null nil))))

; TODO: maybe limit free to offset 0? 
(define (no-freelist-free h hl)
  (match hl
    [(no-freelist (p:pointer o:offset))
     (replace h p (no-freelist empty))]))

(define (no-freelist-alloc h)
  (let* ([l (length h)]
         [h+ (snoc h empty-payload)])
    (cons (no-freelist ,l) h+)))

; return the value at location hl in h
(define (no-freelist-read h hl)
  (match hl
    [(no-freelist (p:pointer o:offset))
     (let* ([pl (nth h p)]
            [val (nth pl o)])
     val)]))

; write val at location hl in h
(define (no-freelist-write h hl val)
  (match hl
    [(no-freelist (p:pointer o:offset))
     (let* ([pl (nth h p)]
            [pl+ (replace pl o val)]
            [h+ (replace h p pl+)])
       h+)]))




;; heap-model.action -> no-freelist.state -> no-freelist.state
(define (no-freelist-action a s)
  (match s
    [(no-freelist (b:buf h:heap))
      (match a
        [(heap-model (free hbl:buf-loc))
         (let* ([hl (nth b hbl)]
                [h+ (no-freelist-free h hl)])
           (no-freelist (,b ,h+)))]
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

  
