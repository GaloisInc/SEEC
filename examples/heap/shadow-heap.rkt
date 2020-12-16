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

;; This shadow model uses a list of pairs of an address and a payload
(define-grammar heap-list
  (pointer ::= natural null)
  (nnvalue ::= integer)
  (value ::= nnvalue pointer)
  (payload ::= list<value>)
  (cell ::= (V nnvalue) null (P payload))
  (heap ::= list<cell>))


(define empty-payload
  (heap-model (cons null (cons null nil))))



   
;; heap-model.action -> heap-list.heap -> heap-list.heap
(define (interpret-hl-action a h)
      (match a
        [(heap-model (free bl:buf-loc))
         (replace h bl (heap-list null))]
        [(heap-model (alloc bl:buf-loc n:natural))
         (replace h bl empty-payload)]
        [(heap-model (set bl:buf-loc val:nnvalue))
         (replace h bl val)]
        [(heap-model (read bl:buf-loc hl:heap-loc))
         (let* ([])
           h)]
        [(heap-model (write hl:heap-loc bl:buf-loc))
         (let* ([])
           h)]))
        
;; heap-model.interaction -> heap-list.heap -> heap-list.heap
(define (interpret-hl-interaction i h)
  (match i
    [(heap-model (a:action i+:interaction))
     (interpret-interaction i+ (interpret-action a h))]
    [(heap-model nop)
     h]))

  
