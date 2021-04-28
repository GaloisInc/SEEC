#lang seec
(require seec/private/util)
(require seec/private/monad)
(require racket/format)
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
(require (file "lib.rkt"))
(require (file "heap-lang.rkt"))
(require (file "heap-abstrat-lang.rkt"))
(provide (all-defined-out))

; returns (list 0 ... n)
(define (list-up-to n)
  (define (list-up-to+ n cur)
    (if (equal? n 0)
        (cons 0 cur)
        (list-up-to+ (- n 1) (cons n cur))))    
  (if (< n 0)
      (assert #f)
      (list-up-to+ n (list ))))

; generate an integer in range n m
(define (gen-int n m)
  (define (gen-int+ n m)
    (if (equal? n m)
        m
        (if (nondet!)
            n
            (gen-int+ (+ n 1) m))))
  (if (< m n)
      (assert #f)
      (gen-int+ n m)))

; receives a non empty list, returns one of the element of the list and the list with that element removed
(define (pick-one-from l)
  (define (pick-one-from+ l1 l2)
    (if (equal? (length l1) 1)
        (cons (car l1) l2)
        (if (nondet!) ; pick head
            (cons (car l1) (append (cdr l1) l2))
            (pick-one-from+ (cdr l1) (cons (car l1) l2)))))
  (if (empty? l)
      (assert #f)
      (pick-one-from+ l (list ))))
    
      

; TODO: also generate the permutation function for pointers
; n is the desired size of the concrete heap (in block)
; m is the number of blocks in the abstract heap
; generate a permutation from 0 ... n into 0 ... m U -1
(define/debug (generate-permutation n m)
  (define/debug (generate-permutation+ n sel)
    (if (equal? n 0)
        (if (empty? sel)
            (list )
            (assert #f))
        (if (nondet!) ; if true, then block is empty, otherwise pick from sel
            (cons -1 (generate-permutation+ (- n 1) sel)) ; generate an empty block TODO: make this a freelist
            (let* ([vl (pick-one-from sel)])
              (cons (car vl) (generate-permutation+ (- n 1) (cdr vl)))))))
  (if (or (< n m)
          (<= m 0))
      (assert #f)
      (let* ([sel (list-up-to (- m 1))])
        (generate-permutation+ n sel))))

; Version of generate-permutation which also creates a (concecutive free list)
; Freelist blocks contain the previous block in the freelist, at address - (+ n 1).
; Since 1 cannot be a previous block, -1 is used to indicate free blocks outside of the freelist
(define/debug (generate-permutation-fl n m)
  (define/debug (generate-permutation-fl+ n sel fh acc)
    (if (equal? n 0)
        (if (empty? sel)
            (list )
            (assert #f))
        (if (nondet!) ; either empty or one block from sel
            (if (nondet!); if true, block is in freelist, otherwise empty
                (generate-permutation-fl+ (- n 1) sel n (cons (if fh (- fh) #f) acc)) ; 
                (generate-permutation-fl+ (- n 1) sel fh (cons -1 acc)))
            (let* ([vl (pick-one-from sel)])
              (generate-permutation-fl+ (- n 1) (cdr vl) (cons (car vl) acc))))))
  (if (or (< n m)
          (<= m 0))
      (assert #f)
      (let* ([sel (list-up-to (- m 1))])
        (generate-permutation-fl+ n sel #f (list )))))


(define (list-permute l)
  (if (empty? l)
      (list )
      (if (nondet!)
          (cons (car l) (list-permute (cdr l)))
          (assert #f))))

(define (index-of l v)
  (define (index-of+ l v i)
    (if (empty? l)
        (assert #f)
        (if (equal? (car l) v)
            i
            (index-of+ (cdr l) v (+ i 1)))))
  (index-of+ l v 0))

; update all pointers in hd
(define/debug (update-abs-p-value v full-p)
  (match v
    [(abstract-model (P n:natural s:selector))
     (let ([n+ (index-of full-p n)])
       (abstract-model (P ,n+ ,s)))]
    [(abstract-model any)
     v]))

(define/debug (update-abs-p-block hd full-p)
  (match hd
    [(abstract-model (v1:value v2:value))
     (let* ([v1+ (update-abs-p-value v1 full-p)]
            [v2+ (update-abs-p-value v2 full-p)])
       (abstract-model (,v1+ ,v2+)))]))


(define/debug (abs-value-to-value v)
  (match v
    [(abstract-model (P n:natural s:selector))
     (let ([n+ (+ (* n 4) (abs-select s 2 3))])
       (heap-model ,n+))]
    [(abstract-model N)
     (heap-model null)]
    [(abstract-model n:integer)
     (heap-model ,n)]))

(define/debug (abs-block-to-block b)
  (match b
    [(abstract-model (v1:value v2:value))
     (let* ([v1+ (abs-value-to-value v1)]
            [v2+ (abs-value-to-value v2)])       
       (heap-model (cons 1 (cons 2 (cons ,v1+ (cons ,v2+ nil))))))]))

; bwd is a pointer 
; fwd is either an integer i, in representing a fwd pointer to block # (- (- i) 1), or #f representing null (end of free list)
(define/debug (abs-free-list-block bp fwd)
  (let ([fp (if fwd
                (let* ([blocknum (- (- fwd) 1)])
                       (heap-model ,(block-addr blocknum)))
                (heap-model null))])
    (heap-model (cons 0 (cons 2 (cons ,fp (cons ,bp nil)))))))


(define (abs-empty-to-block)
  (heap-model (cons 0 (cons 2 (cons 0 (cons 0 nil))))))

(define (compile-abs-heap ah p)
  (define/debug (compile-abs-heap full-ah full-p  p)
    (if (empty? p)
        (heap-model nil)
        (let* ([id (car p)]
               [hd (if (< id 0)
                       (abs-empty-to-block)
                       (abs-block-to-block (update-abs-p-block (nth ah (car p)) full-p)))]
               [tl (compile-abs-heap full-ah full-p (cdr p))])
          (append hd tl))))
  (compile-abs-heap ah p p))


(define (compile-abs-heap-fl ah p)
  ; fl-back is the backward pointer in the fl, where the forward pointer is included in the list
  ; cur-pos is the difference between full-p and p (current index)
  ; fl-head is the head of the freelist
  (define/debug (compile-abs-heap-fl+ full-ah full-p p fl-back cur-pos fl-head)
    (if (empty? p)
        (cons (heap-model nil) fl-head)
        (let* ([id (car p)]
               [hdflbflh (if (equal? id -1)
                             (cons (cons (abs-empty-to-block) fl-back) fl-head)
                             (if (or (not id)
                                     (< id -1))                                
                                 (cons (cons (abs-free-list-block fl-back id) (heap-model ,(block-addr cur-pos)))
                                       (if (equal? fl-head (heap-model null))
                                           (heap-model ,(block-addr cur-pos))
                                           fl-head))                                     
                                 (cons (cons (abs-block-to-block (update-abs-p-block (nth ah id) full-p)) fl-back) fl-head)))]
               [hdflb (car hdflbflh)]
               [flh (cdr hdflbflh)]
               [hd (car hdflb)]
               [fl-back+ (cdr hdflb)]
               [tlflh (compile-abs-heap-fl+ full-ah full-p (cdr p) fl-back+ (+ cur-pos 1) flh)]
               [tl (car tlflh)]
               [flh (cdr tlflh)])
          (cons (append hd tl) flh))))
  (compile-abs-heap-fl+ ah p p (heap-model null) 0 (heap-model null)))



(define/debug (compile-abs-buf ab p)
  (match ab
    [(abstract-model nil)
     (heap-model nil)]
    [(abstract-model (cons v:value ab+:buf))
     (let* ([v+ (abs-value-to-value (update-abs-p-value v p))]
            [ab++ (compile-abs-buf ab+ p)])
       (heap-model (cons ,v+ ,ab++)))]))




; Compile abs.state into a set of heap.state-con
; hl is the desired length of the compiled heap in blocks (of 4 cells each)
(define/debug #:suffix (compile-abs-into-heap hl s)
  (match s
    [(abstract-model (ab:buf ah:heap))
     (let* ([ahl (length ah)]
            [p (generate-permutation hl ahl)]
            [h+ (compile-abs-heap ah p)]
            [b+ (compile-abs-buf ab p)])
       (heap-model (,b+ ,h+ null)))]))

; begin with a default permutation
(define p-test (list 1 -1 0 -1))

(define/debug #:suffix (test-abs-into-heap p s)
  (match s
    [(abstract-model (ab:buf ah:heap))
     (let* ([h+ (compile-abs-heap ah p)]
            [b+ (compile-abs-buf ab p)])
       (heap-model (,b+ ,h+ null)))]))

(define d-ad++ (test-abs-into-heap p-test ad++))


; compile abs.state into a set of heap.state-con with a freelist
(define/debug #:suffix (compile-abs-into-heap-fl hl s)
  (match s
    [(abstract-model (ab:buf ah:heap))
     (let* ([ahl (length ah)]
            [p (generate-permutation-fl hl ahl)]
            [hp+ (compile-abs-heap-fl ah p)]
            [b+ (compile-abs-buf ab p)])
       (heap-model (,b+ ,(car hp+) ,(cdr hp+))))]))

; the permutation generated will have a FL that is stricly increasing (i.e. each block will be after the other in the 
(define pfl-test1 (list 1 -4 0 #f))
(define pfl-test2 (list -2 #f 1 0))
(define pfl-test3 (list #f 1 -1 0))

(define pfl-testbad1 (list 1 #f 0 -2)) ; this can't be generated by generate-permutation-fl

(define/debug #:suffix (test-abs-into-heap-fl p s)
  (match s
    [(abstract-model (ab:buf ah:heap))
     (let* ([hp+ (compile-abs-heap-fl ah p)]
            [b+ (compile-abs-buf ab p)])
       (heap-model (,b+ ,(car hp+) ,(cdr hp+))))]))

(define dfl-ad++ (test-abs-into-heap-fl p-test ad++))
(define dfl-ad1++ (test-abs-into-heap-fl pfl-test1 ad++))
(define dfl-ad2++ (test-abs-into-heap-fl pfl-test2 ad++))
(define dfl-ad3++ (test-abs-into-heap-fl pfl-test3 ad++)) 
(define dfl-adbad1++ (test-abs-into-heap-fl pfl-testbad1 ad++)) 

