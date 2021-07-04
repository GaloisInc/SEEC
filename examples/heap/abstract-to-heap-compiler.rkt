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
(require (file "abstract-lang.rkt"))
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
(define/debug (pick-one-from l)
  (define/debug (pick-one-from+ l1 l2)
    (if (equal? (length l1) 1)
        (cons (car l1) l2)
        (if (nondet!) ; pick head
            (cons (car l1) (append (cdr l1) l2))
            (pick-one-from+ (cdr l1) (cons (car l1) l2)))))
  (if (empty? l)
      (assert #f)
      (pick-one-from+ l (list ))))
    

; n is the desired size of the concrete heap (in block)
; m is the number of blocks in the abstract heap
; Freelist blocks contain the previous block in the freelist, at address - (+ n 1).
; Since 1 cannot be a previous block, -1 is used to indicate free blocks outside of the freelist
(define/debug (generate-permutation n m)
  (define/debug #:suffix (generate-permutation+ n sel fh acc)
    (if (equal? n 0)
        (if (empty? sel)
            acc
            (assert #f))
        (if (nondet!) ; either empty or one block from sel
            (if (nondet!); if true, block is in freelist, otherwise empty
                (generate-permutation+ (- n 1) sel n (cons (if fh (- fh) #f) acc)) ; 
                (generate-permutation+ (- n 1) sel fh (cons -1 acc)))
            (let* ([vl (pick-one-from sel)])
              (generate-permutation+ (- n 1) (cdr vl) fh (cons (car vl) acc))))))
  (if (or (< n m)
          (<= m 0))
      (assert #f)
      (let* ([sel (list-up-to (- m 1))])
        (generate-permutation+ n sel #f (list )))))  

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
  ; fl-back is the backward pointer in the fl, where the forward pointer is included in the list
  ; cur-pos is the difference between full-p and p (current index)
  ; fl-head is the head of the freelist
  (define/debug (compile-abs-heap+ full-ah full-p p fl-back cur-pos fl-head)
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
               [tlflh (compile-abs-heap+ full-ah full-p (cdr p) fl-back+ (+ cur-pos 1) flh)]
               [tl (car tlflh)]
               [flh (cdr tlflh)])
          (cons (append hd tl) flh))))
  (compile-abs-heap+ ah p p (heap-model null) 0 (heap-model null)))



(define/debug (compile-abs-buf ab p)
  (match ab
    [(abstract-model nil)
     (heap-model nil)]
    [(abstract-model (cons v:value ab+:buf))
     (let* ([v+ (abs-value-to-value (update-abs-p-value v p))]
            [ab++ (compile-abs-buf ab+ p)])
       (heap-model (cons ,v+ ,ab++)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (display-weird-abstract-to-heap witness)
  (display-weird-behavior witness
                           #:display-expression display-abs-state
                           #:display-behavior display-state))

(define (display-changed-abstract-to-heap witness)
  (display-changed-behavior witness
                            #:display-source-expression display-abs-state
                            #:display-target-expression (lambda (s) (display-state (make-state-struct s)))
                            #:display-source-behavior display-abs-state
                            #:display-target-behavior display-state))



(define (display-abstract-to-heap witnesses)
  (if witnesses     
      (let* ([lwl-abstract (unpack-language-witness (first witnesses))]
             [lwl-heap (unpack-language-witness (second witnesses))])
        (displayln "State: ")
        (display-abs-state (first lwl-abstract))
        (display "... steps, under interaction ")
        (display (second lwl-abstract))
        (displayln ", to state: ")
        (display-abs-state (fourth lwl-abstract))
        (display "... and compiles to ")
        (display-state (make-state-struct (first lwl-heap)))
        (displayln "... with emergent behavior: ")
        (display-state (fourth lwl-heap)))
      (displayln "No changed behavior found")))

; begin with a default permutation
(define p-test (list 1 -1 0 -1))



; compile abs.state into a set of heap.state-con with a freelist
(define/debug #:suffix (compile-abs-into-heap hl s)
  (match s
    [(abstract-model (ab:buf ah:heap))
     (let* ([ahl (s-length ah)]
            [p (generate-permutation hl ahl)]
            [hp+ (compile-abs-heap ah p)]
            [b+ (compile-abs-buf ab p)])
       (heap-model (,b+ ,(car hp+) ,(cdr hp+))))]))

(define/debug #:suffix (compile-abs-into-heap-nd hl s)
    (let*-values
        ([(s* nondet*) (capture-nondeterminism #:nondet #t (compile-abs-into-heap hl s))])
      s*))

; the permutation generated will have a FL that is stricly increasing
(define pfl-test1 (list 1 -4 0 #f))
(define pfl-test2 (list -2 #f 1 0))
(define pfl-test3 (list #f 1 -1 0))

(define pfl-testbad1 (list 1 #f 0 -2)) ; this can't be generated by generate-permutation

(define/debug #:suffix (test-abs-into-heap p s)
  (match s
    [(abstract-model (ab:buf ah:heap))
     (let* ([hp+ (compile-abs-heap ah p)]
            [b+ (compile-abs-buf ab p)])
       (heap-model (,b+ ,(car hp+) ,(cdr hp+))))]))

(define dfl-ad++ (test-abs-into-heap p-test ad++))
(define dfl-ad1++ (test-abs-into-heap pfl-test1 ad++))
(define dfl-ad2++ (test-abs-into-heap pfl-test2 ad++))
(define dfl-ad3++ (test-abs-into-heap pfl-test3 ad++)) 
(define dfl-adbad1++ (test-abs-into-heap pfl-testbad1 ad++)) 

; Values av and v are equivalent in heap ah and h UP TO n steps
; #t if run out of fuel
(define (bounded-equiv-val ah h n av v)
  (match av
    [(abstract-model N)
     (match v
       [(heap-model null)
        #t]
       [(heap-model any)
        #f])]
    [(abstract-model (P am:natural s:selector))
     (match v
       [(heap-model m:natural)
        (if (<= n 0)
            #t
            (let*
                ([av+ (abs-read-heap ah av)]
                 [v+ (nth h m)])              
              (bounded-equiv-val ah h (- n 1) av+ v+)))]
       [(heap-model any)
        #f])]
    [(abstract-model ai:nnvalue)
     (match v
       [(heap-model i:nnvalue)
        (equal? ai i)]
       [(heap-model any)
        #f])]
    [(abstract-model any) ; e.g. P -1 a
     #f]))
         


; buffers ab and b are equivalent in heap ah and h UP TO n steps
(define (bounded-equiv-buf ah h n ab b)
    (match ab
      [(abstract-model nil)
       (match b
         [(heap-model nil) #t]
         [(heap-model any) #f])]
      [(abstract-model (cons av:any ab+:any))
       (match b
         [(heap-model (cons v:any b+:any))
          (and (bounded-equiv-val ah h n av v)
               (bounded-equiv-buf ah h n ab+ b+))]
         [(heap-model nil) #f])]))

; buffers are equivalent up to n pointer unfolding, and heap layout is expected (i.e. series of block of size 2)
(define/debug (bounded-equiv-state n)
  (lambda (as s)
    (match as
      [(abstract-model E)
       #f]
      [(abstract-model (ab:any ah:any))
       (and
        (valid-heap? (state->heap s))
        (bounded-equiv-buf ah (state->heap s) n ab (state->buf s)))])))


(define fixed-p (list 1 #f 0))
(define dfl-ad-fixed-p (test-abs-into-heap fixed-p astate))

(define smallfixed-p (list #f 0))
(define dfl-ad-smallfixed-p (test-abs-into-heap smallfixed-p asmallstate))
(define dfl-ad-demofixed-p (test-abs-into-heap smallfixed-p ademostate))

(define small-fixed-p (make-state-struct dfl-ad-smallfixed-p))
(define demo-fixed-p (make-state-struct dfl-ad-demofixed-p))



(define-compiler fixed-permutation-to-heap
  #:source abstract-lang
  #:target heap-lang
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal?
  #:compile (lambda (as) (test-abs-into-heap fixed-p as)))

(define-compiler small-fixed-permutation-to-heap
  #:source abstract-lang
  #:target heap-lang
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal?
  #:compile (lambda (as) (test-abs-into-heap smallfixed-p as)))

(define-compiler abstract-to-heap
  #:source abstract-lang
  #:target heap-lang
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation equal? 
  #:compile (lambda (as) (compile-abs-into-heap-nd 2 as)))


; #f
(define (atest0) (find-changed-component small-fixed-permutation-to-heap
                                          #:source-expression asmallstate))

; 
(define (atest1) (display-abstract-to-heap
                  (find-changed-component fixed-permutation-to-heap
                                         #:source-expression astate)))

(define (atest2)
  (let* ([sv (make-symbolic-abstract-state)])
    (display-abstract-to-heap
     (find-changed-component small-fixed-permutation-to-heap
                             #:source-expression (car sv)))))

(define i-test0 (heap-model (cons (decr 1) (cons (free 2) nil)))) ; from demo0
(define i-test1 (heap-model (cons (copy 1 3) (cons (free 3) nil))))  ; access to a block which has been freed

(define a-test0 (heap-model (write 1 3)))

(define as+t1 (abs-interpret-interaction i-test1 ademostate))

; Call query q with an abstract heap schema
(define (with-heap-schema q)
  (let* ([assert-store (asserts)]
         [as* (make-symbolic-abstract-state)])
    (let*-values ([(p* nondet*) (capture-nondeterminism #:nondet #t (generate-permutation 2 1))])
      (let* ([s* (test-abs-into-heap p* (car as*))]
             [w (q s*)])
        (clear-asserts!)
        (for-each (lambda (arg) (assert arg)) assert-store)
        w))))
