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
; generate a permutation from 0 ... n into 0 ... m U -1
; Note: use fl version to also generate the free list
(define/debug (generate-permutation n m)
  (define/debug (generate-permutation+ n sel)
    (if (equal? n 0)
        (if (empty? sel)
            (list )
            (assert #f))
        (if (nondet!) ; if true, then block is empty [but only if n is still bigger than the sel], otherwise pick from sel
            (cons -1 (generate-permutation+ (- n 1) sel)) ; generate an empty block TODO: make this a freelist
            (let* ([vl (pick-one-from sel)])
              (cons (car vl) (generate-permutation+ (- n 1) (cdr vl)))))))
  (if (or (< n m)
          (<= m 0))
      (assert #f)
      (let* ([sel (list-up-to (- m 1))])
        (generate-permutation+ n sel))))

; Trying to generate permutation without failing branches
; Assume  0 < m <= n
(define/debug (generate-permutation2 n m)
  (define/debug (generate-permutation2+ n sel)
    (if (equal? n 0)
        (list )
        (if (and
             (< (length sel) n)
             (nondet!)) ; if true, then block is empty, otherwise pick from sel
            (cons -1 (generate-permutation2+ (- n 1) sel)) ; generate an empty block TODO: make this a freelist
            (let* ([vl (pick-one-from sel)])
              (cons (car vl) (generate-permutation2+ (- n 1) (cdr vl)))))))
      (let* ([sel (list-up-to (- m 1))])
        (generate-permutation2+ n sel)))


; Version of generate-permutation which also creates a (concecutive free list)
; Freelist blocks contain the previous block in the freelist, at address - (+ n 1).
; Since 1 cannot be a previous block, -1 is used to indicate free blocks outside of the freelist
(define/debug (generate-permutation-fl n m)
  (define/debug #:suffix (generate-permutation-fl+ n sel fh acc)
    (if (equal? n 0)
        (if (empty? sel)
            acc
            (assert #f))
        (if (nondet!) ; either empty or one block from sel
            (if (nondet!); if true, block is in freelist, otherwise empty
                (generate-permutation-fl+ (- n 1) sel n (cons (if fh (- fh) #f) acc)) ; 
                (generate-permutation-fl+ (- n 1) sel fh (cons -1 acc)))
            (let* ([vl (pick-one-from sel)])
              (generate-permutation-fl+ (- n 1) (cdr vl) fh (cons (car vl) acc))))))
  (if (or (< n m)
          (<= m 0))
      (assert #f)
      (let* ([sel (list-up-to (- m 1))])
        (generate-permutation-fl+ n sel #f (list )))))


(define/debug (generate-permutation-fl2 n m)
  (define/debug #:suffix (generate-permutation-fl2+ n sel fh acc)
    (begin
      (display n)
      (displayln "IN")
    (if (equal? n 0)
        (begin
          (displayln "DONE")
          acc)
        (let ([ls (length sel)])
          (if (or (equal? ls 0) ; no more block to select
                  (and (nondet!) ; either empty or one block from sel
                       (< ls n))) ; only available if we're not behind on selecting
              (if (nondet!); if true, block is in freelist, otherwise empty
                  (begin
                    (displayln "FREEBLOCK")
                    (generate-permutation-fl2+ (- n 1) sel n (cons (if fh (- fh) #f) acc))) ;
                  (begin
                    (displayln "EMPTYBLOCK")
                    (displayln n)
                    (generate-permutation-fl2+ (- n 1) sel fh (cons -1 acc))))
              (let* ([vl (pick-one-from sel)]
                     [vla (car vl)]
                     [vlb (cdr vl)])
                (begin
                  (displayln " SELECTED")
                  (displayln vla)
                  (displayln vlb)
                  (generate-permutation-fl2+ (- n 1) vlb fh (cons vla acc)))))))))
    (let* ([sel (list-up-to (- m 1))])
      (generate-permutation-fl2+ n sel #f (list ))))
  

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

(define/debug (compile-abs-heap ah p)
  (define/debug (compile-abs-heap+ full-ah full-p  p)
    (if (empty? p)
        (heap-model nil)
        (let* ([id (car p)]
               [hd (if (< id 0)
                       (abs-empty-to-block)
                       (abs-block-to-block (update-abs-p-block (nth ah (car p)) full-p)))]
               [tl (compile-abs-heap+ full-ah full-p (cdr p))])
          (append hd tl))))
  (compile-abs-heap+ ah p p))


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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Pretty-printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (display-abstract-to-heap witnesses)
  (if witnesses     
      (let* ([lwl-abstract (unpack-language-witness (first witnesses))]
             [lwl-heap (unpack-language-witness (second witnesses))])
        (displayln "State: ")
        (display-state (make-state-struct (second lwl-abstract)))
        (display "... steps, under interaction ")
        (display (first lwl-abstract))
        (displayln ", to state: ")
        (display-state (fourth lwl-abstract))
        (display "... and compiles to ")
        (display-state (make-state-struct (second lwl-heap)))
        (displayln "... with emergent behavior: ")
        (displayln (fourth lwl-heap)))
      (displayln "No changed behavior found")))



; Compile abs.state into a set of heap.state-con
; hl is the desired length of the compiled heap in blocks (of 4 cells each)
(define/debug #:suffix (compile-abs-into-heap hl s)
  (match s
    [(abstract-model (ab:buf ah:heap))
     (let* ([ahl (s-length ah)]
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
     (let* ([ahl (s-length ah)]
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



; decompile an heap-model.state into an abstract-lang.state
;; In buffer and on the heap, natural in payloads are converted to both pointers and integers in abs
;(define (lifts-into-abs s)
;  )


; Compare an abstract state and a state
; two steps: first

; TODO: this is a placeholder
; abstract.heap -> heap.heap -> list permutations
(define (equiv-compile-abstract-heap ah h)
  (list (list 0 1) (list 1 0)))



;TODO: cons case
(define (equiv-compile-abstract-heap-real ah h)
  (match ah
    [(abstract-model nil)
     (empty-heap? h) ; no allocated block in h
     ]
    [(abstract-model (cons b:block ab+:heap))
     (match h
       [(heap-model (cons 1 (cons 2 (cons v1:value (cons v2:value h+:heap)))))
        (if #t ;(equiv-compile-block b v1 v2)
            #t 
            #f )]
       [(heap-model (cons 0 (cons 2 (cons any (cons any h+:heap)))))
        (equiv-compile-abstract-heap-real ah h+)]
       [(heap-model any)
        #f])]))


(define (equiv-compile-abstract-value p av v)
  (match av
    [(abstract-model N)
     (match v
       [(heap-model null)
        #t]
       [(heap-model any)
        #f])]
    [(abstract-model (P n:natural s:selector))
     (match v
       [(heap-model n+:natural)
        (let* ([nb (nth p n)]
               [nloc (block-addr nb)]
               [nloc+ (abs-select s nloc (+ nloc 1))])
          (equal? nloc+ n+))]
       [(heap-model any)
        #f])]
    [(abstract-model n:nnvalue)
     (match v
       [(heap-model n+:nnvalue)
        (equal? n n+)]
       [(heap-model any)
        #f])]))

; returns #t if pl contains a permutation s.t. ab equiv b
(define (equiv-compile-abstract-buf pl ab b)
  (define (equiv-compile-abstract-buf+ p ab b)
    (match ab
      [(abstract-model nil)
       (match b
         [(heap-model nil) #t]
         [(heap-model any) #f])]
      [(abstract-model (cons av:value ab+:buf))
       (match b
         [(heap-model (cons v:value b+:buf))
                      (and (equiv-compile-abstract-value p av v)
                           (equiv-compile-abstract-buf+ p ab+ b+))]
         [(heap-model nil) #f])]))
  (if (empty? pl)
      #f
      (or (equiv-compile-abstract-buf+ (car pl) ab b)
          (equiv-compile-abstract-buf (cdr pl) ab b))))


(define (equiv-compile-abstract-state as s)
  (match s
    [(heap-model (b:buf h:heap any))
     (match as
       [(abstract-model (ab:buf ah:heap))
        (let* ([pl (equiv-compile-abstract-heap ah h)]) ; p is a list of potential permutations where ah equiv h
          (equiv-compile-abstract-buf pl ab b))])]))


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
        #f])]))
         


; buffers ab and b are equivalent in heap ah and h UP TO n steps
(define (bounded-equiv-buf ah h n ab b)
    (match ab
      [(abstract-model nil)
       (match b
         [(heap-model nil) #t]
         [(heap-model any) #f])]
      [(abstract-model (cons av:value ab+:buf))
       (match b
         [(heap-model (cons v:value b+:buf))
          (and (bounded-equiv-val ah h n av v)
               (bounded-equiv-buf ah h n ab+ b+))]
         [(heap-model nil) #f])]))

; buffers are equivalent up to n pointer unfolding, and heap layout is expected (i.e. series of block of size 2)
(define/debug (bounded-equiv-state n)
  (lambda (as s)
    (match as
      [(abstract-model (ab:buf ah:heap))
       (and
        (valid-heap? (state->heap s))
        (bounded-equiv-buf ah (state->heap s) n ab (state->buf s)))])))

#|  3 possibilities for behavior relations: by less complicated to more complicated
*) equiv-buf with fuel and valid heap (with 2-sized active blocks)
*) compile-abs-into-heap, but then cannot represent all freelists
*) equiv-compile-abstract-state which generates all potential permutation of blocks on the heap (potentially want this in two passes, one that makes all permutation of active blocks, and one that removes mismatch in heap and buf)
|#

(define fixed-p (list 1 #f 0))
(define dfl-ad-fixed-p (test-abs-into-heap-fl fixed-p astate))

(define smallfixed-p (list #f 0))
(define dfl-ad-smallfixed-p (test-abs-into-heap-fl smallfixed-p asmallstate))
(define dfl-ad-demofixed-p (test-abs-into-heap-fl smallfixed-p ademostate))

(define small-fixed-p (make-state-struct dfl-ad-smallfixed-p))
(define demo-fixed-p (make-state-struct dfl-ad-demofixed-p))



(define-compiler fixed-permutation-to-heap
  #:source abstract-lang
  #:target heap-lang
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation (lambda (as s) (equal? s (test-abs-into-heap-fl fixed-p as)))
  #:compile (lambda (e) e))

(define-compiler small-fixed-permutation-to-heap
  #:source abstract-lang
  #:target heap-lang
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation (lambda (as s) (equal? s (test-abs-into-heap-fl smallfixed-p as)))
  #:compile (lambda (e) e))


(define-compiler abstract-to-heap
  #:source abstract-lang
  #:target heap-lang
  #:behavior-relation (bounded-equiv-state 3)
  #:context-relation (lambda (as s) (equal? s (compile-abs-into-heap-fl 2 as)))
  #:compile (lambda (e) e))

(define (atest0) (find-changed-component small-fixed-permutation-to-heap
                                          #:source-context asmallstate))


(define (atest1) (find-changed-component fixed-permutation-to-heap
                                          #:source-context astate))
(define (atest2) (display-abstract-to-heap
                  (find-changed-component fixed-permutation-to-heap)))

; Test how big fixed-p astate and smallfixed-p are
; smallfixed : 10 
; fixed :  > 10
(define (bench1)
  (begin
    (define bs* (heap-model state-con 10))
    (define as dfl-ad-smallfixed-p)
    (define sol (solve (assert (equal? bs* as))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (define bs (concretize bs* sol))          
          (display-state (make-state-struct bs))))))

; this takes 60ms?
(define (manual-bench0)
  (begin
    (define as dfl-ad-smallfixed-p)
    (define b0 (heap-model value 1))
    (define b1 (heap-model value 1))
    (define b2 (heap-model value 1))
    (define b3 (heap-model value 1))
    (define b* (heap-model (cons ,b0 (cons ,b1 (cons ,b2 (cons ,b3 nil))))))
    (define h0 (heap-model value 1))
    (define h1 (heap-model value 1))
    (define h2 (heap-model value 1))
    (define h3 (heap-model value 1))
    (define h4 (heap-model value 1))
    (define h5 (heap-model value 1))
    (define h6 (heap-model value 1))
    (define h7 (heap-model value 1))   
    (define h* (heap-model (cons ,h0 (cons ,h1 (cons ,h2 (cons ,h3 (cons ,h4 (cons ,h5 (cons ,h6 (cons ,h7 nil))))))))))
    (define p* (heap-model pointer 1))
    (define s* (heap-model (,b* ,h* ,p*)))
    (define sol (solve (assert (equal? s* as))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (define s (concretize s* sol))          
          (display-state (make-state-struct s))))))

; this takes 1 minutes
(define (manual-bench1)
  (begin
    (define as dfl-ad-smallfixed-p)
    (define b* (heap-model buf 5))
    (define h* (heap-model heap 9))
    (define p* (heap-model pointer 1))
    (define s* (heap-model (,b* ,h* ,p*)))
    (define sol (solve (assert (equal? s* as))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (define s (concretize s* sol))          
          (display-state (make-state-struct s))))))


; should be unsat
(define (manual-bench2)
  (begin
    (define as ademostate)
    (define s* demo-fixed-p)
    (define sol (verify (assert ((bounded-equiv-state 3) as s*))))
    (if (unsat? sol)
        (displayln "unsat")
        (displayln "sat"))))


; can we find an action that breaks the equivalence between asmallstate and s*
(define (manual-test0)
  (begin
    (define as ademostate)
    (define s* demo-fixed-p)
    (define i* (heap-model action 3))
    (define s+* (interpret-action i* s*))
    (define as+* (abs-interpret-action i* as))
    (define sol (verify (assert ((bounded-equiv-state 3) as+* s+*))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define i (concretize i* sol))
          (define s+ (interpret-action i s*))
          (define as+ (abs-interpret-action i as))
          (displayln "Over state")
          (display-abs-state as)
          (display "Action ")
          (displayln i)
          (displayln "Results in abstract.state :")
          (display-abs-state as+)
          (displayln "and heap.state :")
          (display-state s+)))))

; same but with interaction
(define (manual-test1)
  (begin
    (define as ademostate)
    (define s* demo-fixed-p)
    (define i* (heap-model interaction 4))
    (define s+* (interpret-interaction i* s*))
    (define as+* (abs-interpret-interaction i* as))
    (define sol (verify (assert ((bounded-equiv-state 3) as+* s+*))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define i (concretize i* sol))
          (define s+ (interpret-interaction i s*))
          (define as+ (abs-interpret-interaction i as))
          (displayln "Over state")
          (display-abs-state as)
          (display "Action ")
          (displayln i)
          (displayln "Results in abstract.state :")
          (display-abs-state as+)
          (displayln "and heap.state :")
          (display-state s+)))))

(define (manual-test2)
  (begin
    (define ab0 (abstract-model value 1))
    (define ab1 (abstract-model value 1))
    (define ab2 (abstract-model value 1))
    (define ab3 (abstract-model value 1))
    (define ab* (abstract-model (cons ,ab0 (cons ,ab1 (cons ,ab2 (cons ,ab3 nil))))))
    (define ablock (abstract-model block 3))
    (define ah* (abstract-model (cons ,ablock nil)))
    (define as* (abstract-model (,ab* ,ah*)))
;    (define as* (abstract-model state 6))
    (define s* (make-state-struct (test-abs-into-heap-fl smallfixed-p as*)))
    (define i* (heap-model action 3))
    (define s+* (interpret-action i* s*))
    (define as+* (abs-interpret-action i* as*))
    (define sol (verify (assert ((bounded-equiv-state 3) as+* s+*))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define i (concretize i* sol))
          (define s (concretize s* sol))
          (define as (concretize as* sol))
          (define s+ (interpret-action i s))
          (define as+ (abs-interpret-action i as))
          (displayln "Over state")
          (display-abs-state as)
          (displayln "which compiled to state")
          (display-state s)
          (display "Action ")
          (displayln i)
          (displayln "Results in abstract.state :")
          (display-abs-state as+)
          (displayln "and heap.state :")
          (display-state s+)))))

; Same as manual-test2 except with a schema as target instead of computed target, around 10x slower.
(define (manual-test3)
  (begin
    (define ab0 (abstract-model value 1))
    (define ab1 (abstract-model value 1))
    (define ab2 (abstract-model value 1))
    (define ab3 (abstract-model value 1))
    (define ab* (abstract-model (cons ,ab0 (cons ,ab1 (cons ,ab2 (cons ,ab3 nil))))))
    (define ablock (abstract-model block 3))
    (define ah* (abstract-model (cons ,ablock nil)))
    (define as* (abstract-model (,ab* ,ah*)))    
    (define b0 (heap-model value 1))
    (define b1 (heap-model value 1))
    (define b2 (heap-model value 1))
    (define b3 (heap-model value 1))
    (define b* (heap-model (cons ,b0 (cons ,b1 (cons ,b2 (cons ,b3 nil))))))
    (define h0 (heap-model value 1))
    (define h1 (heap-model value 1))
    (define h2 (heap-model value 1))
    (define h3 (heap-model value 1))
    (define h4 (heap-model value 1))
    (define h5 (heap-model value 1))
    (define h6 (heap-model value 1))
    (define h7 (heap-model value 1))   
    (define h* (heap-model (cons ,h0 (cons ,h1 (cons ,h2 (cons ,h3 (cons ,h4 (cons ,h5 (cons ,h6 (cons ,h7 nil))))))))))
    (define p* (heap-model pointer 1))
    (define ss* (heap-model (,b* ,h* ,p*)))
    (assert (equal? ss* (test-abs-into-heap-fl smallfixed-p as*)))
    (define s* (make-state-struct ss*))
    (define i* (heap-model action 3))
    (define s+* (interpret-action i* s*))
    (define as+* (abs-interpret-action i* as*))
    (define sol (verify (assert ((bounded-equiv-state 3) as+* s+*))))
    (if (unsat? sol)
        (displayln "unsat")
        (begin
          (displayln "sat")
          (define i (concretize i* sol))
          (define s (concretize s* sol))
          (define as (concretize as* sol))
          (define s+ (interpret-action i s))
          (define as+ (abs-interpret-action i as))
          (displayln "Over state")
          (display-abs-state as)
          (displayln "which compiled to state")
          (display-state s)
          (display "Action ")
          (displayln i)
          (displayln "Results in abstract.state :")
          (display-abs-state as+)
          (displayln "and heap.state :")
          (display-state s+)))))

; Same as manual-test0 but with any permutation
; TODO: change to compile-abs-into-head-fl
; Still debuging generate-permutation
(define (manual-test4)
  (begin
    (define as ademostate)
    (let*-values
     ([(s* nondet*) (capture-nondeterminism #:nondet #t (make-state-struct (compile-abs-into-heap-fl 2 as)))])
     (define i* (heap-model action 3))
     (define s+* (interpret-action i* s*))
     (define as+* (abs-interpret-action i* as))
     (define sol (verify (assert ((bounded-equiv-state 3) as+* s+*))))
     (if (unsat? sol)
         (displayln "unsat")
         (begin
           (displayln "sat")
           (define i (concretize i* sol))
           (define s (concretize s* sol))
           (define nondet (concretize nondet* sol))
           (define s+ (interpret-action i s))
           (define as+ (abs-interpret-action i as))
           (displayln "Over state")
           (display-abs-state as)
           (displayln "compiled as state")
           (display-state s)
           (display "Action ")
           (displayln i)
           (displayln "Results in abstract.state :")
           (display-abs-state as+)
           (displayln "and heap.state :")
           (display-state s+)
           (displayln "which are equivalent?")
           (displayln ((bounded-equiv-state 3) as+ s+)))))))

; like manual-test4 but using a schematic abstract state as
(define (manual-test5)
  (begin
    (define ab0 (abstract-model value 1))
    (define ab1 (abstract-model value 1))
    (define ab2 (abstract-model value 1))
    (define ab3 (abstract-model value 1))
    (define ab* (abstract-model (cons ,ab0 (cons ,ab1 (cons ,ab2 (cons ,ab3 nil))))))
    (define ablock (abstract-model block 3))
    (define ah* (abstract-model (cons ,ablock nil)))
    (define as* (abstract-model (,ab* ,ah*)))
    (let*-values
     ([(s* nondet*) (capture-nondeterminism #:nondet #t (make-state-struct (compile-abs-into-heap-fl 2 as*)))])
     (define i* (heap-model action 3))
     (define s+* (interpret-action i* s*))
     (define as+* (abs-interpret-action i* as*))
     (define sol (verify (assert ((bounded-equiv-state 3) as+* s+*))))
     (if (unsat? sol)
         (displayln "unsat")
         (begin
           (displayln "sat")
           (define as (concretize as* sol))
           (define i (concretize i* sol))
           (define s (concretize s* sol))
           (define s+ (interpret-action i s))
           (define as+ (abs-interpret-action i as))
           (displayln "Over state")
           (display-abs-state as)
           (displayln "compiled as state")
           (display-state s)
           (display "Action ")
           (displayln i)
           (displayln "Results in abstract.state :")
           (display-abs-state as+)
           (displayln "and heap.state :")
           (display-state s+)
           (displayln "which are equivalent?")
           (displayln ((bounded-equiv-state 3) as+ s+)))))))

; Cannot break this property
(define (manual-test5s)
  (begin
    (define as ademostate)
    (let*-values
     ([(s* nondet) (capture-nondeterminism #:nondet #t (make-state-struct (compile-abs-into-heap 2 as)))])
      (define sol (verify (assert ((bounded-equiv-state 3) as s*))))
      (if (unsat? sol)
          (displayln "unsat")
          (begin
            (displayln "sat")
            (define s (concretize s* sol))
            (displayln "State")
            (display-abs-state as)
            (displayln "compiled as state")
            (display-state s)
            (displayln "is equiv?")
            (displayln ((bounded-equiv-state 3) as s)))))))

; Cannot break this property
(define (manual-test5fl)
  (begin
    (define as ademostate)
    (let*-values
     ([(s* nondet) (capture-nondeterminism #:nondet #t (make-state-struct (compile-abs-into-heap-fl 2 as)))])
      (define sol (verify (assert ((bounded-equiv-state 3) as s*))))
      (if (unsat? sol)
          (displayln "unsat")
          (begin
            (displayln "sat")
            (define s (concretize s* sol))
            (displayln "State")
            (display-abs-state as)
            (displayln "compiled as state")
            (display-state s)
            (displayln "is equiv?")
            (displayln ((bounded-equiv-state 3) as s)))))))



(define i-test0 (heap-model (cons (decr 1) (cons (free 2) nil)))) ; from demo0
(define i-test1 (heap-model (cons (copy 1 3) (cons (free 3) nil))))  ; access to a block which has been freed

(define a-test0 (heap-model (write 1 3)))

(define as+t1 (abs-interpret-interaction i-test1 ademostate))
