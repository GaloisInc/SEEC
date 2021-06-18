#lang seec
(require seec/private/util)
(require seec/private/monad)
(require (file "tinyC.rkt"))
(require (file "tinyAssembly.rkt"))
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error
                  values
                  )
         (only-in racket/list
                  range
                  )
         (only-in seec/private/bonsai3
                  new-integer!
                  new-natural!
                  ))
(require rosette/lib/value-browser) ; debugging

(provide (all-defined-out))
(use-contracts-globally #t)


(define/contract (tinyA:store-insn pc stmt p mem)
  (-> tinyA-program-counter? tinyA-statement? syntax-proc-name? tinyA-insn-store?
      tinyA-insn-store?)
  (tinyA:store-insn-sorted pc (tinyA (,p ,stmt)) mem))

; Compile statements into low-level forms. Replace structured control-flow
; with jumps
;
; Compile statement stmt in procedure p at start address init-pc in memory mem
; Return both the updated memory and the PC that points to the next address that
; has not yet been written to.
(define/contract (tinyC->tinyA-statement stmt p init-pc mem)
  (-> tinyC-statement? syntax-proc-name? tinyA-program-counter? tinyA-insn-store?
      (values integer? tinyA-insn-store?))
  (match stmt
    ; Replace if statement with jmpz
    [(tinyC (IF e:expr t:statement f:statement))
     (let*-values ([(t-pc)        (+ 1 init-pc)]
                   [(t-pc+ mem+)  (tinyC->tinyA-statement t p t-pc mem)]
                   [(f-pc)        (+ 1 t-pc+)]
                   [(f-pc+ mem++) (tinyC->tinyA-statement f p f-pc mem+)]
                   [(mem+++)      (tinyA:store-insn init-pc
                                                    (tinyA (JMPZ ,e ,f-pc))
                                                    p
                                                    mem++)]
                   [(mem++++)     (tinyA:store-insn t-pc+
                                                    (tinyA (JMPZ 0 ,f-pc+))
                                                    p
                                                    mem+++)]
                   )
       (values f-pc+ mem++++))]

    ; Replace while statement with jmpz
    [(tinyC (WHILE e:expr body:statement))
     (let*-values ([(body-pc)       (+ 1 init-pc)]
                   [(body-pc+ mem+) (tinyC->tinyA-statement body p body-pc mem)]
                   [(end-pc)        (+ 1 body-pc+)]
                   [(mem++)         (tinyA:store-insn init-pc
                                                      (tinyA (JMPZ ,e ,end-pc))
                                                      p
                                                      mem+)]
                   [(mem+++)        (tinyA:store-insn body-pc+
                                                      (tinyA (JMPZ 0 ,init-pc))
                                                      p
                                                      mem++)]
                   )
       (values end-pc mem+++))]

    ; Layout sequenced blocks linearly
    [(tinyC (SEQ s1:statement s2:statement))
     (let*-values ([(pc1 mem1) (tinyC->tinyA-statement s1 p init-pc mem)])
       (tinyC->tinyA-statement s2 p pc1 mem1))]

    ; SKIP statements can be discarded??
    [(tinyC SKIP) (values init-pc mem)]

    ; Remaining statements do not require compilation
    [_
     (let* ([new-pc (+ 1 init-pc)]
            [mem+   (tinyA:store-insn init-pc
                                      stmt
                                      p
                                      mem)]
            )
       (values new-pc mem+))]

    ))


(define/contract (declaration->frame-element offset decl)
  (-> integer?
      (or/c tinyC-local-decl?
            tinyC-param-decl?)
      tinyA-frame-elem?)
  (match decl
    [(tinyC (x:var ty:simple-type))
     (tinyA (,x ,offset))]
    [(tinyC (x:var (array ty:simple-type len:integer)))
     (tinyA (,x ,offset ,len))]
    ))

(define (declaration-length decl)
  (-> tinyA-stack-pointer?
      (or/c tinyC-local-decl?
            tinyC-param-decl?)
      integer?)
  (match decl
    [(tinyC (x:var ty:simple-type))
     1]
    [(tinyC (x:var (array ty:simple-type len:integer)))
     (+ 1 len)]))

(define/contract (declaration-list->frame offset decl-list)
  (-> integer?
      (curry seec-list-of? (or/c tinyC-local-decl? tinyC-param-decl?))
      tinyA-frame?)
  (match decl-list
    [(tinyC nil) (tinyA nil)]
    [(tinyC (cons (x:var ty:simple-type) decl-list+:any))
     (seec-cons (tinyA (,x ,offset))
                (declaration-list->frame (+ 1 offset) decl-list+)
                )]
    [(tinyC (cons (x:var (array ty:simple-type len:integer)) decl-list+:any))
     (seec-cons (tinyA (,x ,offset ,len))
                (declaration-list->frame (+ 1 offset len) decl-list+)
                )]
    ))

    
(define/contract (declaration->frame decl)
  (-> tinyC-declaration? tinyA-frame?)
  (let* #;([param-list (seec->list (tinyC:declaration->parameters decl))]
         [local-list (seec->list (tinyC:declaration->locals decl))]
         ; Allocate local declarations first, then parameter declarations, so
         ; the argument list is close to the new SP

         ; How to arrays get handled?
         [decl-list  (append local-list param-list)]
         [num-decls  (length decl-list)]
         #;[frames     (map declaration->frame-element
                          (range 0 num-decls)
                          decl-list)]
         [frames     (declaration-list->frame 0 (list->seec decl-list))]
         )
        ([param-list (tinyC:declaration->parameters decl)]
         [local-list (tinyC:declaration->locals decl)]
         ; Allocate local declarations first, then parameter declarations, so
         ; the argument list is close to the new SP

         ; How to arrays get handled?
         [decl-list  (seec-append local-list param-list)]
         [frames     (declaration-list->frame 0 decl-list)]
         )
    frames))

; Compile a prodecure declaration by compiling the procedure's statements
; and creating a stack layout. Insert 'return' or 'halt' instructions at
; the end of each procedure definition.
(define/contract (tinyC->tinyA-declaration decl pc)
  (-> tinyC-declaration? tinyA-program-counter?
      (values tinyA-declaration?
              tinyA-program-counter?
              tinyA-insn-store?))

  (let* ([F (declaration->frame decl)]
         [p (tinyC:declaration->name decl)]
         [body (tinyC:declaration->body decl)]
         )
    (let-values ([(pc+ mem+) (tinyC->tinyA-statement body p pc seec-empty)])
      ; Need to insert either a return or halt to the end of the function
      ; body depending on whether we are currently in "main"
      (let ([pc++ (+ 1 pc+)]
            [mem++ (if (equal? p (string "main"))
                       (tinyA:store-insn pc+ (tinyA HALT)   p mem+)
                       (tinyA:store-insn pc+ (tinyA RETURN) p mem+))]
                 )
      (values (tinyA (,p ,pc ,F)) pc++ mem++)
      ))))

; Compile a high-level program by compiling each procedure in turn and
; storing the results in memory starting at ll.i
(define/contract (tinyC->tinyA-program P pc)
  (-> tinyC-prog? tinyA-program-counter?
      (values tinyA-global-store?
              tinyA-insn-store?))
  (match P
    [(tinyC nil)
     (values (tinyA nil) (tinyA nil))]
    [(tinyC (cons decl:declaration P+:prog))
     (let*-values ([(decl+ pc+ mem) (tinyC->tinyA-declaration decl pc)]
                   [(G+    mem+)    (tinyC->tinyA-program P+ pc+)]
                   )
       (values (tinyA (cons ,decl+ ,G+))
               (seec-append mem mem+))
       )]
    ))

(define/contract (tinyA:load P pc0 sp0 buf vals)
  (-> tinyC-prog? tinyA-program-counter? tinyA-stack-pointer? 
      (listof syntax-input-list?)
      (listof tinyA-val?)
      (failure/c tinyA:state?))
  (let-values ([(G insns) (tinyC->tinyA-program P pc0)])
    (tinyA:load-compiled-program G insns (tinyA nil) sp0 buf vals)))


 ; constraint: sp <= pc?
(define init-pc 100)
(define init-sp 100)

(define tinyA:run
  (λ (#:fuel [fuel 100]
      #:program-counter [pc init-pc] 
      #:stack-pointer   [sp init-sp]
      prog    ; A racket list of declarations
      inputs  ; A racket list of inputs to main
      buf     ; A racket list of seec lists to act as inputs to INPUT
      )
    (tinyA:eval-statement fuel
                          (tinyA:load (list->seec prog)
                                      pc
                                      sp
                                      buf
                                      inputs))))


; All values in the target are integers, while values in the source are either
; integers or locations. Any source location is related to any target value,
; while integer source values are only related to the same target value
(define (val-relation v-src v-target)
  (match v-src
    [(tinyC v:integer) (equal? v v-target)]
    [(tinyC l:loc)     #t]
    ))
(define (trace-relation t-src t-target)
  (and (equal? (seec-length t-src) (seec-length t-target)) ; If you don't include
                                                      ; this check, andmap will
                                                      ; throw an exception
       (andmap val-relation (seec->list t-src) (seec->list t-target))))

(define-compiler tinyC-compiler
  #:source tinyC-lang
  #:target tinyA-lang
  ; Behaviors of both languages are traces of values, but
  ; tinyC traces can contain memory locations, which could
  ; relate to any integer in the target.
  #:behavior-relation trace-relation
  ; Contexts in the source is an argument list, which should not contain memory
  ; locations. Contexts in the target are also argument lists that contain only
  ; integer values
  #:context-relation (λ (ctx-src ctx-target)
                       (equal? ctx-src ctx-target))
  ; Expressions in the source are global stores, while in the target they are
  ; global stores, stack pointer, and memory together
  #:compile (λ (g-src) (let-values ([(g-target insns) (tinyC->tinyA-program g-src init-pc)])
                         (tinyA (,g-target ,init-sp nil ,insns))))
  )




;;;;;;;;;;;;;;;;;;;;;;;;;
;; Synthesis utilities ;;
;;;;;;;;;;;;;;;;;;;;;;;;;

; This differs from tinyA-lang in that the behavior is a (failure/c state?)
; instead of a trace.
(define-language tinyA-lang-st
  #:grammar tinyA+
  #:expression expr #:size 5
  #:context ctx #:size 3 ; The trace acts as as the argument list
  ; A whole program is a (failure/c state?)
  #:link (λ (ctx expr)
           (match (cons ctx expr)
             [(cons (tinyA+ (args:input-list input:list<input-list>))
                    (tinyA (g:global-store sp:stack-pointer m:memory insns:insn-store)))
              (tinyA:load-compiled-program g insns m sp (seec->list input) (seec->list args))]
             ))
  #:evaluate (λ (p) (do st <- p
                        (tinyA:eval-statement (max-fuel) st)))
  )

(define synthesize-tinyA-gadget
  (λ (prog
      #:spec       spec
      #:args       args
      #:input      [input (list)] ; list of lists of integers
      #:seec-input [seec-input (list->seec (map list->seec input))]
      #:forall     [vars (list)]
      )
    (let ([g (find-ctx-gadget tinyA-lang-st
                              spec
                              #:expr ((compiler-compile tinyC-compiler) (list->seec prog))
                              #:context (tinyA (,(list->seec args)
                                                ,seec-input nil))
                              #:forall vars
                              )])
      (display-gadget g #:display-expression display-tinyA-lang-expression
                        #:display-context    display-tinyA-lang-context
                        #:display-behavior   display-state
                        ))))



; Produce a symbolic list<list<integer>> where the length is 'length' and each
; internal list has length 'width'
(define (symbolic-input-stream width length)
  (cond
    [(or (<= length 0)
         (havoc!))
     (tinyA nil)]
    [else (seec-cons (symbolic-arglist width)
                     (symbolic-input-stream width (- length 1)))
          ]
    ))
; produce a racket list instead
(define (symbolic-input-stream+ width length)
  (cond
    [(or (<= length 0)
         (havoc!))
     (list)]
    [else (cons (symbolic-arglist width)
                (symbolic-input-stream+ width (- length 1)))
          ]
    ))


(define (symbolic-arg!)
  (tinyA input-elem 2)
  #;(cond
    [(havoc!) (new-integer!)]
    [else     (tinyA (TRACE ,(new-natural!)))]
    ))
(define (symbolic-arglist n)
  (cond
    [(or (<= n 0) (havoc!))
     (tinyA nil)]
    [else
     (seec-cons (symbolic-arg!) (symbolic-arglist (- 1 n)))]
  #;(tinyA list<integer> (+ 1 n))
  ))




; Synthesize an input to produce a specific trace
; where tr should be a racket list of integers
(define (synthesize-trace prog input-len tr)

  ; Fuel bound = size of program. OR: don't execute the target PC along the way?
  ; Do we need to synthesize loop invariant?

  (synthesize-tinyA-gadget prog
                           #:spec (λ (init-state result-state)
                                    (and (tinyA:state? result-state)
                                         (equal? (seec->list (tinyA:state-trace result-state))
                                                 tr)))
                           #:args (list)
                           #:seec-input (symbolic-input-stream 2 input-len)
                           )
  )
