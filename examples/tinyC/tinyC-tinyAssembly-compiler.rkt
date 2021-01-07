#lang seec
(require racket/contract)
(require "monad.rkt")
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
                  ))
(require rosette/lib/value-browser) ; debugging

(provide (all-defined-out))


; Compile statements into low-level forms. Replace structured control-flow
; with jumps
;
; Compile statement stmt in procedure p at start address init-pc in memory mem
; Return both the updated memory and the PC that points to the next address that
; has not yet been written to.
(define (tinyC->tinyA-statement stmt p init-pc mem)
  (-> tinyC-statement? syntax-proc-name? tinyA-program-counter? tinyA-memory?
      (values integer? tinyA-memory?))
  (match stmt
    ; Replace if statement with jmpz
    [(tinyC (IF e:expr t:statement f:statement))
     (let*-values ([(t-pc)        (+ 1 init-pc)]
                   [(t-pc+ mem+)  (tinyC->tinyA-statement t p t-pc mem)]
                   [(f-pc)        (+ 1 t-pc+)]
                   [(f-pc+ mem++) (tinyC->tinyA-statement f p f-pc mem+)]
                   [(mem+++)      (tinyA:store-mem init-pc
                                                  (tinyA (,p (JMPZ ,e ,f-pc)))
                                                  mem++)]
                   [(mem++++)     (tinyA:store-mem t-pc+
                                                  (tinyA (,p (JMPZ 0 ,f-pc+)))
                                                  mem+++)]
                   )
       (values f-pc+ mem++++))]

    ; Replace while statement with jmpz
    [(tinyC (WHILE e:expr body:statement))
     (let*-values ([(body-pc)       (+ 1 init-pc)]
                   [(body-pc+ mem+) (tinyC->tinyA-statement body p body-pc mem)]
                   [(end-pc)        (+ 1 body-pc+)]
                   [(mem++)         (tinyA:store-mem init-pc
                                                    (tinyA (,p (JMPZ ,e ,end-pc)))
                                                    mem+)]
                   [(mem+++)        (tinyA:store-mem body-pc+
                                                    (tinyA (,p (JMPZ 0 ,init-pc)))
                                                    mem++)]
                   )
       (values end-pc mem+++))]

    ; Layout sequenced blocks linearly
    [(tinyC (SEQ s1:statement s2:statement))
     (let*-values ([(pc1 mem1) (tinyC->tinyA-statement s1 p init-pc mem)])
       (tinyC->tinyA-statement s2 p pc1 mem1))]

    ; Remaining statements do not require compilation
    [_
     (let* ([new-pc (+ 1 init-pc)]
            [mem+   (tinyA:store-mem init-pc
                                    (tinyC (,p ,stmt))
                                    mem)]
            )
       (values new-pc mem+))]

    ))


(define/contract (declaration->frame-element sp decl)
  (-> tinyA-stack-pointer?
      (or/c tinyC-local-decl?
            tinyC-param-decl?)
      tinyA-frame-elem?)
  (match decl
    [(tinyC (x:var ty:simple-type))
     (tinyA (,x ,sp))]
    [(tinyC (x:var (array ty:simple-type len:integer)))
     (tinyA (,x ,sp ,len))]
    ))
    
(define/contract (declaration->frame decl)
  (-> tinyC-declaration? tinyA-frame?)
  (let* ([param-list (seec->list (tinyC:declaration->parameters decl))]
         [local-list (seec->list (tinyC:declaration->locals decl))]
         ; Allocate local declarations first, then parameter declarations, so
         ; the argument list is close to the new SP
         [decl-list  (append local-list param-list)]
         [num-decls  (length decl-list)]
         [frames     (map declaration->frame-element
                          (range 0 num-decls)
                          decl-list)]
         )
    (list->seec frames)))

; Compile a prodecure declaration by compiling the procedure's statements
; and creating a stack layout. Insert 'return' or 'halt' instructions at
; the end of each procedure definition.
(define/contract (tinyC->tinyA-declaration decl pc)
  (-> tinyC-declaration? tinyA-program-counter?
      (values tinyA-declaration?
              tinyA-memory?))

  (let* ([F (declaration->frame decl)]
         [p (tinyC:declaration->name decl)]
         ; Need to insert either a return or halt to the end of the function
         ; body depending on whether we are currently in "main"
         [last-insn (if (equal? p (string "main"))
                            (tinyA HALT)
                            (tinyA RETURN))]
         [body (seec-append (tinyC:declaration->body decl)
                            (seec-singleton last-insn))]
         )
    (let-values ([(pc+ mem+) (tinyC->tinyA-statement body p pc seec-empty)])
      (values (tinyA (,p ,pc+ ,F)) mem+)
      )))

; Compile a high-level program by compiling each procedure in turn and
; storing the results in memory starting at ll.i
(define/contract (tinyC->tinyA-program P pc)
  (-> tinyC-prog? tinyA-program-counter?
      (values tinyA-global-store?
              tinyA-memory?))
  (match P
    [(tinyC nil)
     (values (tinyA nil) (tinyA nil))]
    [(tinyC (cons decl:declaration P+:prog))
     (let*-values ([(decl+ mem) (tinyC->tinyA-declaration decl pc)]
                   [(G+    mem+)   (tinyC->tinyA-program P+ (tinyA:declaration->pc decl+))]
                   )
       (values (tinyA (cons ,decl+ ,G+))
               (seec-append mem mem+))
       )]
    ))
                  
; Given a memory with a compiled program, initialize the stack at 'i_s' and
; invoke 'main' with arguments 'v ...'
(define/contract (load-compiled-program G mem sp vals)
  (-> tinyA-global-store? tinyA-memory? tinyA-stack-pointer? (listof tinyA-value?)
      (or/c #f tinyA:state?)
      )
  (do (<- decl (tinyA:proc-name->declaration (string "main") G))
      (<- mem+ (tinyA:push-objs (- sp (length vals)) vs mem))
      (<- sp+  (- sp (tinyA:frame-size F)))
      (tinyA:initial-state #:global-store G
                           #:pc           (declaration->pc decl)
                           #:sp           sp+
                           #:memory       mem+)
      ))

(define/contract (load P pc0 sp0 vals)
  (-> tinyC-prog? tinyA-program-counter? tinyA-stack-pointer? 
      (listof tinyA-value?)
      (or/c #f tinyA:state?))
  (let-values ([(G mem) (tinyC->tinyA-program P pc0)])
    (load-compiled-program G mem sp0 vals)))
