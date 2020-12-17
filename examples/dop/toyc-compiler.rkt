#lang seec
(require racket/contract)
(require "monad.rkt")
(require (prefix-in toyc:
                    (file "toyc.rkt")
                    )
         (only-in (file "toyc.rkt")
                  syntax
                  syntax-expr?
                  syntax-binop?
                  syntax-lval?
                  syntax-var?
                  toyc
                  toyc-statement?
                  syntax-proc-name?
                  )
         )
(require (prefix-in toya:
                    (file "toya.rkt")
                    )
         (only-in (file "toya.rkt")
                  toya
                  toya-statement?
                  toya-program-counter?
                  toya-memory?
                  )
         )
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error
                  values
                  ))
(require rosette/lib/value-browser) ; debugging

(provide (all-defined-out))


; Compile statements into low-level forms. Replace structured control-flow
; with jumps
;
; Compile statement stmt in procedure p at start address init-pc in memory mem
; Return both the updated memory and the PC that points to the next address that
; has not yet been written to
(define (toyc->toya-statement stmt p init-pc mem)
  (-> toyc-statement? syntax-proc-name? toya-program-counter? toya-memory?
      (values integer? toya-memory?))
  (match stmt
    ; Replace if statement with jmpz
    [(toyc (IF e:expr t:statement f:statement))
     (let*-values ([(t-pc)        (+ 1 init-pc)]
                   [(t-pc+ mem+)  (toyc->toya-statement t p t-pc mem)]
                   [(f-pc)        (+ 1 t-pc+)]
                   [(f-pc+ mem++) (toyc->toya-statement f p f-pc mem+)]
                   [(mem+++)      (toya:store-mem init-pc
                                                  (toya (,p (JMPZ ,e ,f-pc)))
                                                  mem++)]
                   [(mem++++)     (toya:store-mem t-pc+
                                                  (toya (,p (JMPZ 0 ,f-pc+)))
                                                  mem+++)]
                   )
       (values f-pc+ mem++++))]

    ; Replace while statement with jmpz
    [(toyc (WHILE e:expr body:statement))
     (let*-values ([(body-pc)       (+ 1 init-pc)]
                   [(body-pc+ mem+) (toyc->toya-statement body p body-pc mem)]
                   [(end-pc)        (+ 1 body-pc+)]
                   [(mem++)         (toya:store-mem init-pc
                                                    (toya (,p (JMPZ ,e ,end-pc)))
                                                    mem+)]
                   [(mem+++)        (toya:store-mem body-pc+
                                                    (toya (,p (JMPZ 0 ,init-pc)))
                                                    mem++)]
                   )
       (values end-pc mem+++))]

    ; Layout sequenced blocks linearly
    [(toyc (SEQ s1:statement s2:statement))
     (let*-values ([(pc1 mem1) (toyc->toya-statement s1 p init-pc mem)])
       (toyc->toya-statement s2 p pc1 mem1))]

    ; Remaining statements do not require compilation
    [_
     (let* ([new-pc (+ 1 init-pc)]
            [mem+   (toya:store-mem init-pc
                                    (toyc (,p ,stmt))
                                    mem)]
            )
       (values new-pc mem+))]

    ))
