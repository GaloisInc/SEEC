 #lang seec

(require seec/private/util)
(require seec/private/monad)
(require racket/format)
(require (only-in racket/base
                  build-list
                  raise-argument-error
                  raise-arguments-error))
(require (file "lib.rkt"))
(provide (all-defined-out))

(define-grammar freelist
    (action ::=
          (free natural) 
          alloc)
  (interaction ::= list<action>)
  (state ::= list<natural>) ; list of free blocks
)


;; freelist.action -> freelist.state -> freelist.state
(define/debug #:suffix (freelist-action a s)
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

(define-language freelist-lang
  #:grammar freelist
  #:expression state #:size 3
  #:context interaction #:size 3
  #:link cons
  #:evaluate (uncurry freelist-interaction))
