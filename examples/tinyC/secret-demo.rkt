#lang seec

(require seec/private/util)
(require "tinyC.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt"
         )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; A simple password checker ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(define main-declaration
  (tinyC:make-declaration
   (string "main") (list (tinyC ("password" int)))
   ; ^ function name            ^ input

   (list (tinyC ("candidate" int))
         (tinyC ("auth" int))
         (tinyC ("secret" int))
         )
   ;     ^ local arguments

    (list (tinyC (ASSIGN "auth" 0))
          (tinyC (ASSIGN "secret" 42))
          (tinyC (INPUT (& "candidate")))
          (tinyC (IF (= "candidate" "password")
                     (ASSIGN "auth" 1)
                     SKIP))
          (tinyC (CALL "guarded-fun"
                       (cons "auth" (cons "secret" nil))))

          )))

(define guarded-function-declaration
  (tinyC:make-declaration (string "guarded-fun") (list (tinyC ("auth" int))
                                                       (tinyC ("secret" int)))
    (list )
    (list (tinyC (IF "auth"
                     (OUTPUT "secret")
                     SKIP))
          ; ...
          )
    ))
(define password-checker (list main-declaration
                               guarded-function-declaration))




; Display the program
; In tinyC:
(define (print-password-checker)
  (tinyC:display-program (list->seec password-checker)))
; In tinyA:
(define (print-compiled-password-checker)
  (display-tinyA-lang-expression ((compiler-compile tinyC-compiler) (list->seec password-checker))))



(define (run-password-checker correct-password guess)
  (tinyC:run password-checker
             (list correct-password) ; The argument to main
             (list (seec-singleton guess)))) ; The input to INPUT

#;(tinyC:display-state (run-password-checker 100        100))
                                          ;  ^ password ^ guess
; Produces a trace of 1, indicating success
#;(tinyC:display-state (run-password-checker 100        0))
                                          ;  ^ password ^ guess
; Produces a trace of 0, indicating failure


(max-fuel 20)

(define (pp-intlist vals)
  (format "~a" (seec->list vals)))
(define (display-env-password-checker env)
  (match env
    [(tinyC (args:intlist input:list<intlist>))
     (displayln (format "password : ~a" (pp-intlist args)))
     (displayln (format "input stream : ~a" (map pp-intlist (seec->list input))))]
    ))

(define synthesize-tinyC-changed-behavior
  (λ (prog
      #:args   args
      #:input  input
      )
    (let ([g (find-changed-behavior
                tinyC-compiler
                (list->seec prog)
                #:source-context (tinyC (,(list->seec args)
                                         (cons ,(list->seec input) nil)))
                #:target-context (tinyA (,(list->seec args)
                                         (cons ,(list->seec input) nil)))
                )])
      (display-changed-behavior g
                                #:display-source-expression tinyC:display-program
                                #:display-target-expression display-tinyA-lang-expression
                                #:display-context display-env-password-checker
                                ))))


(define (synthesize-changed-behavior-1)
  (define-symbolic* password integer?)
  (define-symbolic* x integer?)
  (synthesize-tinyC-changed-behavior password-checker
                                     #:args  (list password)
                                     #:input (list x)
                                     ))


(define (synthesize-changed-behavior-2)
  (define-symbolic* password integer?)
  (define-symbolic* x y integer?)
  (synthesize-tinyC-changed-behavior password-checker
                                     #:args  (list password)
                                     #:input (list x y)
                                     ))


(define synthesize-tinyC-gadget
  (λ (prog
      #:spec   spec
      #:args   args
      #:input  input
      #:forall [vars (list)]
      )
    (let ([g (find-ctx-gadget tinyA-lang
                              spec
                              #:expr ((compiler-compile tinyC-compiler) (list->seec prog))
                              #:context (tinyA (,(list->seec args)
                                                (cons ,(list->seec input) nil)))
                              #:forall vars
                              )])
      (display-gadget g #:display-expression display-tinyA-lang-expression
                        #:display-context display-env-password-checker
                        ))))




(define (synthesize-password-gadget-2)
  (define-symbolic* password integer?)
  (define-symbolic* x y integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to set auth to true
                           #:spec (λ (p tr) (not (equal? tr seec-empty)))
                           #:args  (list password)
                           #:input (list x y)
                           #:forall password
                           ))
#;(print-password-checker)

(define (synthesize-password-gadget-1)
  (define-symbolic* password integer?)
  (define-symbolic* x integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to set auth to true
                           #:spec (λ (p tr) (not (equal? tr seec-empty)))
                           #:args  (list password)
                           #:input (list x)
                           #:forall password
                           ))


(define (synthesize-password-gadget-2+ target-value)
  (define-symbolic* password integer?)
  (define-symbolic* x y integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to set auth to true
                           #:spec (λ (p tr)
                                    (equal? tr (seec-singleton target-value)))
                           #:args  (list password)
                           #:input (list x y)
                           #:forall password
                           ))
#;(synthesize-password-gadget-2+ 300)

(define (synthesize-password-gadget-3 target-value)
  (define-symbolic* password integer?)
  (define-symbolic* x y z integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to set auth to true
                           #:spec (λ (p tr) (equal? tr (seec-singleton target-value)))
                           #:args  (list password)
                           #:input (list x y z)
                           #:forall password
                           ))








; Read secret
; Write to secret

; Future work:
;   1. Handling symbolic input lists of bounded size, rather than trying lists of length 1, 2, 3.
;   2. Fixing symbolic execution bugs that cause state explosion, common to
;      symbolic execution projects. We are trying to find ways to handle these
;      problems in general, rather than on a case-by-case basis
;   3. Synthesizing more composable gadgets, handling DOP in general, e.g. with loops























(define (synthesize-password-gadget-0)
  (define-symbolic* x integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to set auth to true
                           #:spec (λ (p tr) (not (equal? tr seec-empty)))
                           #:args  (list 100)
                           #:input (list x)
                           ))

                           
