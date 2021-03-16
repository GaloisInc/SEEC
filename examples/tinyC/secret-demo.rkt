#lang seec

(require seec/private/util)
(require "tinyC.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt"
         )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; A simple password checker ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
void main (int password) {
  int candidate;
  int auth;
  auth = 0;
  input(& candidate);
  if (candidate = password) {
    auth = 1;
  } else {
  }
  guarded-fun (auth);
}
void guarded-fun (int auth) {
  output(auth);
  .... ; /* Other sensitive operations depending on auth */
}
|#


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
#;(tinyC:display-program (list->seec password-checker))
; In tinyA:
#;(display-tinyA-lang-expression ((compiler-compile tinyC-compiler) (list->seec password-checker)))



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


(define synthesize-tinyC-weird-behavior
  (λ (prog
      #:args   args
      #:input  input
      )
    (let ([g (find-weird-behavior tinyC-compiler
                                  #:source-expr (list->seec prog)
                                  #:source-context (tinyC (,(list->seec args)
                                                           (cons ,(list->seec input) nil)))
                                  #:target-context (tinyA (,(list->seec args)
                                                           (cons ,(list->seec input) nil)))
                                  #:forall (list)
                                  #:fresh-witness #f
                                  )])
      (display-weird-behavior g
                              #:display-expression tinyC:display-program
                              #:display-context tinyC:display-env
                              ))))


(define (synthesize-weird-behavior-password-1)
  (define-symbolic* password integer?)
  (define-symbolic* x integer?)
  (synthesize-tinyC-weird-behavior password-checker
                                   #:args  (list password)
                                   #:input (list x)
                                   ))


(define (synthesize-weird-behavior-password-2)
  (define-symbolic* password integer?)
  (define-symbolic* x y integer?)
  (synthesize-tinyC-weird-behavior password-checker
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
                        #:display-context display-tinyA-lang-context
                        #:display-behavior displayln
                        ))))

(define (synthesize-password-gadget-0)
  (define-symbolic* x integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to set auth to true
                           #:spec (λ (p tr) (not (equal? tr seec-empty)))
                           #:args  (list 100)
                           #:input (list x)
                           ))

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
#;(tinyC:display-program (list->seec password-checker))


(define (synthesize-password-gadget-2+ target-value)
  (define-symbolic* password integer?)
  (define-symbolic* x y integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to set auth to true
                           #:spec (λ (p tr) (equal? tr (seec-singleton target-value)))
                           #:args  (list password)
                           #:input (list x y)
                           #:forall password
                           ))


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
