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
         (tinyC ("auth" int)))
   ;     ^ local arguments

    (list (tinyC (ASSIGN "auth" 0))
          (tinyC (INPUT (& "candidate")))
          (tinyC (IF (= "candidate" "password")
                     (ASSIGN "auth" 1)
                     SKIP))
          (tinyC (CALL "guarded-fun"
                       (cons "auth" nil)))

          )))

(define guarded-function-declaration
  (tinyC:make-declaration (string "guarded-fun") (list (tinyC ("auth" int)))
    (list )
    (list (tinyC (OUTPUT "auth"))) ; ...
    ))
(define password-checker (list main-declaration
                               guarded-function-declaration))








#;(tinyC:display-program (list->seec password-checker))
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
}
|#


(define (run-password-checker correct-password guess)
  (tinyC:run password-checker
             (list correct-password) ; The argument to main
             (list (seec-singleton guess)))) ; The input to INPUT

#;(tinyC:display-state (run-password-checker 42 ; The password
                                             42 ; The guess
                                             ))
; Produces a trace of 1, indicating success
#;(tinyC:display-state (run-password-checker 42 ; The password
                                           03 ; The wrong guess
                                           ))
; Produces a trace of 0, indicating failure


(max-fuel 10)

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
      (display-weird-behavior g displayln))))

(define (synthesize-weird-behavior-password-1)
  (define-symbolic* x integer?)
  (synthesize-tinyC-weird-behavior password-checker
                                   #:args  (list 42)
                                   #:input (list x)
                                   ))
#;(synthesize-weird-behavior-password-1)

(define (synthesize-weird-behavior-password-1+)
  (define-symbolic* password integer?)
  (define-symbolic* x integer?)
  (synthesize-tinyC-weird-behavior password-checker
                                   #:args  (list password)
                                   #:input (list x)
                                   ))
#;(synthesize-weird-behavior-password-1+)



(define (synthesize-weird-behavior-password-2)
  (define-symbolic* password integer?)
  (define-symbolic* x y integer?)
  (synthesize-tinyC-weird-behavior password-checker
                                   #:args  (list password)
                                   #:input (list x y)
                                   ))
#;(synthesize-weird-behavior-password-2)


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
      (display-gadget g displayln))))

(define (synthesize-password-gadget-1)
  (define-symbolic* password integer?)
  (define-symbolic* x integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to always output "1": sets auth to true
                           #:spec (λ (p tr) (equal? tr (seec-singleton 1)))
                           #:args  (list password)
                           #:input (list x)
                           #:forall password
                           ))
#;(synthesize-password-gadget-1)
; Fails to synthesize
                           
(define (synthesize-password-gadget-2)
  (define-symbolic* password integer?)
  (define-symbolic* x y integer?)
  (synthesize-tinyC-gadget password-checker
                           ; Synthesize a context that causes password-checker
                           ; to always output "1": sets auth to true
                           #:spec (λ (p tr) (equal? tr (seec-singleton 1)))
                           #:args  (list password)
                           #:input (list x y)
                           #:forall password
                           ))
#;(synthesize-password-gadget-2)
; Finds a gadget such that x = 0, y = 1

(define (check-context input-list)
  (define-symbolic* password integer?)
  (synthesize-tinyC-gadget password-checker
                           #:spec (λ (p tr) (equal? tr (seec-singleton 1)))
                           #:args  (list password)
                           #:input input-list
                           #:forall password
                           ))
#;(check-context (list 0 1))
