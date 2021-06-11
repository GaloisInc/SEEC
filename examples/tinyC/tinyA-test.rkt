#lang seec
(require "tinyC.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt"
         "tinyC-test.rkt")

(module+ test (require rackunit
                       rackunit/text-ui
                       seec/private/util
                       ))


#;(define run-array-test+ (tinyA:run (list array-test)
                                   (list)
                                   (list)))
#;(display-state run-array-test+)

(module+ test



  ; Check declaration->frame
  (define f-example-1 (declaration->frame assign-output-decl))
  #;(displayln f-example-1)
  (check-equal? (tinyA:frame-size f-example-1)
                2)


  (define f-example-2 (declaration->frame (first simple-call-example)))
  #;(displayln f-example-2)
  (check-equal? (tinyA:frame-size f-example-2)
                1)

  ; Check evaluation
  (parameterize ([debug? #f])
    (define g-result (tinyA:run assign-output-example
                                (list 1)
                                (list)))
    #;(display-state g-result)
    (check-equal? (tinyA:state-trace g-result)
                  (list->seec (list 99))))

  (parameterize ([debug? #f])
     (define call-example-output (tinyA:run simple-call-example
                                            (list -5)
                                            (list)))
     #;(display-state call-example-output)
     (check-equal? (tinyA:state-trace call-example-output)
                   (list->seec (list -5))))

  (parameterize ([debug? #f])
    (check-equal? (tinyA:state-trace (tinyA:run
                                      factorial
                                      (list 3)
                                      (list)))
                  (seec-singleton 6)))

  ;;;;;;;;;;;;;;;;;;;;
  ; Password checker ;
  ;;;;;;;;;;;;;;;;;;;;

  (parameterize ([debug? #f])
    (check-equal? (tinyA:state-trace (tinyA:run password-checker
                                                (list)
                                                (list (seec-singleton 42))))
                  (seec-singleton 1)))
  (parameterize ([debug? #f])
    (check-equal? (tinyA:state-trace (tinyA:run password-checker
                                                (list)
                                                (list (seec-singleton -5))))
                  (seec-singleton 0)))
  (parameterize ([debug? #f])
    (check-equal? (tinyA:state-trace (tinyA:run password-checker
                                                (list)
                                                (list (list->seec (list 100 100)))))
                              ; Provide 2 of the same values; the second will
                              ; overwrite password, and thus the check will equal #t
                  (seec-singleton 1)))
  (parameterize ([debug? #f])
    (check-equal? (tinyA:state-trace (tinyA:run password-checker
                                                (list)
                                                (list (list->seec (list 42 100)))))
                              ; Even though the first candidate would have been
                              ; correct, now fails because original password was
                              ; overwritten
                  (seec-singleton 0)))
  (parameterize ([debug? #f])
    (check-equal? (tinyA:state-trace (tinyA:run password-checker
                                                (list)
                                                (list (list->seec (list 42 100 1)))))
                              ; Can also just provide 3 arguments, where the
                              ; third is 1; this will overwrite auth directly
                  (seec-singleton 1)))

  (check-equal? (tinyA:state-trace (tinyA:run password-checker-with-arg
                                              (list 84) ; the password
                                              (list (seec-singleton 84)) ; the guess
                                              ))
                (seec-singleton 1))


  (check-equal? (tinyA:state-trace (tinyA:run password-checker-with-arg
                                              (list 84) ; the password
                                              (list (seec-singleton 42)) ; the guess (wrong)
                                              ))
                (seec-singleton 0))

  (check-equal? (tinyA:state-trace (tinyA:run password-checker-with-arg
                                              (list 84) ; the password
                                              (list (list->seec (list 42 1))) ; auth gets set to '1'
                                              ))
                (seec-singleton 1))


  ; simple-call-example but using language-evaluate
  (let-values ([(G insns) (tinyC->tinyA-program (list->seec simple-call-example)
                                              init-pc
                                              )])
    (let ([p ((language-link tinyA-lang)
              (tinyA+ ((cons -5 nil)
                       nil))
              (tinyA+ (,G ,init-sp nil ,insns))
              )])
      (check-equal? ((language-evaluate tinyA-lang) p)
                    (seec-singleton -5))
      ))


  ; Testing the compiler
  (let* ([target-call-example ((compiler-compile tinyC-compiler) (list->seec simple-call-example))])
    (check-equal? (match target-call-example
                    [(tinyA (g:global-store sp:stack-pointer m:memory insns:insn-store)) #t]
                    [_ #f])
                  #t))


  ;; Array tests ;;



  )
