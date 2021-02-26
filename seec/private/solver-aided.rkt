#lang rosette

(require (prefix-in rosette: rosette)
         (only-in rosette assert &&)
         syntax/parse
         (for-syntax syntax/parse))

(provide check-unreachable
         unreachable
         solve
         solve+
         verify
         synthesize)

(define saved-pc
  (make-parameter #t (λ (v) (&& v (saved-pc)))))

(define saved-asserts
  (make-parameter '() (λ (a) (append a (saved-asserts)))))

(define check-unreachable
  (make-parameter #f))

(struct exn:seec:unreachable exn () #;(message continuation-marks))

(define (replace-asserts asserts)
  (clear-asserts!)
  (for ([a (in-list asserts)])
    (assert a)))

(define (unreachable [msg "reached expression marked unreachable"])
  (when (check-unreachable)
    (parameterize ([saved-pc (pc)]
                   [saved-asserts (asserts)])
      (let ([to-restore (asserts)])
        (replace-asserts (saved-asserts))
        (define result (rosette:verify (assert (not (saved-pc)))))
        (replace-asserts to-restore)
        (when (sat? result)
          (raise (exn:seec:unreachable msg (current-continuation-marks))))))))

(define-syntax (define/wrapped stx)
  (syntax-parse stx
    [(_ name replacement)
     #'(define-syntax (name stx)
         (syntax-parse stx
           [(_ s (... ...))
            #'(parameterize ([saved-asserts (asserts)]
                             [saved-pc (pc)])
                (replacement s (... ...)))]))]))

(define/wrapped solve rosette:solve)
(define/wrapped verify rosette:verify)
(define/wrapped synthesize rosette:synthesize)

(define (solve+)
  (let ([solver (rosette:solve+)])
    (lambda (expr)
      (parameterize ([saved-asserts (asserts)]
                     [saved-pc (pc)])
        (solver expr)))))

(module+ test
  (require rackunit)

  (check-unreachable #t)
  
  (test-case "unreachable raises exception"
    (check-exn exn:seec:unreachable? (thunk (unreachable))))

  (test-case "check-unreachable"
    (check-not-exn (thunk (parameterize ([check-unreachable #f]) (unreachable)))))

  (test-case "reachable branch with symbolic state"
    (check-exn exn:seec:unreachable?
               (thunk (define-symbolic x integer?)
                      (if (> x 0)
                          #t
                          (unreachable)))))

  (test-case "unreachable branch with symbolic state"
    (check-not-exn (thunk (define-symbolic z integer?)
                          (assert (= z 5))
                          (if (> z 0)
                              #t
                              (unreachable)))))

  (test-case "reachable branch in solve"
    (check-exn exn:seec:unreachable?
               (thunk (define-symbolic y integer?)
                      (assert (= y 3))
                      (solve (assert (if (> y 0) (unreachable) #t))))))

  (test-case "unreachable branch in solve"
    (check-not-exn (thunk (define-symbolic y integer?)
                          (assert (= y 3))
                          (solve (assert (if (< y 0) (unreachable) #t)))))))
