#lang seec
(require seec/private/util)
(require seec/private/monad)
(require "tinyC.rkt"
         "tinyC-test.rkt"
         "tinyAssembly.rkt"
         "tinyC-tinyAssembly-compiler.rkt")
(require rosette/lib/value-browser) ; debugging

(module+ test (require rackunit
                       rackunit/text-ui
                       racket/contract
                       ))

(use-contracts-globally #t)


; server program
; Inspired by Data-Oriented Programming by Hu et al

#| Original program:

struct server {int *cur_max, total, typ;} *srv;
int connect_limit = MAXCONN;
int *size, *type;
char buf[MAXLEN];

size = &buf[8];
type = &buf[12];

...
while (connect_limit--) {
  readData(sockfd, buf);
  if (*type == NONE)    break;
  if (*type == STREAM)  *size = *(srv->cur_max); // truncating the stream?
  else {
    srv->typ = *type;
    srv->total += *size;
  }
  ... [use size to determine how long to look ahead at the buffer] ...
}

|#


#| Modified program for tinyC:

void main(int MAXCONN, int MAXLEN) {

  int** srv_cur_max;
  int* srv_total srv_typ;
  int connection_limit = MAXCONN;
  int *size;
  int *type;

  int buf[MAXLEN];
  size = &buf[8];
  type = &buf[12];

  ...

  while (connection_limit > 0) {
    input(buf);
    if (*type == 0) { // indicating NONE
      connection_limit = 0; // CHANGE: we don't have break statements
    } else if (*type == 1) { // indicating STREAM
      *size = *srv_cur_max;
    } else {
      *srv_typ = *type;
      *srv_total = *srv_total + *size;
    }
    ...
    connection_limit = connection_limit - 1; 
  }
}

|#






#|

Alternative server

Operations:
0 - QUIT
1 - PUSH
  - first argument: value to push on the stack
2 - POP
  - first argument: number of elements to pop and output to trace
3 - SIZE
  - output the current number of elements

|#



(define MAXLEN 10) ; Set to be a concrete natural number

(define (INPUT arg)
  (tinyC (INPUT ,arg)))
(define (& arg)
  (tinyC (& ,arg)))
(define (IF b ls1 ls2)
  (tinyC (IF ,b
             ,(tinyC:list->statement ls1)
             ,(tinyC:list->statement ls2))))
(define (WHILE b ls)
  (tinyC (WHILE ,b
                ,(tinyC:list->statement ls))))
(define (OUTPUT arg)
  (tinyC (OUTPUT ,arg)))
(define (CALL p args)
  (tinyC (CALL ,p ,(list->seec args))))
(define (ASSIGN x v)
  (tinyC (ASSIGN ,x ,v)))
(define (INDEX arr i)
  (tinyC (,arr[,i])))


#| Modified program for tinyC:

void main(int MAXCONN) {

  int stack[MAXLEN]; // NOTE: we don't support variable length arrays
  int head = 0; // index into the stack
  int buf[2];

  while (MAXCONN > 0) {
    INPUT(buf);

    if (buf[0] == 1) { // PUSH
      stack[head] = buf[1];
      head = head + 1;

    } else if (buf[0] = 2) { // POP
      output(stack[head]);
      head = head - 1;

    } else if (buf[0] = 3) { // SIZE
      output(head);

    } else { // QUIT
      MAXCONN = 0;
    }

    MAXCONN = MAXCONN - 1;
  }

}

|#


(define server-loop-body
              (list (INPUT (tinyC "buf"))

                    (IF (tinyC (= ("buf"[0]) 1)) ; PUSH
                        (list (tinyC (ASSIGN ("stack"["head"])
                                             ("buf"[1])))
                              (tinyC (ASSIGN "head" (+ "head" 1)))
                              ) ; then branch
                        (list ; else branch

                     (IF (tinyC (= ("buf"[0]) 2)) ; POP
                         (list (tinyC (OUTPUT ("stack"[(- "head" 1)])))
                               (tinyC (ASSIGN "head" (- "head" 1)))
                               )
                        (list ; else branch

                     (IF (tinyC (= ("buf"[0]) 3))
                         (list (tinyC (OUTPUT "head")))

                         (list ; else branch
                          (tinyC (ASSIGN "MAXCONN" 0))
                          ))))))

                    (tinyC (ASSIGN "MAXCONN" (- "MAXCONN" 1)))
                    ))
(define/contract foo
  syntax-expr?
  (tinyC (< 0 "connectionlimit")))

(define/contract server-body
  (listof tinyC-statement?)
  (list (tinyC (ASSIGN "head" 0))
        (WHILE (tinyC (< 0 "MAXCONN"))
               server-loop-body)
        ))

(define server-declaration (tinyC:make-declaration
                            (string "main")
                            ; function arguments
                            (list (tinyC ("MAXCONN" int))
                                  )
                            ; local declarations
                            (list (tinyC ("stack" (array int ,MAXLEN)))
                                  (tinyC ("head"  int))
                                  (tinyC ("buf"   (array int 2)))
                                  )
                            server-body))
(define server-program (list server-declaration))

#;(tinyC:display-program (list->seec server-program))


(module+ test

#;(parameterize ([debug? #t])
  (define server-test-quit
    (tinyA:run server-program
               (list 3)
               (list (seec-singleton 0)
                     )
               ))
  (display-state server-test-quit)
  )
 

  
  (define server-test
    (parameterize ([debug? #f]
                   [max-fuel 1000])
    (tinyC:run server-program
               (list 10)
               (list (list->seec (list 1 100)) ; PUSH 100
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 1 200)) ; PUSH 200
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 2))     ; POP
                     (list->seec (list 3))     ; SIZE
                     (list->seec (list 0))     ; QUIT
                     )
               )))
  (check-equal? (tinyC:state->trace server-test)
                (list->seec (list 1 2 200 1 100 0))
                )
  )

#;(parameterize ([debug? #t])
  (define server-test-quit
    (tinyA:run server-program
               (list 10)
               (list (list->seec (list 1 0))
                     (list->seec (list 2))
                     )
               ))
  (display-state server-test-quit)
  )
