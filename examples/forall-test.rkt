#lang seec

(define-grammar map
  (mapping ::= (integer integer))
  (intmap  ::= list<mapping>)
  )

(define (lookup-in-map key m)
  (for*/all ([key key #:exhaustive]
             [m m]) ; Both these for/all clauses are important to make sure the
                    ; output of this function is a concise union, and not too
                    ; large
    #;(debug-display "(lookup-in-map ~a)" x)
    (match m
    [(map nil) 0]
    [(map (cons (key+:integer value+:integer) m+:intmap))
     (for/all ([key+ key+ #:exhaustive])
       (if (equal? key key+)
           value+
           (lookup-in-map key m+)))]
     )))


(define symbolic-map
  (cond
    [(havoc!) (list->seec (list (map (200 3)) (map (200 2))))]
    [else     (list->seec (list (map (200 2))))]
    ))
(displayln (lookup-in-map 200 symbolic-map)) ; produces (ite havoc$0 3 2)
(for/all ([x (lookup-in-map 200 symbolic-map)])
  (displayln x)) ; produces (ite havoc$0 3 2)
(for/all ([x (lookup-in-map 200 symbolic-map) #:exhaustive])
  (displayln x)) ; produces 3, and then 2


(define wrapped-map
  (let ([x (lookup-in-map 200 symbolic-map)])
    (seec-cons (map (300 ,x)) symbolic-map)))

(displayln wrapped-map) ; produces (300, ite havoc0 3 2) :: {2-element union}
(for/all ([x wrapped-map])
  (displayln x)) ; same as above since wrapped-map is not a union
(for/all ([x wrapped-map #:exhaustive])
  (displayln x)) ; same as above since wrapped-map is not a union

(define wrapped-map-union
  (for/all ([x (lookup-in-map 200 symbolic-map) #:exhaustive])
    (seec-cons (map (300 ,x)) symbolic-map)))
(displayln wrapped-map-union) ; 2-element union
(for/all ([m+ wrapped-map-union])
  (displayln m+)) ; Produces {(300,3)::2-element union ; (300,2)::2-element union}
(for/all ([m+ wrapped-map-union #:exhaustive])
  (displayln m+)) ; Same as above

(define wrapped-map-union-final
  (for*/all ([m+ symbolic-map]
             [x (lookup-in-map 200 m+) #:exhaustive])
    (seec-cons (map (300 ,x)) m+)))
(displayln wrapped-map-union-final) ; 2-element union
(for/all ([m+ wrapped-map-union-final])
  (displayln m+)) ; Produces {(300,3)::(200:3)::(200,2) ; (300,2)::(200,2)}
(for/all ([m+ wrapped-map-union-final #:exhaustive])
  (displayln m+)) ; Same as above

(struct point (x y))
(define symbolic-pt (cond
                      [(havoc!) (point 1 2)]
                      [else     (point 3 4)]))
(define (display-point pt)
  (displayln (format "(point ~a ~a)" (point-x pt) (point-y pt))))
(display-point symbolic-pt) ; produces a single struct with two symbolic arguments
(for/all ([p symbolic-pt])
  (display-point p)) ; produces a union of the two points
(for/all ([p symbolic-pt #:exhaustive])
  (display-point p)) ; produces a union of the two points
(displayln (format "union? ~a" (union? symbolic-pt))) ; #t


(struct point-transparent (x y) #:transparent)
(define symbolic-pt-transparent (cond
                                  [(havoc!) (point-transparent 1 2)]
                                  [else     (point-transparent 3 4)]))
(define (display-point-transparent pt)
  (displayln (format "(point-transparent ~a ~a)"
                     (point-transparent-x pt)
                     (point-transparent-y pt))))
(display-point-transparent symbolic-pt-transparent) ; produces a single struct
                                                    ; with two symbolic
                                                    ; arguments
(for/all ([p symbolic-pt-transparent])
  (display-point-transparent p)) ; same as above
(for/all ([p symbolic-pt-transparent #:exhaustive])
  (display-point-transparent p)) ; same as above
(displayln (format "union? ~a" (union? symbolic-pt-transparent))) #f
