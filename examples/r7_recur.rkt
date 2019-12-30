(program ()
(define (sumup x)
        (if (eq? x 0)
	       0
	      (+ x (sumup (- x 1)))))
(- (sumup 9) 3))
