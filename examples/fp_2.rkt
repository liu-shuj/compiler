(program ()
(define (f [a : Double] [b : Double]) : Double 
  (+ (if (> a 25.5) 
       (+ a b) 
       0.0) 
     1))
(int (f 30.5 10.5)))
