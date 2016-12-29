#|
Program name    : test-case.ss
Description     : This program defines a test case for assignment 15. It will take a pair and calculate
		  the cube of the numbers in the pair. It will output a list with sum of the cubes as
		  the first element followed by the cube values.
|#


(letrec ([sqr (lambda (a) (* a (* a a)))]
	 [sum (lambda () '())]
	 [res (cons (lambda (x) x) '())])
        (let ([pair '(1 . 2)])
	     (and (fixnum? (car pair)) (or (not (= (car pair) 0)) 0) (fixnum? (cdr pair)) (or (not (= (cdr pair) 0)) 0)
	       (begin
                 (set-car! pair (sqr (car pair)))
            	 (set-cdr! pair (sqr (cdr pair)))
	    	 (set! sum (lambda (x y) (+ x y)))
	    	 ((cdr res) (cons (sum (car pair) (cdr pair)) (cons (car pair) (cons (cdr pair) '()))))))))
