#|
Program name    : specify-representation.ss
Functions       : specify-representation
Description     : This program convert scheme datatypes to ptr equivalents and translate scheme primitive
		  calls to UIL primitive calls.
Input Language  : Scheme with valid context
Output Language : Scheme with UIL primitive calls
|#

#!chezscheme
(library (Compiler specify-representation)
  (export
    specify-representation)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers)
    (Framework prims))

;; Defines pass19 of the compiler
(define-who specify-representation
  (define value-prims?
    (lambda (x)
      (memq x '(make-procedure procedure-ref procedure-code))))
  (define effect-prims?
    (lambda (x)
      (equal? x 'procedure-set!)))
  (define pred-prims?
    (lambda (x)
      (equal? x 'procedure?)))
  (define get-data
    (lambda (x)
      (match x
        ((quote ,y) y)
        (,y y))))
  ;; Process Value part of the grammer
  (define Value
    (lambda (val)
      (match val
	[,label (guard (label? label)) label]
	[,uvar (guard (uvar? uvar)) uvar]
	[(quote ,Immediate) (guard (isImmediate Immediate))
	  (case Immediate
	    [(#t) $true]
	    [(#f) $false]
	    [(()) $nil]
	    [(void) $void]
	    [else (* 8 Immediate)])] 
        [(if ,[Pred -> p] ,[Value -> v1] ,[Value -> v2]) `(if ,p ,v1 ,v2)]
        [(begin ,[Effect -> ef] ... ,[Value -> v]) (make-begin`(,ef ... ,v))]
        [(let ([,uvar* ,[Value -> v1]] ...) ,[Value -> v2]) `(let ([,uvar* ,v1] ...) ,v2)]
	[(,prim ,x1* ,x2*) (guard (equal? prim '*))
	  (let ([x1 (Value x1*)] [x2 (Value x2*)] [x3 (get-data x1*)] [x4 (get-data x2*)])
	    (if (and (integer? x3) (integer? x4)) `(,prim ,(* 8 x4) ,x3)
	    (if (or (integer? x3) (integer? x4)) (if (integer? x3) `(,prim ,x3 ,x2) `(,prim ,x1 ,x4)) 
	   `(,prim ,x1 (sra ,x2 ,shift-fixnum)))))]
	[(,prim ,[Value -> x*] ...) (guard (or (checkValPrim prim) (value-prims? prim)))
	  (case prim
	    [(+) `(+ ,x* ...)]
	    [(-) `(- ,x* ...)]
	    [(car) `(mref ,x* ... ,(- disp-car tag-pair))]
	    [(cdr) `(mref ,x* ... ,(- disp-cdr tag-pair))]
	    [(cons) (let ([tmp-car (unique-name 't)] [tmp-cdr (unique-name 't)] [tmp (unique-name 't)])
		      `(let ([,tmp-car ,(car x*)] [,tmp-cdr ,(cadr x*)])
    			 (let ([,tmp (+ (alloc ,size-pair) ,tag-pair)])
 		           (begin
		             (mset! ,tmp ,(- disp-car tag-pair) ,tmp-car)
        		     (mset! ,tmp ,(- disp-cdr tag-pair) ,tmp-cdr)
        		     ,tmp))))]
	    [(make-vector) (if (integer? (car x*))
			       (let ([tmp (unique-name 't)])
			         `(let ([,tmp (+ (alloc ,(+ disp-vector-data (car x*))) ,tag-vector)])
				    (begin
 				      (mset! ,tmp ,(- disp-vector-length tag-vector) ,(car x*))
      				      ,tmp)))
			       (let ([tmp1 (unique-name 't)] [tmp2 (unique-name 't)])
			         `(let ([,tmp1 ,(car x*)])
    				    (let ([,tmp2 (+ (alloc (+ ,disp-vector-data ,tmp1)) ,tag-vector)])
      				      (begin
        			        (mset! ,tmp2 ,(- disp-vector-length tag-vector) ,tmp1)
        			        ,tmp2)))))]
	    [(make-procedure) (if (integer? (cadr x*))
			       (let ([tmp (unique-name 't)])
			         `(let ([,tmp (+ (alloc ,(+ disp-procedure-data (cadr x*))) ,tag-procedure)])
				    (begin
 				      (mset! ,tmp ,(- disp-procedure-code tag-procedure) ,(car x*))
      				      ,tmp)))
			       (error who "unexpected pred-prim ~s" prim))]
	    [(vector-length) `(mref ,x* ... ,(- disp-vector-length tag-vector))]
	    [(procedure-code) `(mref ,x* ... ,(- disp-procedure-code tag-procedure))]
            [(vector-ref) (if (integer? (cadr x*)) 
			      `(mref ,(car x*) ,(+ (- disp-vector-data tag-vector) (cadr x*)))
			      `(mref ,(car x*) (+ ,(- disp-vector-data tag-vector) ,(cadr x*))))]
            [(procedure-ref) (if (integer? (cadr x*)) 
			        `(mref ,(car x*) ,(+ (- disp-procedure-data tag-procedure) (cadr x*)))
			        `(mref ,(car x*) (+ ,(- disp-procedure-data tag-procedure) ,(cadr x*))))]
	    [(void) $void]
	    [else (error who "unexpected pred-prim ~s" prim)])]
        [(,[Value -> v1] ,[Value -> v2] ...) `(,v1 ,v2 ...)]
        [,st (errorf who "invalid syntax for Value ~s" val)])))
  ;; Process Effect part of the grammer
  (define Effect
    (lambda (st)
      (match st
        [(nop) `(nop)]
        [(if ,[Pred -> p] ,[Effect -> ef1] ,[Effect -> ef2]) `(if ,p ,ef1 ,ef2)]
        [(begin ,[Effect -> ef1] ... ,[Effect -> ef2]) (make-begin `(,ef1 ... ,ef2))]
	[(let ([,uvar* ,[Value -> v]] ...) ,[Effect -> ef]) `(let ([,uvar* ,v] ...) ,ef)]
	[(,prim ,[Value -> x*] ...) (guard (or (checkEffectPrim prim) (effect-prims? prim)))
	  (case prim
	    [(set-car!) `(mset! ,(car x*) ,(- disp-car tag-pair) ,(cadr x*))]
	    [(set-cdr!) `(mset! ,(car x*) ,(- disp-cdr tag-pair) ,(cadr x*))]
            [(vector-set!) (if (integer? (cadr x*)) 
			      `(mset! ,(car x*) ,(+ (- disp-vector-data tag-vector) (cadr x*)) ,(cadr (cdr x*)))
			      `(mset! ,(car x*) (+ ,(- disp-vector-data tag-vector) ,(cadr x*)) ,(cadr (cdr x*))))]
            [(procedure-set!) (if (integer? (cadr x*)) 
			      `(mset! ,(car x*) ,(+ (- disp-procedure-data tag-procedure) (cadr x*)) ,(cadr (cdr x*)))
			      `(mset! ,(car x*) (+ ,(- disp-procedure-data tag-procedure) ,(cadr x*)) ,(cadr (cdr x*))))]
	    [else (error who "unexpected pred-prim ~s" prim)])]
	[(,[Value -> v1] ,[Value -> v2] ...) `(,v1 ,v2 ...)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; Process predicate part of the grammer
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> p1] ,[Pred -> p2] ,[Pred -> p3]) `(if ,p1 ,p2 ,p3)]
        [(begin ,[Effect -> ef] ... ,[Pred -> p]) (make-begin `(,ef ... ,p))]
        [(true) `(true)]
        [(false) `(false)]
	[(let ([,uvar* ,[Value -> v]] ...) ,[Pred -> p]) `(let ([,uvar* ,v] ...) ,p)]
	[(,prim ,[Value -> x*] ...) (guard (or (checkPredPrim prim) (pred-prims? prim))) 
	   (if (isRelop prim)
	      `(,prim ,x* ...)
	       (case prim
        	 [(boolean?) `(= (logand ,x* ... ,mask-boolean) ,tag-boolean)]
        	 [(eq?) `(= ,x* ...)]
		 [(fixnum?) `(= (logand ,x* ... ,mask-fixnum) ,tag-fixnum)]
		 [(null?) `(= ,x* ... ,$nil)]
		 [(pair?) `(= (logand ,x* ... ,mask-pair) ,tag-pair)]
		 [(vector?) `(= (logand ,x* ... ,mask-vector) ,tag-vector)]
		 [(procedure?) `(= (logand ,x* ... ,mask-procedure) ,tag-procedure)]
        	 [else (error who "unexpected pred-prim ~s" prim)]))]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; Convert scheme primitives to UIL primitives
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda (,uvar* ...) ,[Value -> body*])] ...) ,[Value -> body])
          `(letrec ([,label* (lambda (,uvar* ...) ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))

)
