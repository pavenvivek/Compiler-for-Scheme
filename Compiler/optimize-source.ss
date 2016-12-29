#|
Program name    : optimize-source.ss
Functions       : optimize-source
Description     : This program move the inner nested letrec statements to outside and wrap it around
                  the remaining statements
Input Language  : Scheme with procedure primitives and nested letrec
Output Language : Scheme with letrec moved to outside
|#

#!chezscheme
(library (Compiler optimize-source)
  (export
    optimize-source)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers)
    (Framework prims))

;; Defines pass16 of the compiler
(define-who optimize-source
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure? procedure-ref procedure-set! make-procedure procedure-code))
  ;; It defines candidates for folding
  (define foldable-prims
   '(+ - * <= < = >= > boolean? eq? fixnum? null? pair? vector? procedure?))
  ;; It defines procedures that are to be left undisturbed by useless-code remove functionality
  (define non-useless-code
   '(procedure-set! vector-set! set-car! set-cdr! usefull))
  ;; Check if the given values is a numeric constant
  (define num-constant?
    (lambda (imm)
      (if (and (integer? imm) (exact? imm) (fixnum-range? imm)) #t #f)))
  ;; It unquotes the variable and return the result
  (define unquote*
    (lambda (x)
      (match x
        [(quote ,y) y]
	[,x x])))
  ;; It binds uvars with immediate values or direct uvar assignments
  (define filter-bind
    (lambda (uv x)
      (cond
        ((null? x) '())
       	((or (isImmediate (unquote* (car x))) (uvar? (unquote* (car x)))) 
	     (cons (list (car uv) (car x)) (filter-bind (cdr uv) (cdr x))))
 	(else (filter-bind (cdr uv) (cdr x))))))
  ;; It binds uvars with non immediate values or non direct uvar assignments
  (define filter-bind-rev
    (lambda (uv x)
      (cond
        ((null? x) '())
       	((or (isImmediate (unquote* (car x))) (uvar? (unquote* (car x)))) (filter-bind-rev (cdr uv) (cdr x)))
 	(else (cons (list (car uv) (car x)) (filter-bind-rev (cdr uv) (cdr x)))))))
  ;; It returns list with usefull code bindings
  (define remove-useless-code
    (lambda (expr-lst)
      (cond
        ((null? expr-lst) '())
	((memq (caar expr-lst) non-useless-code) (cons (cadar expr-lst) (remove-useless-code (cdr expr-lst))))
	(else (remove-useless-code (cdr expr-lst))))))
  ;; moves the nested letrecs outside
  (define Program
    (lambda (x)
      ;; It handles expression part of the grammer
      (define Expr
	(lambda (cp)
          (lambda (x)
            (match x
              [,label (guard (label? label)) (values label 'label)]
              [,uvar (guard (uvar? uvar)) (if (assq uvar cp) (values (cadr (assq uvar cp)) 'uvar) 
							     (values uvar 'uvar))]
              [(quote ,[Immediate ->]) (values x 'quot)]
              [(if ,[(Expr cp) -> x1 flg1] ,[(Expr cp) -> x2 flg2] ,[(Expr cp) -> x3 flg3])
		 (let ([dead-code (if (isImmediate (unquote* x1))
				      (if (equal? (unquote* x1) #f) x3 x2)
				     `(if ,x1 ,x2 ,x3))])
		      (if (null? (intersection (list flg1 flg2 flg3) non-useless-code)) 
		          (values dead-code 'useless)
		          (values dead-code 'usefull)))]
              [(begin ,[(Expr cp) -> x1* flg*] ... ,[(Expr cp) -> x1 flg]) 
		 (let* ([xpr (map list flg* x1*)]
		        [filtered-xpr* (remove-useless-code xpr)])
		       (if (null? (intersection (append flg* (list flg)) non-useless-code))
		           (values (make-begin `(,filtered-xpr* ... ,x1)) 'useless)
			   (values (make-begin `(,filtered-xpr* ... ,x1)) 'usefull)))]
              [(let ([,uvar* ,[(Expr cp) -> x* flg*]] ...) ,x) 
		 (let* ([binds (filter-bind uvar* x*)]
			[new-binds (filter-bind-rev uvar* x*)])
		       (let-values ([(tail flg) ((Expr (append cp binds)) x)])
				   (if (null? new-binds)
				       (if (memq flg non-useless-code)
					   (values tail 'usefull)
					   (values tail 'useless))
		      		       (if (null? (intersection (cons flg flg*) non-useless-code)) 
					   (values `(let (,new-binds ...) ,tail) 'useless)
					   (values `(let (,new-binds ...) ,tail) 'usefull)))))]
              [(letrec ([,label* (lambda (,uvar* ...) ,[(Expr cp) -> x* flg*])] ...) ,[(Expr cp) -> x flg])
		 (if (memq flg non-useless-code)
                     (values `(letrec ([,label* (lambda (,uvar* ...) ,x*)] ...) ,x) 'usefull)
		     (values `(letrec ([,label* (lambda (,uvar* ...) ,x*)] ...) ,x) 'useless))]
              [(,prim ,[(Expr cp) -> x* flg*] ...) (guard (memq prim primitives))
		(if (memq prim foldable-prims)
		    (case prim
		      [(+ - * <= < = >= >) (if (and (num-constant? (unquote* (car x*))) (num-constant? (unquote* (cadr x*)))) 
				   	       (let ([val (eval `(,prim ,(car x*) ,(cadr x*)))])
				                    (if (memq prim '(+ - *))
						        (if (fixnum-range? val) 
							    (values `(quote ,val) 'useless) 
							    (if (null? (intersection (cons prim flg*) non-useless-code)) 
								(values `(,prim ,x* ...) 'useless)
								(values `(,prim ,x* ...) 'usefull)))
						       (values `(quote ,val) 'useless)))
					       (if (null? (intersection (cons prim flg*) non-useless-code)) 
						   (values `(,prim ,x* ...) 'useless)
					 	   (values `(,prim ,x* ...) 'usefull)))]
		      [(boolean? fixnum? null? pair? vector? procedure?) 
			 (let ([xpr (if (isImmediate (unquote* (car x*))) `(quote ,(eval `(,prim ,(car x*)))) `(,prim ,x* ...))])
			      (if (null? (intersection (cons prim flg*) non-useless-code))
				  (values xpr 'useless)
				  (values xpr 'usefull)))]
		      [(eq?) 
			 (let ([xpr (if (and (isImmediate (unquote* (car x*))) (isImmediate (unquote* (cadr x*))))
					`(quote ,(eval `(,prim ,(car x*) ,(cadr x*))))
				       `(,prim ,x* ...))])
			      (if (null? (intersection (cons prim flg*) non-useless-code)) 	 
				  (values xpr 'useless)
				  (values xpr 'usefull)))]
		      [else (if (null? (intersection (cons prim flg*) non-useless-code)) 
				(values `(,prim ,x* ...) 'useless)
			 	(values `(,prim ,x* ...) 'usefull))])
		    (if (null? (intersection (cons prim flg*) non-useless-code)) 
			(values `(,prim ,x* ...) 'useless)
			(values `(,prim ,x* ...) 'usefull)))]
              [(,[(Expr cp) -> x flg] ,[(Expr cp) -> y flg*] ...)
		 (if (null? (intersection (append (list flg) flg*) non-useless-code)) 
		     (values `(,x ,y ...) 'usefull)
		     (values `(,x ,y ...) 'usefull))]
              [,x (error who "invalid Expr ~s" x)]))))
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      ((Expr '())  x)))
  (lambda (x)
    (begin
      ;(printf "here --- \n")
      (let-values ([(prg fvar) (Program x)]) prg))))

)
