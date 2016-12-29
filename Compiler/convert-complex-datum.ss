#|
Program name    : convert-complex-datum.ss
Functions       : convert-complex-datum
Description     : This program will replace pairs and vectors with cons and make-vector statements
Input Language  : Scheme with quoted pairs and vectors
Output Language : Scheme with quoted pairs and vectors replaced by cons and make-vector
|#

(library (Compiler convert-complex-datum)
  (export convert-complex-datum)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass2 of the compiler
(define-who convert-complex-datum
  (define let-binds '())
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; Check if given expression is immediate
  (define (constant? x)
    (or (memq x '(#t #f ()))
        (and (and (integer? x) (exact? x))
             (or (fixnum-range? x)
                 (error who "integer ~s is out of fixnum range" x)))))
  ;; Check if given expression is a datum
  (define (datum? x)
    (or (constant? x)
        (if (pair? x)
            (and (datum? (car x)) (datum? (cdr x)))
            (and (vector? x) (andmap datum? (vector->list x))))))
  ;; Build the cons or make-vector statements for a given pair or vector
  (define build-datum
    (lambda (x)
      (cond
        ((constant? x) `(quote ,x))
        ((vector? x) 
	   (match x		
	     [#(,[build-datum -> x*] ...) (let ([tmp (unique-name 'tmp)])
 			  		        `(let ([,tmp (make-vector ',(length x*))])
			        		      (begin
				  		       ,(build-datum* x* 0 (length x*) tmp) ... ,tmp)))]))
        (else `(cons ,(build-datum (car x)) ,(build-datum (cdr x)))))))
  ;; Builds the intermediate vector-set! statements
  (define build-datum*
    (lambda (x* leng1 leng2 tmp)
      (cond
        ((equal? leng1 leng2) '())
        (else (cons `(vector-set! ,tmp ',leng1 ,(car x*)) (build-datum* (cdr x*) (add1 leng1) leng2 tmp))))))
  (define Program
    (lambda (x)
      ;; Convert complex datum from expression part of the grammer
      (define Expr
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,x) (guard (datum? x)) (if (constant? x) 
						 `(quote ,x) 
						 (let ([uvar (unique-name 't)])
						      (begin     
						        (set! let-binds (cons `(,uvar ,(build-datum x)) let-binds))
						        uvar)))]
              [(if ,[Expr -> x1] ,[Expr -> x2] ,[Expr -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[Expr -> x1*] ... ,[Expr -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[Expr -> x*]] ...) ,[Expr -> x]) `(let ([,uvar* ,x*] ...) ,x)]
	      [(lambda (,fml* ...) ,[Expr -> x]) `(lambda (,fml* ...) ,x)]
              [(letrec ([,uvar* ,[Expr -> x*]] ...) ,[Expr -> x]) `(letrec ([,uvar* ,x*] ...) ,x)]
	      [(set! ,uvar ,[Expr -> x]) `(set! ,uvar ,x)]
              [(,prim ,[Expr -> x*] ...) (guard (memq prim primitives)) `(,prim ,x* ...)]
              [(,[Expr -> x] ,[Expr -> y] ...) `(,x ,y ...)]
              [,x (error who "invalid Expr ~s" x)])))
      (Expr  x)))
  (lambda (x)
    (begin 
      (set! let-binds '())
      (let ([prg (Program x)]) `(let ,let-binds ,prg)))))

)

