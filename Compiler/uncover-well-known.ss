#|
Program name    : uncover-well-known.ss
Functions       : uncover-well-known
Description     : This program will identify the well-known variables bound by closure form
Input Language  : Scheme
Output Language : Scheme with well-known variables exposed
|#

#!chezscheme
(library (Compiler uncover-well-known)
  (export
    uncover-well-known)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass12 of the compiler
(define-who uncover-well-known
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; Expose well-known variables and wrap it around closure body
  (define Program
    (lambda (x)
      (define Expr
          (lambda (x)
            (match x
	      [,label (guard (label? label)) (values label '())]
              [,uvar (guard (uvar? uvar)) (values uvar (list uvar))]
              [(quote ,[Immediate ->]) (values x '())]
              [(if ,[Expr -> x1 test-wkvar] ,[Expr -> x2 conseq-wkvar] ,[Expr -> x3 alt-wkvar]) 
		 (values `(if ,x1 ,x2 ,x3) (union test-wkvar conseq-wkvar alt-wkvar))]
              [(begin ,[Expr -> x1* x1*-wkvar] ... ,[Expr -> x1 x1-wkvar]) 
		 (values (make-begin `(,x1* ... ,x1)) (union (apply union x1*-wkvar) x1-wkvar))]
              [(let ([,uvar* ,[Expr -> x* x*-wkvar]] ...) ,[Expr -> x x-wkvar]) 
		 (values `(let ([,uvar* ,x*] ...) ,x) (union (apply union x*-wkvar) x-wkvar))]
              [(letrec ([,uvar* ,[Lambda -> lmd* wkvar*]] ...) (closures ((,uvar ,label ,wkvar** ...) ...) ,[Expr -> x x-wkvar]))
                 (values `(letrec ([,uvar* ,lmd*] ...) (closures ((,uvar ,label ,wkvar** ...) ...) 
						       (well-known ,(difference uvar (union (apply union wkvar*) x-wkvar)) ,x))) 
			  (union (apply union wkvar*) x-wkvar))]
              [(,prim ,[Expr -> x* x*-wkvar] ...) (guard (memq prim primitives)) 
		 (values `(,prim ,x* ...) (apply union x*-wkvar))]
              [(,[Expr -> x x-wkvar] ,[Expr -> y y-wkvar] ,[Expr -> z z-wkvar] ...) 
		 (if (not (label? x))
		     (values `(,x ,y ,z ...) (union x-wkvar y-wkvar (apply union z-wkvar)))
		     (values `(,x ,y ,z ...) (union x-wkvar (apply union z-wkvar))))]
              [,x (error who "invalid Expr ~s" x)])))

      (define Lambda
	(lambda (expr)
	  (match expr
	    [(lambda (,cp ,uvar* ...) (bind-free (,cp ,wkvar* ...) ,x*))
	       (let-values ([(ex* wkvar) (Expr x*)])
		   (values `(lambda (,cp ,uvar* ...) (bind-free (,cp ,wkvar* ...) ,ex*)) wkvar))])))

      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      (Expr  x)))
  (lambda (x)
    (begin 
      (let-values ([(prg wkvar) (Program x)]) prg))))

)
