#|
Program name    : sanitize-binding-forms.ss
Functions       : sanitize-binding-forms
Description     : This program partition let bindings into two sets - one with lambda bindings and another
		  without lambda bindings
Input Language  : Scheme with anonymous lambda
Output Language : Scheme with lambda bindings separated
|#

(library (Compiler sanitize-binding-forms)
  (export sanitize-binding-forms)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass8 of the compiler
(define-who sanitize-binding-forms
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; It checks for lambda forms
  (define check-match
    (lambda (bind)
      (match bind
	[(lambda (,fml* ...) ,x) #t]
	[,x #f])))
  ;; It partition the let bindings into two of which one is with lambda forms
  (define partition-bindings
    (lambda (uvar binds outer-binds inner-binds)
      (cond
	((null? uvar) (values outer-binds inner-binds))
	(else 
	  (if (check-match (car binds)) 
	      (partition-bindings (cdr uvar) (cdr binds) (cons (list (car uvar) (car binds)) outer-binds) inner-binds)
	      (partition-bindings (cdr uvar) (cdr binds) outer-binds (cons (list (car uvar) (car binds)) inner-binds)))))))
  (define Program
    (lambda (x)
      ;; It sanitize binding forms in expression part of the grammer
      (define Expr
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[Expr -> x1] ,[Expr -> x2] ,[Expr -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[Expr -> x1*] ... ,[Expr -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[Expr -> x*]] ...) ,[Expr -> x]) 
		 (let-values ([(outer-binds inner-binds) (partition-bindings uvar* x* '() '())])
			     (if (and (null? outer-binds) (null? inner-binds))
			         x
			         (if (and (null? outer-binds) (not (null? inner-binds)))
			            `(let (,inner-binds ...) ,x)
				     (if (and (not (null? outer-binds)) (null? inner-binds))
					`(letrec (,outer-binds ...) ,x)
			                `(letrec (,outer-binds ...) (let (,inner-binds ...) ,x))))))]
	      [(lambda (,fml* ...) ,[Expr -> x]) `(lambda (,fml* ...) ,x)]
              [(letrec ([,new-uvar* (lambda (,fml* ...) ,[Expr -> x*])] ...) ,[Expr -> x])
		 `(letrec ([,new-uvar* (lambda (,fml* ...) ,x*)] ...) ,x)]
              [(,prim ,[Expr -> x*] ...) (guard (memq prim primitives)) `(,prim ,x* ...)]
              [(,[Expr -> x] ,[Expr -> y] ...) `(,x ,y ...)]
              [,x (error who "invalid Expr ~s" x)])))
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      (Expr x)))
  (lambda (x)
    (begin 
      (let ([prg (Program x)]) prg))))

)
