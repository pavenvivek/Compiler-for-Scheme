#|
Program name    : purify-letrec.ss
Functions       : purify-letrec
Description     : This program will restructure letrec statements to include only unassigned variables 
		  binding to lambda forms
Input Language  : Scheme with assigned variables exposed and impure letrec statements
Output Language : Scheme with pure letrec statements
|#

#!chezscheme
(library (Compiler purify-letrec)
  (export
    purify-letrec)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass4 of the compiler
(define-who purify-letrec
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  (define Program
    (lambda (x)
      ;; Purify letrec from expression part of the grammer
      (define Expr
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[Expr -> x1] ,[Expr -> x2] ,[Expr -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[Expr -> x1*] ... ,[Expr -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[Expr -> x*]] ...) (assigned (,asg* ...) ,[Expr -> x])) `(let ([,uvar* ,x*] ...) (assigned (,asg* ...) ,x))]
	      [(lambda (,fml* ...) (assigned (,asg* ...) ,[Expr -> x])) `(lambda (,fml* ...) (assigned (,asg* ...) ,x))]
	      [(letrec ([,uvar* (lambda (,fml* ...) (assigned (,asg* ...) ,[Expr -> x*]))] ...) (assigned () ,[Expr -> x]))
		`(letrec ([,uvar* (lambda (,fml* ...) (assigned (,asg* ...) ,x*))] ...) ,x)]
              [(letrec ([,uvar* ,[Expr -> x*]] ...) (assigned (,asg! ...) ,[Expr -> x])) 
		(let ([new-uvars (map (lambda (x) (unique-name (string->symbol (extract-root x)))) uvar*)]
		      [void* (map (lambda (x) '(void)) uvar*)])
		    `(let ([,uvar* ,void*] ...) 
			  (assigned (,uvar* ...) 
			   ,(make-begin
			      `((let ([,new-uvars ,x*] ...) 
			             (assigned ()
				       ,(make-begin `((set! ,uvar* ,new-uvars) ... )))) ,x)))))]
	      [(set! ,uvar ,[Expr -> x]) `(set! ,uvar ,x)]
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
      (Expr  x)))
  (lambda (x)
    (let ([prg (Program x)]) prg)))

)

