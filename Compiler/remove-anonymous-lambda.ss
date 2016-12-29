#|
Program name    : remove-anonymous-lambda.ss
Functions       : remove-anonymous-lambda
Description     : This program assign unique name for anonymous lambda by wrapping them inside letrec
Input Language  : Scheme with direct lambda calls replaced by let expression
Output Language : Scheme with anonymous lambda named
|#

(library (Compiler remove-anonymous-lambda)
  (export remove-anonymous-lambda)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass7 of the compiler
(define-who remove-anonymous-lambda
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  (define Program
    (lambda (x)
      ;; It removes anonymous lambda from expression part of the grammer
      (define Expr
	(lambda (bool)
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[(Expr #f) -> x1] ,[(Expr #f) -> x2] ,[(Expr #f) -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[(Expr #f) -> x1*] ... ,[(Expr #f) -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[(Expr #t) -> x*]] ...) ,[(Expr #f) -> x]) `(let ([,uvar* ,x*] ...) ,x)]
	      [(lambda (,fml* ...) ,[(Expr #f) -> x]) 
		 (let ([anon (unique-name 'anon)])
		      (if bool
			`(lambda (,fml* ...) ,x)
		        `(letrec ([,anon (lambda (,fml* ...) ,x)]) ,anon)))]
              [(letrec ([,new-uvar* (lambda (,fml* ...) ,[(Expr #f) -> x*])] ...) ,[(Expr #f) -> x])
		 `(letrec ([,new-uvar* (lambda (,fml* ...) ,x*)] ...) ,x)]
              [(,prim ,[(Expr #f) -> x*] ...) (guard (memq prim primitives)) `(,prim ,x* ...)]
              [(,[(Expr #f) -> x] ,[(Expr #f) -> y] ...) `(,x ,y ...)]
              [,x (error who "invalid Expr ~s" x)]))))
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      ((Expr #f)  x)))
  (lambda (x)
    (begin 
      (let ([prg (Program x)]) prg))))

)

