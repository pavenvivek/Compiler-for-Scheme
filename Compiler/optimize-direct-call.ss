#|
Program name    : optimize-direct-call.ss
Functions       : optimize-direct-call
Description     : This program replaces direct lambda call with simple let expression
Input Language  : Scheme with direct lambda calls
Output Language : Scheme with direct lambda calls replaced by let expression
|#

(library (Compiler optimize-direct-call)
  (export optimize-direct-call)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass6 of the compiler
(define-who optimize-direct-call
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  (define Program
    (lambda (x)
      ;; Optimize direct calls in expression part of the grammer
      (define Expr
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[Expr -> x1] ,[Expr -> x2] ,[Expr -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[Expr -> x1*] ... ,[Expr -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[Expr -> x*]] ...) ,[Expr -> x]) `(let ([,uvar* ,x*] ...) ,x)]
	      [((lambda (,uvar* ...) ,[Expr -> x*]) ,[Expr -> expr*] ...)
		 `(let ([,uvar* ,expr*] ...) ,x*)]
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
      (Expr  x)))
  (lambda (x)
    (begin 
      (let ([prg (Program x)]) prg))))

)

