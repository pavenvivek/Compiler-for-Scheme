#|
Program name    : uncover-assigned.ss
Functions       : uncover-assigned
Description     : This program will uncover the assigned variables within let, letrec and lambda forms
Input Language  : Scheme with quoted pairs and vectors replaced by cons and make-vector
Output Language : Scheme with assigned variables exposed
|#

#!chezscheme
(library (Compiler uncover-assigned)
  (export
    uncover-assigned)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass3 of the compiler
(define-who uncover-assigned
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; Expose assigned variables and wrap it around lambda body
  (define Program
    (lambda (x)
      ;; Uncover assigned vars from lambda part of the grammer
      (define Expr
          (lambda (x)
            (match x
              [,uvar (guard (uvar? uvar)) (values uvar '())]
              [(quote ,[Immediate ->]) (values x '())]
              [(if ,[Expr -> x1 test-asg] ,[Expr -> x2 conseq-asg] ,[Expr -> x3 alt-asg]) 
		 (values `(if ,x1 ,x2 ,x3) (union test-asg conseq-asg alt-asg))]
              [(begin ,[Expr -> x1* x1*-asg] ... ,[Expr -> x1 x1-asg]) 
		 (values (make-begin `(,x1* ... ,x1)) (union (apply union x1*-asg) x1-asg))]
              [(let ([,uvar* ,[Expr -> x* x*-asg]] ...) ,[Expr -> x x-asg]) 
		 (let ([asg* (intersection (union (apply union x*-asg) x-asg) uvar*)])
		      (values `(let ([,uvar* ,x*] ...) (assigned ,asg* ,x)) (union (apply union x*-asg) x-asg)))]
	      [(lambda (,fml* ...) ,[Expr -> x x-asg]) 
		 (let ([asg* (intersection x-asg fml*)])
		      (values `(lambda (,fml* ...) (assigned ,asg* ,x)) x-asg))]
              [(letrec ([,uvar* ,[Expr -> x* x*-asg]] ...) ,[Expr -> x x-asg])
		 (let ([asg* (intersection (union (apply union x*-asg) x-asg) uvar*)])
                      (values `(letrec ([,uvar* ,x*] ...) (assigned ,asg* ,x)) (union (apply union x*-asg) x-asg)))]
	      [(set! ,uvar ,[Expr -> x x-asg]) (values `(set! ,uvar ,x) (union (list uvar) x-asg))]
              [(,prim ,[Expr -> x* x*-asg] ...) (guard (memq prim primitives))
		 (values `(,prim ,x* ...) (apply union x*-asg))]
              [(,[Expr -> x x-asg] ,[Expr -> y y-asg] ...) (values `(,x ,y ...) (union x-asg (apply union y-asg)))]
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
      (let-values ([(prg asg) (Program x)]) prg))))
)
