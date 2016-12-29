#|
Program name    : uncover-free.ss
Functions       : uncover-free
Description     : This program will identify the free variables inside letrec body
Input Language  : Scheme
Output Language : Scheme with free variables exposed
|#

#!chezscheme
(library (Compiler uncover-free)
  (export
    uncover-free)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass9 of the compiler
(define-who uncover-free
  (define free-vars '())
  (define formal-vars '())
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; Expose free variables and wrap it around lambda body
  (define Program
    (lambda (x)
      (define Expr
          (lambda (x)
            (match x
              [,uvar (guard (uvar? uvar)) (values uvar (list uvar))]
              [(quote ,[Immediate ->]) (values x '())]
              [(if ,[Expr -> x1 test-fvar] ,[Expr -> x2 conseq-fvar] ,[Expr -> x3 alt-fvar]) 
		 (values `(if ,x1 ,x2 ,x3) (union test-fvar conseq-fvar alt-fvar))]
              [(begin ,[Expr -> x1* x1*-fvar] ... ,[Expr -> x1 x1-fvar]) 
		 (values (make-begin `(,x1* ... ,x1)) (union (apply union x1*-fvar) x1-fvar))]
              [(let ([,uvar* ,[Expr -> x* x*-fvar]] ...) ,[Expr -> x x-fvar]) 
		 (values `(let ([,uvar* ,x*] ...) ,x) (difference (union (apply union x*-fvar) x-fvar) uvar*))]
              [(letrec ([,uvar* ,[Lambda -> lmd* fvar*]] ...) ,[Expr -> x x-fvar])
                 (values `(letrec ([,uvar* ,lmd*] ...) ,x) (difference (union (apply union fvar*) x-fvar) uvar*))]
              [(,prim ,[Expr -> x* x*-fvar] ...) (guard (memq prim primitives)) 
		 (values `(,prim ,x* ...) (apply union x*-fvar))]
              [(,[Expr -> x x-fvar] ,[Expr -> y y-fvar] ...) (values `(,x ,y ...) (union x-fvar (apply union y-fvar)))]
              [,x (error who "invalid Expr ~s" x)])))

      (define Lambda
	(lambda (expr)
	  (match expr
	    [(lambda (,uvar* ...) ,ex)
	       (let-values ([(ex* fvar) (Expr ex)])
		 (let ([fvars (difference fvar uvar*)])
		   (values `(lambda (,uvar* ...) (free ,fvars ,ex*)) fvars)))])))

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
      (let-values ([(prg fvar) (Program x)]) prg))))
)
