#|
Program name    : convert-closures.ss
Functions       : convert-closures
Description     : This program will convert lambda expressions with free variables into lambda 
		  expressions without free variables and add a closure form which stores a pointer
		  to the procedure code and the value of free variables
Input Language  : Scheme with free variables exposed
Output Language : Scheme with closure form
|#

(library (Compiler convert-closures)
  (export convert-closures)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass10 of the compiler
(define-who convert-closures
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  (define get-label
    (lambda (uvar)
      (values (unique-label uvar) uvar)))
  ;; It returns a new closure parameter
  (define get-cp
    (lambda (cnt)
      (cond
	((zero? cnt) '())
	(else (cons (unique-name 'cp) (get-cp (sub1 cnt)))))))
  (define Program
    (lambda (x)
      ;; It handles the expression part of the grammer
      (define Expr
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[Expr -> x1] ,[Expr -> x2] ,[Expr -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[Expr -> x1*] ... ,[Expr -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[Expr -> x*]] ...) ,[Expr -> x]) `(let ([,uvar* ,x*] ...) ,x)]
              [(letrec ([,[get-label -> labl label*] (lambda (,uvar* ...) (free (,fvar* ...) ,[Expr -> x*]))] ...) ,[Expr -> x])
		  (let* ([cp-lst (get-cp (length label*))])
		      `(letrec ([,labl (lambda (,cp-lst ,uvar* ...) (bind-free (,cp-lst ,fvar* ...) ,x*))] ...)
			       (closures ([,label* ,labl ,fvar* ...] ...) ,x)))]
              [(,prim ,[Expr -> x*] ...) (guard (memq prim primitives)) `(,prim ,x* ...)]
              [(,[Expr -> x] ,[Expr -> y] ...) 
		 (if (uvar? x)
		    `(,x ,x ,y ...)
		     (let ([tmp (unique-name 'tmp)])
			 `(let ([,tmp ,x]) (,tmp ,tmp ,y ...))))]
              [,x (error who "invalid Expr ~s" x)])))
      ;; It handles the immediate part of the grammer
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
