#|
Program name    : optimize-known-call.ss
Functions       : optimize-known-call
Description     : This program optimize known calls by replacing the variable with corresponding label 
		  of the lambda expression to which it evaluates by using the closure form
Input Language  : Scheme with closure form
Output Language : Scheme with known calls optimized
|#

(library (Compiler optimize-known-call)
  (export optimize-known-call)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass11 of the compiler
(define-who optimize-known-call
  (define call-bindings '())
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; It zip elements from two list like : (1 2) & (a b) as ((1 a) (2 b))
  (define zip
    (lambda (lst1 lst2)
      (if (or (null? lst1) (null? lst2))
         '()
          (cons (list (car lst1) (car lst2)) (zip  (cdr lst1) (cdr lst2))))))
  (define Program
    (lambda (x)
      ;; It optimize known calls in expression part of the grammer
      (define Expr
          (lambda (x)
            (match x
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[Expr -> x1] ,[Expr -> x2] ,[Expr -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[Expr -> x1*] ... ,[Expr -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[Expr -> x*]] ...) ,[Expr -> x]) `(let ([,uvar* ,x*] ...) ,x)]
              [(letrec ([,label* ,body*] ...) (closures ((,uvar ,label ,fvar* ...) ...) ,x))
		 (begin
		   (set! call-bindings (append (zip uvar label) call-bindings))
		   (let ([lmd* (map Lambda body*)]
			 [x* (Expr x)])
			`(letrec ([,label* ,lmd*] ...) (closures ((,uvar ,label ,fvar* ...) ...) ,x*))))]
              [(,prim ,[Expr -> x*] ...) (guard (memq prim primitives)) `(,prim ,x* ...)]
              [(,[Expr -> x] ,[Expr -> x] ,[Expr -> y] ...) (if (and (uvar? x) (assq x call-bindings)) 
							       `(,(cadr (assq x call-bindings)) ,x ,y ...)
							       `(,x ,x ,y ...))]
              [,x (error who "invalid Expr ~s" x)])))
      ;; It defines a lambda helper to handle letrec lambda bindings
      (define Lambda
        (lambda (body)
	  (match body
	    ((lambda (,cp ,uvar* ...) (bind-free (,cp ,fvar* ...) ,[Expr -> x*]))
	       `(lambda (,cp ,uvar* ...) (bind-free (,cp ,fvar* ...) ,x*))))))
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
