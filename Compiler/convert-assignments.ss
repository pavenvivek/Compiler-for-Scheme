#|
Program name    : convert-assignments.ss
Functions       : convert-assignments
Description     : This program will replace assigned forms with let statements and it also replace
		  reference to assigned variables with car and set! with set-car! statements
Input Language  : Scheme with pure letrec statements and assigned forms
Output Language : Scheme with set! and assigned forms eliminated
|#

(library (Compiler convert-assignments)
  (export convert-assignments)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass5 of the compiler
(define-who convert-assignments
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; It replace the uvar list with new uvar assignments
  (define replace
    (lambda (lst asg)
      (cond
	((null? lst) '())
	((assv (car lst) asg) (cons (cdr (assv (car lst) asg)) (replace (cdr lst) asg)))
	(else (cons (car lst) (replace (cdr lst) asg))))))
  (define Program
    (lambda (x)
      ;; It convert assignments in expression part of the grammer
      (define Expr
	(lambda (asg)
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) (if (memq uvar asg) `(car ,uvar) uvar)]
              [(quote ,[Immediate ->]) x]
              [(if ,[(Expr asg) -> x1] ,[(Expr asg) -> x2] ,[(Expr asg) -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[(Expr asg) -> x1*] ... ,[(Expr asg) -> x1]) (make-begin `(,x1* ... ,x1))]
	      [(let ([,uvar* ,[(Expr asg) -> x*]] ...) (assigned () ,[(Expr asg) -> x]))
		 `(let ([,uvar* ,x*] ...) ,x)]
              [(let ([,uvar* ,[(Expr asg) -> x*]] ...) (assigned (,asg* ...) ,[(Expr (union asg* asg)) -> x]))
		 (let* ([new-uvars (map (lambda (x) (unique-name (string->symbol (extract-root x)))) asg*)]
		        [void* (map (lambda (x) '(void)) asg*)]
			[uv-asg (map cons asg* new-uvars)]
			[uvar** (replace uvar* uv-asg)])
		      `(let ([,uvar** ,x*] ...) (let ((,asg* (cons ,new-uvars ,void*)) ...) ,x)))]
	      [(lambda (,fml* ...) (assigned () ,[(Expr asg) -> x]))
		 `(lambda (,fml* ...) ,x)]
	      [(lambda (,fml* ...) (assigned (,asg* ...) ,[(Expr (union asg* asg)) -> x])) 
		 (let* ([new-uvars (map (lambda (x) (unique-name (string->symbol (extract-root x)))) asg*)]
		        [void* (map (lambda (x) '(void)) asg*)]
			[uv-asg (map cons asg* new-uvars)]
			[fml** (replace fml* uv-asg)])
		      `(lambda (,fml** ...) (let ((,asg* (cons ,new-uvars ,void*)) ...) ,x)))]
	      [(letrec ([,uvar* ,[(Expr asg) -> x*]] ...) ,[(Expr asg) -> x])
  		      `(letrec ([,uvar* ,x*] ...) ,x)]
	      [(set! ,uvar ,[(Expr asg) -> x]) `(set-car! ,uvar ,x)]
              [(,prim ,[(Expr asg) -> x*] ...) (guard (memq prim primitives)) `(,prim ,x* ...)]
              [(,[(Expr asg) -> x] ,[(Expr asg) -> y] ...) `(,x ,y ...)]
              [,x (error who "invalid Expr ~s" x)]))))
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      ((Expr '())  x)))
  (lambda (x)
    (let ([prg (Program x)]) prg)))

)

