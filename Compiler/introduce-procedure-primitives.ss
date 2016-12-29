#|
Program name    : introduce-procedure-primitives.ss
Functions       : introduce-procedure-primitives
Description     : This program complete closure conversion by introducing procedure primitives and eliminating
		  bind-free and closure forms
Input Language  : Scheme with closure form
Output Language : Scheme with procedure primitives
|#

(library (Compiler introduce-procedure-primitives)
  (export introduce-procedure-primitives)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass15 of the compiler
(define-who introduce-procedure-primitives
  (define letrec-bindings '())
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; It returns the index of free variables
  (define get-index
    (lambda (x lst n)
      (cond
        ((null? lst) 0)
        ((equal? (car lst) x) n)
	(else (get-index x (cdr lst) (add1 n))))))
  ;; It builds the body of let for make-procedure
  (define get-proc-set
    (lambda (n cp fvar)
      (lambda (fvar* uvar)
        (cond
	  ((null? fvar*) '())
	  (else (cons `(procedure-set! ,uvar (quote ,(add1 n)) ,(if (memq (car fvar*) fvar) 
					     `		    (procedure-ref ,cp (quote ,(get-index (car fvar*) fvar 0)))
					      		    (car fvar*))) 
		       ((get-proc-set (add1 n) cp fvar) (cdr fvar*) uvar)))))))
  (define Program
    (lambda (x)
      ;; It handles the expression part of the grammer
      (define Expr
	(lambda (cp fvar)
          (lambda (x)
            (match x
	      [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) (if (memq uvar fvar) 
					     `(procedure-ref ,cp (quote ,(get-index uvar fvar 0)))
					      uvar)]
              [(quote ,[Immediate ->]) x]
              [(if ,[(Expr cp fvar) -> x1] ,[(Expr cp fvar) -> x2] ,[(Expr cp fvar) -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[(Expr cp fvar) -> x1*] ... ,[(Expr cp fvar) -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[(Expr cp fvar) -> x*]] ...) ,[(Expr cp fvar) -> x]) `(let ([,uvar* ,x*] ...) ,x)]
              [(letrec ([,label* ,[Lambda -> body*]] ...) (closures ((,uvar ,label ,fvar* ...) ...) ,[(Expr cp fvar) -> x]))
		 (let ([lengt (map length fvar*)]
		       [proc-set (map (get-proc-set -1 cp fvar) fvar* uvar)])
                 `(letrec ([,label* ,body*] ...)
		    (let ([,uvar (make-procedure ,label (quote ,lengt))] ...)
		      ,(make-begin `(,proc-set ... ... ,x)))))]
              [(,prim ,[(Expr cp fvar) -> x*] ...) (guard (memq prim primitives)) `(,prim ,x* ...)]
              [(,[(Expr cp fvar) -> x] ,[(Expr cp fvar) -> y] ,[(Expr cp fvar) -> z] ...)
		 (if (not (label? x))
		    `((procedure-code ,x) ,y ,z ...)
		    `(,x ,y ,z ...))]
              [,x (error who "invalid Expr ~s" x)]))))
      ;; It is a Lambda helper for handling letrec body
      (define Lambda
        (lambda (body)
	  (match body
	    [(lambda (,uvar* ...) (bind-free (dummy) ,[(Expr '() '()) -> x*]))
	       `(lambda (,uvar* ...) ,x*)]
	    [(lambda (,cp ,uvar* ...) (bind-free (,cp ,fvar* ...) ,[(Expr cp fvar*) -> x*]))
	       `(lambda (,cp ,uvar* ...) ,x*)])))
      ;; It handles the immediate part of the grammer
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      ((Expr '() '())  x)))
  (lambda (x)
    (begin
      (set! letrec-bindings '())
      (let ([prg (Program x)]) prg))))
)
