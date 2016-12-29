#|
Program name    : optimize-self-reference.ss
Functions       : optimize-self-reference
Description     : This program will remove the self-reference by removing each left-hand side of letrec from its own
		  closure and adjusting bind-free form and its body accordingly
Input Language  : Scheme will self-references
Output Language : Scheme with self-references removed
|#

#!chezscheme
(library (Compiler optimize-self-reference)
  (export
    optimize-self-reference)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass14 of the compiler
(define-who optimize-self-reference
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  ;; It replace var x with var y in a given list ls
  (define replace
    (lambda (ls x y)
      (cond
      	((null? ls) '())
	((equal? (car ls) x) (cons y (replace (cdr ls) x y)))
	(else (cons (car ls) (replace (cdr ls) x y))))))
  ;; Expose free variables and wrap it around lambda body
  (define Program
    (lambda (x)
      (define Expr
	(lambda (sref cp)
          (lambda (x)
            (match x
	      [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[(Expr sref cp) -> x1] ,[(Expr sref cp) -> x2] ,[(Expr sref cp) -> x3]) 
		`(if ,x1 ,x2 ,x3)]
              [(begin ,[(Expr sref cp) -> x1*] ... ,[(Expr sref cp) -> x1]) 
		 (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[(Expr sref cp) -> x*]] ...) ,[(Expr sref cp) -> x]) 
		`(let ([,uvar* ,x*] ...) ,x)]
              [(letrec ([,uvar* ,lmd*] ...) 
		       (closures ((,uvar ,label ,fvar* ...) ...) ,x))
		         (let* ([labl-uvar (map cons label uvar)]
				[cls-uv (map (lambda (x) (if (assq x labl-uvar) (cdr (assq x labl-uvar)) #f)) uvar*)]
				[Lambda* (map (lambda (x y) (Lambda x y)) lmd* cls-uv)]
				[x* ((Expr sref cp) x)]
				[fvar** (map (lambda (x) (replace x sref cp)) fvar*)]
				[closure* (map (lambda (x y z) `(,x ,y ,(difference z (list x)) ...)) uvar label fvar**)])
                	      `(letrec ([,uvar* ,Lambda*] ...) (closures (,closure* ...) ,x*)))]
              [(,prim ,[(Expr sref cp) -> x*] ...) (guard (memq prim primitives))
		`(,prim ,x* ...)]
              [(,[(Expr sref cp) -> x] ,[(Expr sref cp) -> y] ,[(Expr sref cp) -> z] ...)
		 (if (equal? y sref)
		    `(,x ,cp ,(replace z sref cp) ...)
		    `(,x ,y ,(replace z sref cp) ...))]
              [,x (error who "invalid Expr ~s" x)]))))
      ;; Lambda helper
      (define Lambda
	(lambda (expr sref)
	  (match expr
	    [(lambda (,uvar* ...) (bind-free (dummy) ,x*))
	       (let ([ex* ((Expr sref '()) x*)])
		       `(lambda (,uvar* ...) (bind-free (dummy) ,ex*)))]
	    [(lambda (,cp ,uvar* ...) (bind-free (,cp ,wkvar* ...) ,x*))
	       (let ([ex* ((Expr sref cp) x*)])
		    (if sref
		       `(lambda (,cp ,uvar* ...) (bind-free (,cp ,(difference wkvar* (list sref)) ...) ,ex*))
		       `(lambda (,cp ,uvar* ...) (bind-free (,cp ,wkvar* ...) ,ex*))))])))
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      ((Expr '() '()) x)))
  (lambda (x)
    (begin
      (let ([prg (Program x)]) prg))))
)
