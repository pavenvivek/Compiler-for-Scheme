#|
Program name    : lift-letrec.ss
Functions       : lift-letrec
Description     : This program move the inner nested letrec statements to outside and wrap it around
                  the remaining statements
Input Language  : Scheme with procedure primitives and nested letrec
Output Language : Scheme with letrec moved to outside
|#

#!chezscheme
(library (Compiler lift-letrec)
  (export
    lift-letrec)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass17 of the compiler
(define-who lift-letrec
  (define letrec-bindings '())
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure? procedure-ref procedure-set! make-procedure procedure-code))
  ;; moves the nested letrecs outside
  (define Program
    (lambda (x)
      (define Expr
          (lambda (x)
            (match x
              [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[Expr -> x1] ,[Expr -> x2] ,[Expr -> x3]) `(if ,x1 ,x2 ,x3)]
              [(begin ,[Expr -> x1*] ... ,[Expr -> x1]) (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[Expr -> x*]] ...) ,[Expr -> x]) `(let ([,uvar* ,x*] ...) ,x)]
              [(letrec ([,label* (lambda (,uvar* ...) ,[Expr -> x*])] ...) ,[Expr -> x])
                 (begin 
                   (set! letrec-bindings (append `([,label* (lambda (,uvar* ...) ,x*)] ...) letrec-bindings))
		   x)]
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
      (set! letrec-bindings '())
      (let ([prg (Program x)]) 
          `(letrec ,letrec-bindings ,prg)))))
)
