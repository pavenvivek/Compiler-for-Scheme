#|
Program name    : uncover-locals.ss
Functions       : uncover-locals
Description     : This program scans through lambda and letrec body to find let expressions and
		  stores the let variables inside locals wrapper
Input Language  : Scheme with UIL primitive calls
Output Language : Scheme with locals wrapper introduced
|#

#!chezscheme
(library (Compiler uncover-locals)
  (export
    uncover-locals)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass20 of the compiler
(define-who uncover-locals
  (define uvars-list '())
  (define Value
    (lambda (val)
      (match val
        [(let ([,new-uvar* ,[Value -> v1]] ...) ,[Value -> v2]) (begin (set! uvars-list (append uvars-list new-uvar*)) '())]
        [(if ,[Pred -> p] ,[Value -> v1] ,[Value -> v2]) '()]
        [(begin ,[Effect -> ef] ... ,[Value -> v]) '()]
        [(,binop ,[Value -> v1] ,[Value -> v2]) (guard (memq binop '(mref + - * logand logor sra))) '()]
        [(alloc ,[Value -> v]) '()]
        [(,[Value -> v1] ,[Value -> v2] ...) '()]
        [,triv '()])))
  (define Effect
    (lambda (st)
      (match st
        [(nop) '()]
	[(mset! ,[Value -> v1] ,[Value -> v2] ,[Value -> v3]) '()]
	[(let ([,new-uvar* ,[Value -> v]] ...) ,[Effect -> ef]) (begin (set! uvars-list (append uvars-list new-uvar*)) '())]
        [(if ,[Pred -> p] ,[Effect -> ef1] ,[Effect -> ef2]) '()]
        [(begin ,[Effect -> ef1] ... ,[Effect -> ef2]) '()]
	[(,[Value -> v1] ,[Value -> v2] ...) '()]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It uncover locals in the Predicate part of grammer 
  ;; It process if, begin, relop, bool, let statements and uncover locals in Predicate
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> p1] ,[Pred -> p2] ,[Pred -> p3]) '()]
        [(begin ,[Effect -> ef] ... ,[Pred -> p]) '()]
        [(true) '()]
        [(false) '()]
	[(let ([,new-uvar* ,[Value -> v]] ...) ,[Pred -> p]) (begin (set! uvars-list (append uvars-list new-uvar*)) '())]
        [(,relop ,[Value -> v1] ,[Value -> v2]) (guard (memq relop '(< > <= >= =))) '()]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It uncover locals in the Tail part of grammer
  ;; It process triv, if, begin, alloc, binop, let statements and uncover locals in Tail
  (define Tail
    (lambda (tail)
      (match tail
	[(let ([,new-uvar* ,[Value -> v]] ...) ,[Tail -> t]) (begin (set! uvars-list (append uvars-list new-uvar*)) '())]
        [(begin ,[Effect -> ef] ... ,[Tail -> t]) '()]
        [(if ,[Pred -> p] ,[Tail -> t1] ,[Tail -> t2]) '()]
	[(alloc ,[Value -> v1]) '()]
        [(,binop ,[Value -> v1] ,[Value -> v2])
           (guard (memq binop '(mref + - * logand logor sra)))
	   '()]
        [(,[Value -> v1] ,[Value -> v2] ...) '()]
        [,triv '()])))
  ;; It uncover locals in the Body part of grammer
  (define Body
    (lambda (tail)
      (begin
	(set! uvars-list '())
	(Tail tail))))
  ;; It uncover locals in the Body part of grammer
  ;; It process (label (lambda ...)) statements
   (define Lambda
    (lambda (code)
      (match code
        [(,label* (lambda (,uvar* ...) ,body*))
	   (Body body*)
          `[,label* (lambda (,uvar* ...) (locals (,uvars-list ...) ,body*))]]
	[,program (errorf who "invalid syntax for Code: ~s" program)])))
  ;; It uncover locals in the program
  ;; It process letrec statements
  (lambda (program)
    (match program
      [(letrec (,[Lambda -> x*] ...) ,body)
	 (begin
	   (Body body)
          `(letrec (,x* ...) (locals (,uvars-list ...) ,body)))]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))
)
