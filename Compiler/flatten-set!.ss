#|
Program name    : flatten-set!.ss
Functions       : flatten-set!
Description     : This program restructure the set! statements to a form more closer to the assembly language.
Input Language  : Scheme with complex operations removed
Output Language : Scheme with set! statements flattened
|#

#!chezscheme
(library (Compiler flatten-set!)
(export
    flatten-set!)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass24 of the compiler
(define-who flatten-set!
  (define uvars-list '())
  (define relops '(< > <= >= =))
  (define binops '(+ - * logand logor sra))
  (define Triv?
    (lambda (t)
      (if (or (uvar? t) (integer? t) (label? t)) #t #f)))
  ;; It flatten set! statements in the Value part of the grammer
  ;; It process if, begin, binop and trivial statements and flatten the set! statements in them
  (define Value
    (lambda (val uvar)
      (match val
        [(if ,[Pred -> test] ,conseq ,altern) `(if ,test ,(Value conseq uvar) ,(Value altern uvar))]
        [(begin ,[Effect -> ef*] ... ,val) (make-begin `(,ef* ... ,(Value val uvar)))]
        [(,binop ,t1 ,t2) (guard (memq binop binops)) `(set! ,uvar (,binop ,t1 ,t2))]
	[(,Triv ,Triv* ...) `(set! ,uvar (,Triv ,Triv* ...))]
        [,triv `(set! ,uvar ,triv)])))
  ;; It flatten set! statements in the Effect part of the grammer
  ;; It process if, begin, nop and set! statements and flatten the set! statements in them
  (define Effect
    (lambda (st)
      (match st
        [(nop) `(nop)]
        [(set! ,uvar ,val) (Value val uvar)]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) (make-begin `(,effect* ... ,effect))]
	[(,Triv ,Triv* ...) `(,Triv ,Triv* ...)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It flatten set! statements in the Predicate part of the grammer
  ;; It process if, begin, (boolean) and relop statements and flatten the set! statements in them
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) (make-begin `(,effect* ... ,pred))]
        [(true) `(true)]
        [(false) `(false)]
        [(,relop ,t1 ,t2) (guard (memq relop relops)) `(,relop ,t1 ,t2)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It flatten set! statements in the Tail part of the grammer
  ;; It process if, begin, binop, (Triv Triv*) and trivial statements and flatten the set! statements in them
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
         (make-begin `(,ef* ... ,tail))]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2]) `(if ,pred ,tail1 ,tail2)]
        [(,binop ,t1 ,t2)
           (guard (memq binop binops)) `(,binop ,t1 ,t2)]
        [(,Triv ,Triv* ...) `(,Triv ,Triv* ...)]
        [,triv triv]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It flatten set! statements in the Body part of grammer
  ;; It process locals statements and flatten the set! statements in them
  (define Body
    (lambda (bexp)
      (match bexp
        [(locals (,uvar* ...) ,[Tail -> tail])
           `(locals (,uvar* ...) ,tail)]
        [,b (error who "invalid syntax for Body" b)])))
  ;; It flatten set! statements in the program
  ;; It process letrec statements and flatten the set! statements in them
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda (,uvar* ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda (,uvar* ...) ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))  
)
