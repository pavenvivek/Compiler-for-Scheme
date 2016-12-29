#|
Program name    : expose-allocation-pointer.ss
Functions       : expose-allocation-pointer
Description     : This program will process the alloc statements and remove them from the grammer.
		  It changes the alloc statement as follows:
		  (set! var (alloc 16)) -> (set! var allocation-pointer-register)
        				   (set! allocation-pointer-register (+ allocation-pointer-register 16))
Input Language  : Scheme with calling conventions imposed
Output Language : Scheme with allocation pointers exposed
|#

#!chezscheme
(library (Compiler expose-allocation-pointer)
  (export
    expose-allocation-pointer)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

(define warn-if-dead-at-assignment (make-parameter #f))

;; Defines pass26 of the compiler
(define-who expose-allocation-pointer
  ;; It expose allocation pointer in the Value part of grammer
  (define Value
    (lambda (val)
      (match val
        [(if ,[Pred -> test] ,[Value -> conseq] ,[Value -> altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[Value -> val]) (make-begin `(,ef* ... ,val))]
	[(mref ,[Value -> val1] ,[Value -> val2]) `(mref ,val1 ,val2)]
        [(,binop ,[Value -> x] ,[Value -> y])
           (guard (memq binop '(+ - * logand logor sra)))
           `(,binop ,x ,y)]
	[(,[Value -> rator] ,[Value -> rand*] ...)
	   `(,rator ,rand* ...)]
        [,triv triv])))
  ;; It expose allocation pointer in the Effect part of grammer
  (define Effect
    (lambda (st)
      (match st
        [(nop) `(nop)]
	[(set! ,var (alloc ,[Value -> val])) 
	  (make-begin `((set! ,var ,allocation-pointer-register) 
	    (set! ,allocation-pointer-register (+ ,allocation-pointer-register ,val))))]
	[(set! ,uvar ,[Value -> val]) `(set! ,uvar ,val)]
	[(mset! ,[Value -> val1] ,[Value -> val2] ,[Value -> val3]) `(mset! ,val1 ,val2 ,val3)]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) (make-begin `(,effect* ... ,effect))]
	[(return-point ,rp-label ,[Tail -> tail]) `(return-point ,rp-label ,tail)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It expose allocation pointer in the Predicate part of grammer
  (define Pred
    (lambda (x)
      (match x
        [(true) `(true)]
        [(false) `(false)]
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) (make-begin `(,effect* ... ,pred))]
        [(,relop ,x ,y)
         `(,relop ,x ,y)]
        [,x (error who "invalid Pred ~s" x)])))
  ;; It expose allocation pointer in the Tail part of grammer
  (define Tail
    (lambda (x)
      (match x 
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail]) (make-begin `(,ef* ... ,tail))]
        [(if ,[Pred -> test] ,[Tail -> t1] ,[Tail -> t2]) `(if ,test ,t1 ,t2)]
	[(,binop ,[Value -> x] ,[Value -> y]) (guard (memq binop '(+ - * logand logor sra)))
	`(,binop ,x ,y)]
	[(,[Value -> rator] ,[Value -> rand*] ...) `(,rator ,rand* ...)] 
        [,triv triv]
        [,x (error who "invalid Tail ~s" x)])))
  ;; It expose allocation pointer in the Body part of grammer
  (define Body
    (lambda (x)
      (match x
        [(locals (,uvar* ...) (new-frames (,Frame* ...) ,[Tail -> tail])) 
           `(locals (,uvar* ...) (new-frames (,Frame* ...) ,tail))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body]) 
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
)
