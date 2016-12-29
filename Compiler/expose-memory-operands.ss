#|
Program name    : expose-memory-operands.ss
Functions       : expose-memory-operands
Description     : This program converts the occurrences of mset and mref into displacement/index 
		  mode operands. Then it returns the modified code to the flatten-program pass.
		  It converts them as follows:
		  (mref ,t1 ,t2) -> if t2 is register then (make-index-opnd t1 t2) else (make-disp-opnd t1 t2)
		  (mset! ,val1 ,val2 ,val3) -> (set! 
						  if val2 is register then (make-index-opnd val1 val2) 
						  else (make-disp-opnd val1 val2) 
						val3)
Input Language  : Scheme code with frame-vars replaced by displacement mode operands
Output Language : Scheme code with mset!/mref replaced by displacement/index mode operands
|#

#!chezscheme
(library (Compiler expose-memory-operands)
  (export
    expose-memory-operands)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass39 of the compiler
(define-who expose-memory-operands
  ;; It process relop, if, begin, bool statements and restructure mset! and mref statements in Predicate
  (define Pred
    (lambda (pred)
      (match pred
        [(true) `(true)]
        [(false) `(false)]
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) `(begin ,effect* ... ,pred)]
        [(,relop ,triv1 ,triv2) `(,relop ,triv1 ,triv2)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It process set!, mset!, if, begin, return-point, nop statements and restructure mset! and mref statements in Effect
  (define Effect
    (lambda (st)
      (match st
  	[(set! ,var (mref ,t1 ,t2)) 
	`(set! ,var ,(if (register? t2) (make-index-opnd t1 t2) (make-disp-opnd t1 t2)))]
        [(set! ,var (,binop ,t1 ,t2)) (guard (memq binop '(+ - * logand logor sra)))
         `(set! ,var (,binop ,t1 ,t2))]
        [(set! ,var ,t) `(set! ,var ,t)]
	[(mset! ,val1 ,val2 ,val3) `(set! ,(if (register? val2) (make-index-opnd val1 val2) (make-disp-opnd val1 val2)) ,val3)]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) (make-begin `(,effect* ... ,effect))]
	[(return-point ,rp-label ,[Tail -> tail]) `(return-point ,rp-label ,tail)]
        [(,x) (guard (equal? x 'nop)) `(,x)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It process binop, if, begin statements and restructure mset! and mref statements in Tail
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
        `(begin ,ef* ... ,tail)]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2]) `(if ,pred ,tail1 ,tail2)]
	[(,binop ,t1 ,t2) (guard (memq binop '(+ - * logand logor sra))) `(,binop ,t1 ,t2)]
	[(,t) `(,t)]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It process letrec statements and restructure mset! and mref statements
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))
)
