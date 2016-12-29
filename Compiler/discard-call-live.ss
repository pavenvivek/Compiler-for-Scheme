#|
Program name    : discard-call-live.ss
Functions       : discard-call-live
Description     : This program discards the Loc* from (Triv Loc*) part of the grammer.
Input Language  : Scheme with locals list replaced by locate statement and registers assigned for uvars.
Output Language : Scheme with live variables discarded from each call.
|#

#!chezscheme
(library (Compiler discard-call-live)
  (export
    discard-call-live)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass36 of the compiler
(define-who discard-call-live
  ;; It discard live vars in the Effect part of grammer
  ;; It process set!, mset!, if, begin, return-point, nop statements
  (define Effect
    (lambda (st)
      (match st
        [(set! ,var ,expr) `(set! ,var ,expr)]
	[(mset! ,lhs ,var1 ,var2) `(mset! ,lhs ,var1 ,var2)]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) `(begin ,effect* ... ,effect)]
	[(return-point ,rp-label ,[Tail -> tail]) `(return-point ,rp-label ,tail)]
        [(,x) (guard (equal? x 'nop)) `(,x)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It discard live vars in the Predicate part of grammer
  ;; It process if, begin, relop, bool statements
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) `(begin ,effect* ... ,pred)]
        [(true) `(true)]
        [(false) `(false)]
        [(,relop ,triv1 ,triv2) `(,relop ,triv1 ,triv2)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It process (triv loc*) and will discard live vars in Tail
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
         `(begin ,ef* ... ,tail)]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2]) `(if ,pred ,tail1 ,tail2)]
        [(,triv ,loc* ...) `(,triv)]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It process locate statements
  (define Body
    (lambda (bexp)
      (match bexp
        [(locate (,loc* ...) ,[Tail -> tail])
        `(locate (,loc* ...) ,tail)]
        [,b (error who "invalid syntax for Body" b)])))
  ;; It process letrec statements and discard live variables from the program
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))  
)
