#|
Program name    : remove-let.ss
Functions       : remove-let
Description     : This program replace let expressions with appropriate set! expressions
Input Language  : Scheme with locals wrapper introduced
Output Language : Scheme with let removed
|#

#!chezscheme
(library (Compiler remove-let)
  (export
    remove-let)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass21 of the compiler
(define-who remove-let
  ;; It restructure the set! statements
  (define build-ins
    (lambda (x)
      (match x
        [(set! (,a ...) (,b ...)) `((set! ,a ,b) ...)])))
  ;; It removes let from the Value part of grammer 
  ;; It process if, begin, binop, alloc, let statements and removes let from Value
  (define Value
    (lambda (val)
      (match val
        [(let ([,new-uvar* ,[Value -> v1]] ...) ,[Value -> v2]) 
	   (make-begin (append (build-ins `(set! ,new-uvar* ,v1)) (list v2)))]
	[(if ,[Pred -> p] ,[Value -> v1] ,[Value -> v2]) `(if ,p ,v1 ,v2)]
        [(begin ,[Effect -> ef] ... ,[Value -> v]) (make-begin `(,ef ... ,v))]
        [(,binop ,[Value -> v1] ,[Value -> v2]) (guard (memq binop '(mref + - * logand logor sra))) `(,binop ,v1 ,v2)]
        [(alloc ,[Value -> v]) `(alloc ,v)]
        [(,[Value -> v1] ,[Value -> v2] ...) `(,v1 ,v2 ...)]
        [,triv triv])))
  ;; It removes let from the Effect part of grammer 
  ;; It process (nop), mset!, if, begin, let statements and removes let from Effect
  (define Effect
    (lambda (st)
      (match st
        [(nop) `(nop)]
	[(mset! ,[Value -> v1] ,[Value -> v2] ,[Value -> v3]) `(mset! ,v1 ,v2 ,v3)]
	[(let ([,new-uvar* ,[Value -> v]] ...) ,[Effect -> ef]) 
	   (make-begin (append (build-ins `(set! ,new-uvar* ,v)) (list ef)))]
	[(if ,[Pred -> p] ,[Effect -> ef1] ,[Effect -> ef2]) `(if ,p ,ef1 ,ef2)]
        [(begin ,[Effect -> ef1] ... ,[Effect -> ef2]) (make-begin `(,ef1 ... ,ef2))]
	[(,[Value -> v1] ,[Value -> v2] ...) `(,v1 ,v2 ...)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It removes let from the Predicate part of grammer 
  ;; It process if, begin, relop, bool, let statements and removes let from Predicate
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> p1] ,[Pred -> p2] ,[Pred -> p3]) `(if ,p1 ,p2 ,p3)]
        [(begin ,[Effect -> ef] ... ,[Pred -> p]) (make-begin `(,ef ... ,p))]
        [(true) `(true)]
        [(false) `(false)]
	[(let ([,new-uvar* ,[Value -> v]] ...) ,[Pred -> p]) 
	   (make-begin (append (build-ins `(set! ,new-uvar* ,v)) (list p)))]
        [(,relop ,[Value -> v1] ,[Value -> v2]) (guard (memq relop '(< > <= >= =))) `(,relop ,v1 ,v2)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It removes let from the Tail part of grammer
  ;; It process triv, if, begin, let, alloc statements and removes let from Tail
  (define Tail
    (lambda (tail)
      (match tail
	[(let ([,new-uvar* ,[Value -> v]] ...) ,[Tail -> t]) 
           (make-begin (append (build-ins `(set! ,new-uvar* ,v)) (list t)))]
        [(begin ,[Effect -> ef] ... ,[Tail -> t]) (make-begin `(,ef ... ,t))]
        [(if ,[Pred -> p] ,[Tail -> t1] ,[Tail -> t2]) `(if ,p ,t1 ,t2)]
	[(alloc ,[Value -> v1]) `(alloc ,v1)]
        [(,binop ,[Value -> v1] ,[Value -> v2])
           (guard (memq binop '(mref + - * logand logor sra)))
	   `(,binop ,v1 ,v2)]
        [(,[Value -> v1] ,[Value -> v2] ...) `(,v1 ,v2 ...)]
        [,triv triv])))
  ;; It removes let from the Body part of grammer
  ;; It process (label (lambda ...)) statements
  (define Body
    (lambda (bexp)
      (match bexp
        [(locals (,uvar* ...) ,[Tail -> tail]) `(locals (,uvar* ...) ,tail)]
        [,b (error who "invalid syntax for Body" b)])))
  ;; It removes let from the program
  ;; It process letrec statements and removes let expressions in them
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda (,uvar* ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda (,uvar* ...) ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))
)
