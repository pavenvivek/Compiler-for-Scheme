#|
Program name    : normalize-context.ss
Functions       : normalize-context
Description     : This program restructure the code such that each expressions will occur in meaningfull contexts.
Input Language  : Scheme with improper contexts
Output Language : Scheme with meaningful contexts
|#

#!chezscheme
(library (Compiler normalize-context)
  (export
    normalize-context)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers)
    (Framework prims))

;; Defines pass18 of the compiler
(define-who normalize-context
  (define value-prims?
    (lambda (x)
      (memq x '(make-procedure procedure-ref procedure-code))))
  (define effect-prims?
    (lambda (x)
      (equal? x 'procedure-set!)))
  (define pred-prims?
    (lambda (x)
      (equal? x 'procedure?)))
  (define (make-nopless-begin x*)
    (let ([x* (remove '(nop) x*)])
      (if (null? x*)
         '(nop)
          (make-begin x*))))
  ;; Process Value part of the grammer
  (define Value
    (lambda (val)
      (match val
	[,label (guard (label? label)) label]
	[,uvar (guard (uvar? uvar)) uvar]
	[(void) val]
	[(quote ,Immediate) (guard (isImmediate Immediate)) `(quote ,Immediate)] 
        [(if ,[Pred -> p] ,[Value -> v1] ,[Value -> v2]) `(if ,p ,v1 ,v2)]
        [(begin ,[Effect -> ef] ... ,[Value -> v]) (make-nopless-begin`(,ef ... ,v))]
        [(let ([,uvar* ,[Value -> v1]] ...) ,[Value -> v2]) `(let ([,uvar* ,v1] ...) ,v2)]
	[(,prim ,[Value -> x*] ...) (guard (or (checkValPrim prim) (value-prims? prim))) `(,prim ,x* ...)]
	[(,prim ,[Value -> x*] ...) (guard (or (checkEffectPrim prim) (effect-prims? prim))) (make-nopless-begin `((,prim ,x* ...) (void)))]
	[(,prim ,[Value -> x*] ...) (guard (or (checkPredPrim prim) (pred-prims? prim))) `(if (,prim ,x* ...) '#t '#f)]
        [(,[Value -> v1] ,[Value -> v2] ...) `(,v1 ,v2 ...)]
        [,st (errorf who "invalid syntax for Value ~s" val)])))
  ;; Process Effect part of the grammer
  (define Effect
    (lambda (st)
      (match st
        [(nop) `(nop)]
	[,label (guard (label? label)) `(nop)]
	[,uvar (guard (uvar? uvar)) `(nop)]
	[(void) `(nop)]
	[(quote ,Immediate) (guard (isImmediate Immediate)) `(nop)] 
        [(if ,[Pred -> p] ,[Effect -> ef1] ,[Effect -> ef2]) `(if ,p ,ef1 ,ef2)]
        [(begin ,[Effect -> ef1] ... ,[Effect -> ef2]) (make-nopless-begin `(,ef1 ... ,ef2))]
	[(let ([,uvar* ,[Value -> v]] ...) ,[Effect -> ef]) `(let ([,uvar* ,v] ...) ,ef)]
	[(,prim ,[Value -> x*] ...) (guard (or (checkEffectPrim prim) (effect-prims? prim))) `(,prim ,x* ...)]
	[(,prim ,[Effect -> x*] ...) (guard (or (checkPredPrim prim) (pred-prims? prim))) (make-nopless-begin x*)]
	[(,prim ,[Effect -> x*] ...) (guard (or (checkValPrim prim) (value-prims? prim))) (make-nopless-begin x*)]
	[(,[Value -> v1] ,[Value -> v2] ...) `(,v1 ,v2 ...)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; Process predicate part of the grammer
  (define Pred
    (lambda (pred)
      (match pred
        [(true) `(true)]
        [(false) `(false)]
	[,label (guard (label? label)) `(true)]
	[,uvar (guard (uvar? uvar)) `(if (eq? ,uvar '#f) (false) (true))]
	[(void) `(if (eq? ,pred '#f) (false) (true))]
	[(quote ,Immediate) (guard (isImmediate Immediate)) (if (eq? Immediate '#f) '(false) '(true))]
        [(if ,[Pred -> p1] ,[Pred -> p2] ,[Pred -> p3]) `(if ,p1 ,p2 ,p3)]
        [(begin ,[Effect -> ef] ... ,[Pred -> p]) (make-nopless-begin `(,ef ... ,p))]
	[(let ([,uvar* ,[Value -> v]] ...) ,[Pred -> p]) `(let ([,uvar* ,v] ...) ,p)]
	[(,prim ,[Value -> x*] ...) (guard (or (checkPredPrim prim) (pred-prims? prim))) `(,prim ,x* ...)]
	[(,prim ,[Value -> x*] ...) (guard (or (checkEffectPrim prim) (effect-prims? prim))) (make-nopless-begin `((,prim ,x* ...) (true)))]
	[(,prim ,[Value -> x*] ...) (guard (or (checkValPrim prim) (value-prims? prim))) `(if (eq? (,prim ,x* ...) '#f) (false) (true))]
	[(,[Value -> v1] ,[Value -> v2] ...) `(if (eq? (,v1 ,v2 ...) '#f) (false) (true))]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; Convert scheme primitives to UIL primitives
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda (,uvar* ...) ,[Value -> body*])] ...) ,[Value -> body])
          `(letrec ([,label* (lambda (,uvar* ...) ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))
)
