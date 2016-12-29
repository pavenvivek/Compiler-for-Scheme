#|
Program name    : finalize-frame-locations.ss
Functions       : finalize-frame-locations
Description     : This program perform two functions. The first one is to replace the uvars in the program
                  with corresponding locations. The second function is to replace ineffectual statements
                  [like (set! x y) where x and y resolves to same location] to nop.
Input Language  : Scheme with live variables discarded
Output Language : Scheme with uvars replaced by corresponding locations and (locate ...), (nop) statements
                  removed 
|#

#!chezscheme
(library (Compiler finalize-frame-locations)
  (export
    finalize-frame-locations)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass35 of the compiler
(define-who finalize-frame-locations
  (define uvars-list '())
  (define location-list '())
  ;; it will identify the corresponding location for a given uvar from the location-list
  (define Triv
    (lambda (t)
      (if (and (uvar? t) (memv t uvars-list)) (list-ref location-list (- (length uvars-list) (length (memv t uvars-list)))) t)))
  ;; It finalize locations of the Effect* part of grammer
  ;; It process set!, if, begin statements and replace the uvars with locations
  ;; and it also remove the nop statements in Effect*
  (define Effect
    (lambda (st)
      (match st
	[(set! ,[Triv -> lhs] (mref ,[Triv -> x] ,[Triv -> y])) `(set! ,lhs (mref ,x ,y))]
        [(set! ,[Triv -> var] (,binop ,[Triv -> t1] ,[Triv -> t2]))
         `(set! ,var (,binop ,t1 ,t2))]
        [(set! ,[Triv -> var] ,[Triv -> t]) (if (equal? var t) `(nop) `(set! ,var ,t))]
	[(mset! ,[Triv -> val1] ,[Triv -> val2] ,[Triv -> val3]) `(mset! ,val1 ,val2 ,val3)]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) `(begin ,effect* ... ,effect)]
	[(return-point ,rp-label ,[Tail -> tail]) `(return-point ,rp-label ,tail)]
        [(,x) (guard (equal? x 'nop)) `(,x)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It finalize locations of the Predicate part of grammer
  ;; It process if, begin, relop, bool statements and replace the uvars with locations
  ;; in Predicate
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) `(begin ,effect* ... ,pred)]
        [(,bool) `(,bool)]
        [(,relop ,[Triv -> triv1] ,[Triv -> triv2]) `(,relop ,triv1 ,triv2)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It finalize locations of the Tail part of grammer
  ;; It process (triv), if, begin statements and replace the uvars with locations
  ;; in Tail
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
         `(begin ,ef* ... ,tail)]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2]) `(if ,pred ,tail1 ,tail2)]
        ;[(,[Triv -> t]) `(,t)]
        [(,[Triv -> triv] ,[Triv -> loc*] ...) `(,triv ,loc* ...)]
        ;(let ([liv-lst (union (list triv) loc*)]) (union live-list (live-var? liv-lst)))]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It finalize locations of the Body part of grammer
  ;; It process locate statements and set the uvars-list and location-list
  (define Body
    (lambda (bexp)
      (match bexp
        [(locals (,uvar* ...) (ulocals (,uvar2* ...) (locate ([,uvar3* ,Loc*] ...) (frame-conflict (,cflist* ...) ,tail))))
         (set! uvars-list uvar3*) 
         (set! location-list Loc*)
         `(locals (,uvar* ...) (ulocals (,uvar2* ...) (locate ([,uvar3* ,Loc*] ...) (frame-conflict (,cflist* ...) ,(Tail tail)))))]
        [(locate (,x* ...) ,tail) `(locate (,x* ...) ,tail)]
        [,b (error who "invalid syntax for Body" b)])))
  ;; It finalize locations in the program
  ;; It process letrec statements and replace the uvars with locations
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))  
)
