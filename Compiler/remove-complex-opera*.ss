#|
Program name    : remove-complex-opera*.ss
Functions       : remove-complex-opera*
Description     : This program restructure the part of the code involving complex operations. It does so
		  by changing the subexpressions of primitive calls and procedure calls from Value to trivial
		  expressions.
Input Language  : Valid scheme code as per the grammer
Output Language : Scheme with complex operations removed
|#

#!chezscheme
(library (Compiler remove-complex-opera*)
  (export
    remove-complex-opera*)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass23 of the compiler
(define-who remove-complex-opera*
  (define uvars-list '())
  ;; It restructure the set! statements
  (define build-ins
    (lambda (x)
      (match x
        [(set! (,a ...) (,b ...)) `((set! ,a ,b) ...)])))
  ;; It generate uvars for non-trivial statements in (Value Value*) part of the grammer
  (define generate-uvar
    (lambda (n ls)
      (cond
        ((zero? n) ls)
        (else (cons (unique-name 't) (generate-uvar (sub1 n) ls))))))
  ;; It returns true if the given variable is trivial
  (define Triv?
    (lambda (t)
      (if (or (uvar? t) (integer? t) (label? t)) #t #f)))
  (define union-list
    (lambda (rand* triv ulist)
      (cond
        ((null? rand*) '())
        ((Triv? (car rand*)) (cons (car triv) (union-list (cdr rand*) (cdr triv) ulist)))
        (else (cons (car ulist) (union-list (cdr rand*) triv (cdr ulist)))))))
  ;; It remove complex operations from the Value part of the grammer
  ;; It process if, begin, alloc, mref, binop expressions and trivial statements and 
  ;; remove complex operations in them
  (define Value
    (lambda (val)
      (match val
        [(if ,[Pred -> test] ,[Value -> conseq] ,[Value -> altern]) `(if ,test ,conseq ,altern)]
        [(begin ,[Effect -> ef*] ... ,[Value -> val]) (make-begin `(,ef* ... ,val))]
	[(alloc ,[Value -> val]) (if (Triv? val) `(alloc ,val) 
				     (let ([u1 (unique-name 't)])
                 			  (begin
		   			  (set! uvars-list (append uvars-list (list u1)))
                  			 `(begin (set! ,u1 ,val) (alloc ,u1)))))]
	[(mref ,[Value -> x] ,[Value -> y])
           (if (and (Triv? x) (Triv? y))
              `(mref ,x ,y)
           (if (Triv? y)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,x) (mref ,u1 ,y))))
           (if (Triv? x)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,y) (mref ,x ,u1))))
           (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,y) (mref ,u1 ,u2)))))))]
        [(,binop ,[Value -> x] ,[Value -> y])
           (guard (memq binop '(+ - * logand logor sra)))
           (if (and (Triv? x) (Triv? y))
              `(,binop ,x ,y)
           (if (Triv? y)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,x) (,binop ,u1 ,y))))
           (if (Triv? x)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,y) (,binop ,x ,u1))))
           (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,y) (,binop ,u1 ,u2)))))))]
        [(,[Value -> rator] ,[Value -> rand*] ...)
	   (if (memv #f (map Triv? rand*))
           (letrec* ([non-triv (difference rand* (filter Triv? rand*))]
		     [triv (filter Triv? rand*)]
		     [len (length non-triv)] 
                     [ulist (generate-uvar len '())])
                (begin
                  (set! uvars-list (append uvars-list ulist))
		  (letrec* ([u1 (unique-name 't)]
			    [inst (if (not (Triv? rator))
                      		  (begin
		   		    (set! uvars-list (append uvars-list (list u1)))
                  		   `((set! ,u1 ,rator))) '())]
			    [ratr (if (not (Triv? rator)) u1 rator)])
                  (make-begin (append inst (build-ins `(set! ,ulist ,non-triv)) 
			      (list (append (list ratr) (union-list rand* triv ulist))))))))
	   (if (Triv? rator)
	  `(,rator ,rand* ...)
	   (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,rator) (,u1 ,rand* ...))))))]
        [,triv triv])))
  ;; It remove complex operations from the Effect part of the grammer
  ;; It process if, begin, set!, mset! and nop statements and remove complex operations in them
  (define Effect
    (lambda (st)
      (match st
        [(nop) `(nop)]
        [(set! ,uvar ,[Value -> val]) `(set! ,uvar ,val)]
	[(mset! ,[Value -> x] ,[Value -> y] ,[Value -> z])
           (if (and (Triv? x) (Triv? y) (Triv? z))
              `(mset! ,x ,y ,z)
           (if (and (Triv? y) (not (Triv? x)) (Triv? z))
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,x) (mset! ,u1 ,y ,z))))
           (if (and (Triv? x) (not (Triv? y)) (Triv? z))
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,y) (mset! ,x ,u1 ,z))))
           (if (and (Triv? x) (not (Triv? z)) (Triv? y))
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,z) (mset! ,x ,y ,u1))))
           (if (and (not (Triv? x)) (not (Triv? y)) (Triv? z))
               (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,y) (mset! ,u1 ,u2 ,z))))
           (if (and (not (Triv? x)) (not (Triv? z)) (Triv? y))
               (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,z) (mset! ,u1 ,y ,u2))))
           (if (and (not (Triv? y)) (not (Triv? z)) (Triv? x))
               (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,y) (set! ,u2 ,z) (mset! ,x ,u1 ,u2))))
           (if (and (not (Triv? x)) (not (Triv? y)) (not (Triv? z)))
               (let ([u1 (unique-name 't)] [u2 (unique-name 't)] [u3 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2 u3)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,y) (set! ,u3 ,z) (mset! ,u1 ,u2 ,u3))))))))))))]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) (make-begin `(,effect* ... ,effect))]
        [(,[Value -> rator] ,[Value -> rand*] ...)
	   (if (memv #f (map Triv? rand*))
           (letrec* ([non-triv (difference rand* (filter Triv? rand*))]
		     [triv (filter Triv? rand*)]
		     [len (length non-triv)] 
                     [ulist (generate-uvar len '())])
                (begin
                  (set! uvars-list (append uvars-list ulist))
		  (letrec* ([u1 (unique-name 't)]
			    [inst (if (not (Triv? rator))
                      		  (begin
		   		    (set! uvars-list (append uvars-list (list u1)))
                  		   `((set! ,u1 ,rator))) '())]
			    [ratr (if (not (Triv? rator)) u1 rator)])
                  (make-begin (append inst (build-ins `(set! ,ulist ,non-triv)) 
			      (list (append (list ratr) (union-list rand* triv ulist))))))))
	   (if (Triv? rator)
	  `(,rator ,rand* ...)
	   (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,rator) (,u1 ,rand* ...))))))]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It remove complex operations from the Predicate part of the grammer
  ;; It process if, begin, (boolean) and relop statements and remove complex operations in them
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) (make-begin `(,effect* ... ,pred))]
        [(true) `(true)]
        [(false) `(false)]
        [(,relop ,[Value -> x] ,[Value -> y])
           (if (and (Triv? x) (Triv? y))
              `(,relop ,x ,y)
           (if (Triv? y)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,x) (,relop ,u1 ,y))))
           (if (Triv? x)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,y) (,relop ,x ,u1))))
           (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,y) (,relop ,u1 ,u2)))))))]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It remove complex operations from the Tail part of the grammer
  ;; It process if, begin, mref, alloc, (Value Value*), trivial and binop statements and 
  ;; remove complex operations in them
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
         (make-begin `(,ef* ... ,tail))]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2]) `(if ,pred ,tail1 ,tail2)]
	[(alloc ,[Value -> val]) (if (Triv? val) `(alloc ,val) 
				     (let ([u1 (unique-name 't)])
                 			  (begin
		   			  (set! uvars-list (append uvars-list (list u1)))
                  			 `(begin (set! ,u1 ,val) (alloc ,u1)))))]
	[(mref ,[Value -> x] ,[Value -> y])
           (if (and (Triv? x) (Triv? y))
              `(mref ,x ,y)
           (if (Triv? y)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,x) (mref ,u1 ,y))))
           (if (Triv? x)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,y) (mref ,x ,u1))))
           (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,y) (mref ,u1 ,u2)))))))]

        [(,binop ,[Value -> x] ,[Value -> y])
           (guard (memq binop '(+ - * logand logor sra)))
           (if (and (Triv? x) (Triv? y))
              `(,binop ,x ,y)
           (if (Triv? y)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,x) (,binop ,u1 ,y))))
           (if (Triv? x)
               (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,y) (,binop ,x ,u1))))
           (let ([u1 (unique-name 't)] [u2 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1 u2)))
                  `(begin (set! ,u1 ,x) (set! ,u2 ,y) (,binop ,u1 ,u2)))))))]
        [(,[Value -> rator] ,[Value -> rand*] ...)
	   (if (memv #f (map Triv? rand*))
           (letrec* ([non-triv (difference rand* (filter Triv? rand*))]
		     [triv (filter Triv? rand*)]
		     [len (length non-triv)] 
                     [ulist (generate-uvar len '())])
                (begin
                  (set! uvars-list (append uvars-list ulist))
		  (letrec* ([u1 (unique-name 't)]
			    [inst (if (not (Triv? rator))
                      		  (begin
		   		    (set! uvars-list (append uvars-list (list u1)))
                  		   `((set! ,u1 ,rator))) '())]
			    [ratr (if (not (Triv? rator)) u1 rator)])
                  (make-begin (append inst (build-ins `(set! ,ulist ,non-triv)) 
			      (list (append (list ratr) (union-list rand* triv ulist))))))))
	   (if (Triv? rator)
	  `(,rator ,rand* ...)
	   (let ([u1 (unique-name 't)])
                 (begin
		   (set! uvars-list (append uvars-list (list u1)))
                  `(begin (set! ,u1 ,rator) (,u1 ,rand* ...))))))]
        [,triv triv]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It remove complex operations from the Body part of the grammer
  ;; It process locals statements and remove complex operations in them
  (define Body
    (lambda (bexp)
      (match bexp
        [(locals (,uvar* ...) ,tail)
         (begin
           (set! uvars-list uvar*)
           (let ([tail (Tail tail)])
               `(locals (,uvars-list ...) ,tail)))]
        [,b (error who "invalid syntax for Body" b)])))
  ;; It remove complex operations from the program
  ;; It process letrec statements and remove complex operations in them
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda (,uvar* ...) ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda (,uvar* ...) ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))   
)
