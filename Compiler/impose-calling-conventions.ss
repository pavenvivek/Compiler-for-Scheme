#|
Program name    : impose-calling-conventions.ss
Functions       : impose-calling-conventions
Description     : This program impose calling conventions in the code. It assigns reg/fvar for uvars in the
		  lambda and procedure call part of the program and build instructions for the same.
Input Language  : Scheme with set! statements flattened
Output Language : Scheme with calling conventions imposed
|#

#!chezscheme
(library (Compiler impose-calling-conventions)
  (export
    impose-calling-conventions)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass25 of the compiler
(define-who impose-calling-conventions
  (define uvars-list '())
  (define ref-var '())
  (define frame* '())
  ;; It generate fvars for the unique variables
  (define get-fvars
    (lambda (n c)
      (cond
        ((zero? c) '())
        (else (cons (index->frame-var n) (get-fvars (add1 n) (sub1 c)))))))
  (define get-new-fvars
    (lambda (c)
      (cond
        ((zero? c) '())
        (else (cons (unique-name 'nfv) (get-new-fvars (sub1 c)))))))
  ;; It generate reg/fvars for the unique variable list
  (define get-vars
    (lambda (var-list leng position)
      (cond
	((equal? leng 0) '())
        ((equal? leng 1) (begin (when (equal? position 'Effect) (set! frame* (cons '() frame*))) (list (car parameter-registers))))
	((equal? leng 2) (begin (when (equal? position 'Effect) (set! frame* (cons '() frame*))) parameter-registers))
        (else (if (memv position '(Tail Body)) 
		  (append parameter-registers (get-fvars 0 (- leng 2)))
		  (append parameter-registers 
			  (let ([new-fv (get-new-fvars (- leng 2))]) 
			       (begin (set! frame* (cons new-fv frame*)) new-fv))))))))
  ;; It inserts set! into the list of (uvar reg/fvar) or (reg/fvar uvar)
  (define insert-set!
    (lambda (var-list)
      (cond
        ((null? var-list) '())
        (else (cons (cons 'set! (car var-list)) (insert-set! (cdr var-list)))))))
  (define merge-list
    (lambda (lst)
      (cond 
        ((null? lst) '())
        (else (append (car lst) (merge-list (cdr lst)))))))
  ;; It build the instructions for uvars in the lambda and uvars in the procedure call
  (define build-ins
    (lambda (var-list uvar position)
      (letrec* ([reg/fvar (map list (get-vars var-list (length var-list) position))]
	        [var-assignments 
		 (if (memv position '(Tail Effect))
		     (map append reg/fvar (map list var-list))
		     (map cons var-list reg/fvar))]
	    	[instructions
	         (if (memv position '(Tail Effect))
		     (append (reverse var-assignments) (list (list return-address-register uvar)))
		     (cons (list uvar return-address-register) var-assignments))])
	       (begin
	  	 (set! uvars-list instructions)
	  	 (if (null? var-list)
	      	     (cons 'begin (insert-set! instructions))
              	     (make-begin (insert-set! instructions)))))))
  ;; It returns the assigned reg/fvars for the uvars in the procedure call
  (define get-assigned-reg
    (lambda (triv uvars-lst)
      (cond
        ((null? triv) '())
        ((assv (car triv) uvars-lst) (cons (cadr (assv (car triv) uvars-lst)) (get-assigned-reg (cdr triv) uvars-lst)))
	(else (get-assigned-reg (cdr triv) uvars-lst)))))
  ;; It impose calling conventions in the Effect* part of grammer
  ;; It process set!, if, begin statements and impose calling conventions in Effect*
  (define Effect
    (lambda (st)
      (match st
        [(nop) `(nop)]
	[(set! ,uvar (,binop ,Triv ,Triv)) (guard (memq binop '(+ - * logand logor sra))) 
	  `(set! ,uvar (,binop ,Triv ,Triv))]
	[(set! ,var (,triv ,triv* ...)) (guard (or (label? triv) (uvar? triv)))
   	   (make-begin
     	    `(,(Effect `(,triv ,triv* ...))
       	     (set! ,var ,return-value-register)))]
        [(set! ,uvar ,triv) `(set! ,uvar ,triv)]
	[(mset! ,val1 ,val2 ,val3) `(mset! ,val1 ,val2 ,val3)]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) (make-begin `(,effect* ... ,effect))]
	[(,triv ,triv* ...)
	   (letrec* ([rp-label (unique-label 'rp)]
		     [inst (build-ins triv* rp-label 'Effect)]) 
	           `(return-point ,rp-label
		     ,(make-begin `(,(append inst
                    		  (list (append (list triv return-address-register frame-pointer-register allocation-pointer-register) 
		    		  (get-assigned-reg triv* (map reverse uvars-list)))))))))]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It impose calling conventions in the Predicate part of grammer 
  ;; It process if, begin, relop, bool statements and impose calling conventions in Predicate
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) (make-begin `(,effect* ... ,pred))]
        [(true) `(true)]
        [(false) `(false)]
        [(,relop ,x ,y)
	  `(,relop ,x ,y)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It impose calling conventions in the Tail part of grammer
  ;; It process (triv), if, begin statements and impose calling conventions in Tail
  (define Tail
    (lambda (uvar)
      (lambda (tail)
        (match tail
          [(begin ,[Effect -> ef*] ... ,[(Tail uvar) -> tail]) (make-begin `(,ef* ... ,tail))]
          [(if ,[Pred -> pred] ,[(Tail uvar) -> tail1] ,[(Tail uvar) -> tail2]) `(if ,pred ,tail1 ,tail2)]
	  [(alloc ,xpr) 
	    `(begin (set! ,return-value-register (alloc ,xpr)) 
		    (,uvar ,frame-pointer-register ,allocation-pointer-register ,return-value-register))]
	  [(mref ,x ,y)
            `(begin (set! ,return-value-register (mref ,x ,y)) 
		    (,uvar ,frame-pointer-register ,allocation-pointer-register ,return-value-register))]
          [(,binop ,x ,y)
             (guard (memq binop '(+ - * logand logor sra)))
            `(begin (set! ,return-value-register (,binop ,x ,y)) 
		    (,uvar ,frame-pointer-register ,allocation-pointer-register ,return-value-register))]
          [(,Triv ,Triv* ...)
	     (letrec* ([inst (build-ins Triv* uvar 'Tail)]) 
	              (append inst
                      (list (append (list Triv return-address-register frame-pointer-register allocation-pointer-register) 
			    (get-assigned-reg Triv* (map reverse uvars-list))))))]
          [,triv (make-begin `((set! ,return-value-register ,triv) 
			       (,uvar ,frame-pointer-register ,allocation-pointer-register ,return-value-register)))]
          [,tail (errorf who "invalid syntax for Tail ~s" tail)]))))
  ;; It impose calling conventions in the Body part of grammer
  ;; It process locals statements and set the uvars-list
  (define Body
    (lambda (uvarlist)
      (lambda (bexp)
        (match bexp
          [(locals (,uvar* ...) ,tail)
           (begin 
	     (set! uvars-list uvarlist)
	     (set! frame* '())
             (letrec* ([uvar (unique-name 'rp)]
		       [uvars2* (append (list uvar) uvars-list uvar*)]
                       [inst (build-ins uvars-list uvar 'Body)]
                       [tail1 ((Tail uvar) tail)])
                     `(locals ,(append uvars2* (merge-list frame*)) (new-frames (,frame* ...) ,(make-begin `(,inst ,tail1))))))]
          [,b (error who "invalid syntax for Body" b)]))))
  ;; It impose calling conventions in the Body part of grammer
  ;; It process (label (lambda ...)) statements and set the uvars-list
  (define Lambda
    (lambda (code)
      (match code
        [(,label* (lambda (,uvar* ...) ,body*))
  	   (begin
             (set! uvars-list '())
	     (set! ref-var '())
             (set! body* ((Body uvar*) body*))
            `[,label* (lambda () ,body*)])]
	[,program (errorf who "invalid syntax for Code: ~s" program)])))
  ;; It impose calling conventions in the program
  ;; It process letrec statements
  (lambda (program)
    (match program
      [(letrec (,[Lambda -> x*] ...) ,body)
	 (begin
           (set! uvars-list '())
	   (set! ref-var '())
 	   (set! body ((Body '()) body))
          `(letrec (,x* ...) ,body))]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))
)
