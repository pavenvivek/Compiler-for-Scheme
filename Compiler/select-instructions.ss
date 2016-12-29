#|
Program name    : select-instructions.ss
Functions       : select-instructions
Description     : This program is used to select appropriate instructions for codes segments which do not
                  obey the machine constraints. It introduces unspillables to handle them.
Input Language  : Scheme with frames assigned for new-frames
Output Language : Scheme with code modified as per machine constraints.
|#

#!chezscheme
(library (Compiler select-instructions)
  (export
    select-instructions)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass30 of the compiler
(define-who select-instructions
  (define ulocals '())
  ;; It checks whether given variable is uvar or register
  (define uvar/reg?
    (lambda (triv)
      (if (or (uvar? triv) (register? triv)) #t #f)))
  ;; It checks whether given variable is int64 or label
  (define int64/label?
    (lambda (triv)
      (if (or (label? triv) (and (integer? triv) (exact? triv) (not (int32? triv)))) #t #f)))
  ;; It checks whether given binary operator is commutative
  (define commutative?
    (lambda (op)
      (if (memv op '(+ * logand logor)) #t #f)))
  ;; It returns opposite match for given relational operator
  (define getop
    (lambda (op)
      (case op
        [(>) '<]
        [(<) '>]
        [(>=) '<=]
        [(<=) '>=]
	[(=) '=]
        [else (error who "unexpected binop ~s" op)])))
  (define merge-list
    (lambda (lst)
      (cond 
        ((null? lst) '())
	((null? (car lst)) (merge-list (cdr lst)))
        ((pair? (car lst)) (cons (caar lst) (merge-list (cdr lst))))
        (else (cons (car lst) (merge-list (cdr lst)))))))
  ;; It selects appropriate statements for binop code segments that dont obey machine constraints
  (define select-binop-instruction
     (lambda (binop var triv)
       (case binop
         [(+ - logand logor) 
            (if (or (int64/label? triv) (and (frame-var? var) (frame-var? triv)))
	      (let ([ulocal (unique-name 'u)])
                (begin 
                  (set! ulocals (cons ulocal ulocals)) 
                 `(begin (set! ,ulocal ,triv) (set! ,var (,binop ,var ,ulocal)))))
               `(set! ,var (,binop ,var ,triv)))]
         [(*) 
            (if (frame-var? var)
              (let ([ulocal (unique-name 'u)])
                (begin 
                  (set! ulocals (cons ulocal ulocals))
                 `(begin 
                    (set! ,ulocal ,var) 
                   ,(select-binop-instruction binop ulocal triv)
                    (set! ,var ,ulocal))))
                (if (or (or (label? triv) (and (integer? triv) (not (int32? triv)))))
		  (let ([ulocal (unique-name 'u)])
                    (begin
                      (set! ulocals (cons ulocal ulocals))
                     `(begin (set! ,ulocal ,triv) (set! ,var (,binop ,var ,ulocal)))))
                 `(set! ,var (,binop ,var ,triv))))]
         [(sra)
            `(set! ,var (,binop ,var ,triv))])))
  ;; It selects appropriate statements for relop code segments that dont obey machine constraints
  (define select-relop-instructions
    (lambda (relop t1 t2)
      (let* ([u1 (unique-name 'u)]
	     [u2 (unique-name 'u)]
             [X4 `(,(getop relop) ,t2 ,t1)]
             [X5 `(begin (set! ,u1 ,t1) (,relop ,u1 ,t2))]
             [X6 `(begin (set! ,u1 ,t2) (,(getop relop) ,u1 ,t1))]
	     [X7 `(begin (set! ,u1 ,t1) (set! ,u2 ,t2) (,relop ,u1 ,u2))])
      (if (or (and (frame-var? t1) (frame-var? t2)) 
              (and (int32? t1) (int32? t2))
              (and (int64/label? t1) (or (uvar/reg? t2) (frame-var? t2) (int32? t2))))
          (begin (set! ulocals (cons u1 ulocals)) X5)
      (if (and (int32? t1) (or (uvar/reg? t2) (frame-var? t2)))
          (begin (set! ulocals (cons u1 ulocals)) X4)
      (if (and (int64/label? t2) (or (uvar/reg? t1) (frame-var? t1) (int32? t1)))
          (begin (set! ulocals (cons u1 ulocals)) X6)
      (if (and (int64/label? t1) (int64/label? t2))
          (begin (set! ulocals (cons u1 (cons u2 ulocals))) X7)
         `(,relop ,t1 ,t2))))))))

  ;; It select instructions for the Effect* part of grammer
  ;; It process set!, if, begin statements and identify appropriate instructions as per
  ;; the machine constraints
  (define Effect
    (lambda (st)
      (match st
	[(set! ,var (mref ,t1 ,t2))
	   (letrec* ([u1 (if (or (uvar? var) (register? var)) var (unique-name 'u))]
		     [u2 (if (or (uvar? t1) (register? t1)) t1 (unique-name 'u))]
		     [u3 (if (or (uvar? t2) (int32? t2)) t2 (unique-name 'u))]
		     [inst1 (if (or (uvar? var) (register? var) (frame-var? var)) '() `((set! ,u1 ,var)))] 
		     [inst2 (if (or (uvar? t1) (register? t1)) '() `((set! ,u2 ,t1)))]
		     [inst3 (if (or (uvar? t2) (int32? t2)) '() `((set! ,u3 ,t2)))])
		    (begin 
		      (set! ulocals (append 
			  	      (merge-list 
				      (list 
				        (if (equal? u1 var) '() u1)
				        (if (equal? u2 t1) '() u2)
				        (if (equal? u3 t2) '() u3))) 
				      ulocals))
		      (if (frame-var? var)
			 (cons 'begin (merge-list (list inst2 inst3 `((set! ,u1 (mref ,u2 ,u3))) `((set! ,var ,u1)))))
		         (cons 'begin (merge-list (list inst1 inst2 inst3 `((set! ,u1 (mref ,u2 ,u3)))))))))]
        [(set! ,var (,binop ,t1 ,t2))
         (if (equal? var t1) (select-binop-instruction binop var t2)
           (if (and (equal? var t2) (commutative? binop))
              (select-binop-instruction binop var t1)
              (let ([ulocal (unique-name 'u)])
                (begin
                  (set! ulocals (cons ulocal ulocals))
                 `(begin 
                  (set! ,ulocal ,t1) 
                 ,(select-binop-instruction binop ulocal t2)
                  (set! ,var ,ulocal))))))]
        [(set! ,var ,t) 
           (if (equal? var t) `(nop) 
           (if (and (frame-var? var) (or (int64/label? t) (frame-var? t))) 
           (let ([u (unique-name 'u)]) (begin (set! ulocals (cons u ulocals)) `(begin (set! ,u ,t) (set! ,var ,u))))
           `(set! ,var ,t)))]
	[(mset! ,var ,t1 ,t2) 
           (letrec* ([u1 (if (uvar? var) var (unique-name 'u))]
		 [u2 (if (or (uvar? t1) (int32? t1)) t1 (unique-name 'u))]
		 [u3 (if (or (uvar? t2) (int32? t2)) t2 (unique-name 'u))]
		 [inst1 (if (uvar? var) '() `((set! ,u1 ,var)))] 
		 [inst2 (if (or (uvar? t1) (int32? t1)) '() `((set! ,u2 ,t1)))]
		 [inst3 (if (or (uvar? t2) (int32? t2)) '() `((set! ,u3 ,t2)))])
		(begin 
		  (set! ulocals (append 
				  (merge-list 
				    (list 
				      (if (equal? u1 var) '() u1)
				      (if (equal? u2 t1) '() u2)
				      (if (equal? u3 t2) '() u3))) 
				    ulocals)) 
		  (cons 'begin (merge-list (list inst1 inst2 inst3 `((mset! ,u1 ,u2 ,u3)))))))]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) `(begin ,effect* ... ,effect)]
	[(return-point ,rp-label ,[Tail -> tail]) `(return-point ,rp-label ,tail)]
        [(,x) (guard (equal? x 'nop)) `(,x)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It select instructions for the Predicate part of grammer
  ;; It process if, begin, relop, bool statements and identify appropriate instructions as per
  ;; the machine constraints
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) (make-begin `(,effect* ... ,pred))]
        [(,bool) `(,bool)]
        [(,relop ,triv1 ,triv2) (select-relop-instructions relop triv1 triv2)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It select instructions for the Tail part of grammer
  ;; It process (triv loc), if, begin statements and identify appropriate instructions as per
  ;; the machine constraints
  (define Tail
    (lambda (tail)
      (match tail
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
         (make-begin `(,ef* ... ,tail))]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2]) `(if ,pred ,tail1 ,tail2)]
        [(,triv ,loc* ...) `(,triv ,loc* ...)]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It select instructions for the body part of grammer
  ;; It process locals statements and identify appropriate instructions as per
  ;; the machine constraints. For locate statements, it returns the same without any modifications
  (define Body
    (lambda (bexp)
      (match bexp
        [(locals (,uvar* ...) (ulocals (,uvar2* ...) (locate (,x* ...) (frame-conflict (,y* ...) ,tail))))
         (begin 
           (set! ulocals '())
           (let ([tail (Tail tail)])
          `(locals (,uvar* ...) (ulocals ,(append ulocals uvar2*) (locate (,x* ...) (frame-conflict (,y* ...) ,tail))))))]
	[(locate (,x* ...) ,tail) `(locate (,x* ...) ,tail)]
        [,b (error who "invalid syntax for Body" b)])))
  ;; It select instructions for the program
  ;; It process letrec statements and identify appropriate instructions as per
  ;; the machine constraints
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))  
)
