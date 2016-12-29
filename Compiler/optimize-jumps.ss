#|
Program name    : optimize-jumps.ss
Functions       : optimize-jumps
Description     : This program removes the unnecessary superflous jumps introduced by expose-basic-blocks
Input Language  : Code with basic blocks
Output Language : Code with unncessary jump statements removed
|#

#!chezscheme
(library (Compiler optimize-jumps)
  (export
    optimize-jumps)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass41 of the compiler
(define-who optimize-jumps
  (define asc-list '())
  (define bindings '())
  ;; It creates the association list for jump statements
  (define create-assoc-list
    (lambda (labl val)
      (cond
        ((null? labl) '())
        ((label? (caar val)) (cons (cons (car labl) (list (caar val))) (create-assoc-list (cdr labl) (cdr val))))
        (else (create-assoc-list (cdr labl) (cdr val))))))
  ;; It updates the assoc list once a jump statement is removed
  (define update-assoc-list
    (lambda (labl val asc-lst)
      (cond
	((null? asc-lst) '())
	((equal? labl (cadar asc-lst)) (cons (cons (caar asc-lst) (list val)) (update-assoc-list labl val (cdr asc-lst))))
	(else (cons (car asc-lst) (update-assoc-list labl val (cdr asc-lst)))))))
  ;; It updates the letrec bindings once a jump statement is removed
  (define replace
    (lambda (binding-list labl val)
      (if (equal? (caadr binding-list) labl) (cons (car binding-list) (list (list val))) binding-list)))
  ;; It removes unnecessary jump statements from letrec bindings
  (define remove-bindings
    (lambda (labl)
      (set! bindings (remove (assq labl bindings) bindings))))
  ;; It updates the letrec bindings once a jump statement is removed
  (define update-bindings
    (lambda (labl val)
      (set! bindings (map (lambda (lst) (replace lst labl val)) bindings))))    
  ;; It update letrec bindings and assoc list accordingly
  (define refine-bindings
    (lambda (labl val)
      (cond
        ((null? labl) '())
        ((and (label? (caar val)) (not (equal? (car labl) (caar val)))) 
	   (begin
	     (remove-bindings (car labl))
	     (update-bindings (car labl) (caar val))
	     (set! asc-list (update-assoc-list (car labl) (caar val) asc-list))
             (refine-bindings (cdr labl) (cdr val))))
        (else (refine-bindings (cdr labl) (cdr val))))))
  ;; It build the letrec bindings
  (define build-bindings
    (lambda (binds)
      (cond
        ((null? binds) '())
	(else
 	  (let* ([labl (caar binds)]
		 [val (cadar binds)]
		 [new-binds `[,labl (lambda() ,val)]])
		(cons new-binds (build-bindings (cdr binds))))))))
  ;; It update jumps in the tail part of the grammer
  (define update-tail*
    (lambda (x)
      (match x
	[([,labl (lambda() ,[Tail -> tail*])] ...) `([,labl (lambda() ,tail*)] ...)]
	[,tl (error who "invalid syntax for Tail " tl)])))
  ;; It updates jumps based on assoc list 
  (define Triv
    (lambda (x)
      (if (label? x) (if (assq x asc-list) (cadr (assq x asc-list)) x) x)))
  ;; Process the Effect part of the grammer
  (define Effect
    (lambda (st)
      (match st
	[(set! ,x (,binop ,[Triv -> triv1] ,[Triv -> triv2])) `(set! ,x (,binop ,triv1 ,triv2))]
        [(set! ,x ,[Triv -> triv]) `(set! ,x ,triv)]
        [,st (error who "unexpected effect ~s" st)])))
  ;; Process the tail part of the grammer
  (define Tail
   (lambda (tl)
       (match tl
         [(begin ,[Effect -> x*] ... ,[Tail -> tail]) (make-begin `(,x* ... ,tail))]
         [(if (,relop ,[Triv -> x] ,[Triv -> y]) (,[Triv -> clb]) (,[Triv -> alb])) `(if (,relop ,x ,y) (,clb) (,alb))]
         [(,[Triv -> x]) `(,x)]
         [,tl (error who "invalid syntax for Tail" tl)])))
  ;; Remove unnecessary jumps from the code
  (lambda (code)
    (match code
      [(letrec ([,labl (lambda() ,tail*)] ...) ,tail)
       (begin
         (set! asc-list (create-assoc-list labl tail*))
	 (set! bindings (map cons labl (map list tail*)))
	 (refine-bindings labl tail*)
         (let* ([bindings* (build-bindings bindings)]
		[bindings** (update-tail* bindings*)]
		[tail1 (Tail tail)])
	      `(letrec (,bindings** ...) ,tail1)))]
      [() (void)]
      [,x (error who "Invalid Syntax: ~s\n" exp)])))

)
