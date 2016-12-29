#|
Program name    : assign-new-frame.ss
Functions       : assign-new-frame
Description     : This program determines the size of the body's frame based on locations of the variables
		  in call-live list. Then it assigns frame-var for variables in new-frames list. It also 
		  restructure the code by placing the callee's frame above the body's frame.
Input Language  : Scheme with locate list
Output Language : Scheme with frames assigned for new-frames
|#

#!chezscheme
(library (Compiler assign-new-frame)
  (export
    assign-new-frame)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass29 of the compiler
(define-who assign-new-frame
  (define cf-list '())
  (define binops '(+ - * logand logor sra))
  (define relops '(< > <= >= =))
  ;; It assign frame-vars for variables in new-frames list
  (define assign-frames
    (lambda (n)
      (lambda (new-frames)
        (cond
          ((null? new-frames) '())
	  (else (cons (list (car new-frames) (index->frame-var n)) ((assign-frames (add1 n)) (cdr new-frames))))))))
  ;; It returns the index for frame-vars
  (define get-index
    (lambda (locate-lst)
      (lambda (var)
        (if (frame-var? var) (frame-var->index var) (frame-var->index (cadr (assv var locate-lst)))))))
  ;; It returns the frame-size
  (define get-frame-size
    (lambda (var-list locate-list)
      (+ (apply max (map (get-index locate-list) var-list)) 1)))
  ;; It removes the new-frames from the locals list
  (define get-local
    (lambda (uvar frame)
      (cond
        ((null? frame) uvar)
	(else (get-local (difference uvar (car frame)) (cdr frame))))))
  ;; It merges sub-lists inside a list
  (define merge-list
    (lambda (lst)
      (cond 
        ((null? lst) '())
        (else (append (car lst) (merge-list (cdr lst)))))))
  ;; It process Effect part of the grammer and assign frames for new-frames
  (define Effect
    (lambda (frame-size)
      (lambda (ef)
        (match ef
          [(nop) `(nop)]
          [(if ,[(Pred frame-size) -> pred] ,[(Effect frame-size) -> ef1] ,[(Effect frame-size) -> ef2]) `(if ,pred ,ef1 ,ef2)]
          [(begin ,[(Effect frame-size) -> ef*] ... ,[(Effect frame-size) -> ef]) `(begin ,ef* ... ,ef)]
          [(set! ,var ,expr) `(set! ,var ,expr)]
	  [(mset! ,val1 ,val2 ,val3) `(mset! ,val1 ,val2 ,val3)]
	  [(return-point ,rp-label ,[(Tail frame-size) -> tail]) 
	    `(begin (set! ,frame-pointer-register (+ ,frame-pointer-register ,(ash frame-size word-shift)))
    	       	    (return-point ,rp-label ,tail)
    	       	    (set! ,frame-pointer-register (- ,frame-pointer-register ,(ash frame-size word-shift))))]
          [,ef (error who "invalid Effect ~s" ef)]))))
  ;; It process Predicate part of the grammer and assign frames for new-frames
  (define Pred
    (lambda (frame-size)
      (lambda (pr)
        (match pr
          [(true) `(true)]
          [(false) `(false)]
          [(if ,[(Pred frame-size) -> pred1] ,[(Pred frame-size) -> pred2] ,[(Pred frame-size) -> pred3]) `(if ,pred1 ,pred2 ,pred3)]
          [(begin ,[(Effect frame-size) -> ef*] ... ,[(Pred frame-size) -> pred]) `(begin ,ef* ... ,pred)]
          [(,relop ,triv1 ,triv2) (guard (memq relop relops)) `(,relop ,triv1 ,triv2)]
          [,pr (error who "invalid Pred ~s" pr)]))))
  ;; It process Tail part of the grammer and assign frames for new-frames
  (define Tail
    (lambda (frame-size)
      (lambda (tail)
        (match tail
          [(if ,[(Pred frame-size) -> pred] ,[(Tail frame-size) -> tail1] ,[(Tail frame-size) -> tail2]) `(if ,pred ,tail1 ,tail2)]
          [(begin ,[(Effect frame-size) -> ef*] ... ,[(Tail frame-size) -> tail]) `(begin ,ef* ... ,tail)]
          [(,triv ,loc* ...) `(,triv ,loc* ...)]
	  [,tl (error who "invalid Tail ~s" tl)]))))
  ;; It process Body part of the grammer and assign frames for new-frames
  (define Body
    (lambda (bexp)
      (match bexp
        [(locals (,uvar* ...) (new-frames (,Frame* ...) (locate ,conflict-graph 
                 (frame-conflict (,cflist* ...) (call-live (,uvar3* ...) ,tail)))))
	 (letrec* ([frame-size (if (null? uvar3*) 0 (get-frame-size uvar3* conflict-graph))]
	           [cf (merge-list (map (assign-frames frame-size) Frame*))]
		   [tail1 ((Tail frame-size) tail)])
	         `(locals ,(get-local uvar* Frame*) (ulocals () (locate ,(append conflict-graph cf) 
                  (frame-conflict (,cflist* ...) ,tail1)))))]
        [,b (error who "invalid syntax for Body" b)])))
  ;; It process letrec statements and assign frames for new-frames
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))  
)
