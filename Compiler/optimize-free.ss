#|
Program name    : optimize-free.ss
Functions       : optimize-free
Description     : This program will identify closures that are well-known and requires no free variable and eliminate them
		  and also remove them from free variable lists of other closures
Input Language  : Scheme with well-known wrapper and well-know empty closures
Output Language : Scheme with well-know empty closures removed
|#

#!chezscheme
(library (Compiler optimize-free)
  (export
    optimize-free)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass13 of the compiler
(define-who optimize-free
  (define free-vars '())
  (define formal-vars '())
  (define primitives
   '(+ - * car cdr cons make-vector vector-length vector-ref void <= < = >= > boolean?  eq? fixnum?  null? pair? vector? set-car! set-cdr!
     vector-set! procedure?))
  (define-record node (name free*) ([wkmt #t] [link* '()]))
  ;; It create the nodes for all closure forms
  (define create-nodes
    (lambda (uvars fvars uvars*)
      (cond
        ((null? uvars) '())
        (else
	  (let ([node* (make-node (car uvars) (difference (car fvars) uvars*))])
	       (cons node* (create-nodes (cdr uvars) (cdr fvars) uvars*)))))))
  ;; It updates the created nodes with links
  (define create-links
    (lambda (nodes fvars uvars nodes*)
      (cond
        ((null? nodes) #t)
	(else
          (let ([links (intersection uvars (car fvars))])
	       (begin
		 (unless (null? links) (create-links* links (car nodes) nodes*))
		 (create-links (cdr nodes) (cdr fvars) uvars nodes*)))))))
  ;; It is a link helper for create-links
  (define create-links*
    (lambda (links node nodes*)
      (cond
	((null? links) #f)
	(else 
	  (begin
	    (set-node-link (car links) node nodes*)
	    (create-links* (cdr links) node nodes*))))))
  ;; It is link helper for create-links* which sets the actual links
  (define set-node-link
    (lambda (name node nodes)
      (cond
        ((null? nodes) #f)
	((equal? name (node-name (car nodes))) (let ([existg-links (node-link* (car nodes))])
						    (begin 
						      (set-node-link*! (car nodes) (cons node existg-links))
						      (set-node-link name node (cdr nodes)))))
	(else (set-node-link name node (cdr nodes))))))
  ;; It identifies the well-known vars using the nodes
  (define find-wkvar
    (lambda (nodes wk-vars)
      (cond
    	((null? nodes) '())
	(else
	   (let ([cnode (car nodes)])
		(if (and (memq (node-name cnode) wk-vars) (node-wkmt cnode) (null? (node-free* cnode)))
		    (cons cnode (find-wkvar (cdr nodes) wk-vars))
		    (if (node-wkmt cnode)
			(begin
			  (map (lambda (x) (update-nodes x (node-name cnode))) (node-link* cnode))
			  (find-wkvar (cdr nodes) wk-vars))
 			(find-wkvar (cdr nodes) wk-vars))))))))
  ;; It updates the node free-variables and wkmt flag based on the links
  (define update-nodes
    (lambda (link name)
      (let ([cfree (node-free* link)])
	   (begin
	     (set-node-free*! link (union (list name) cfree))
	     (if (node-wkmt link)
		 (begin
		   (set-node-wkmt! link #f)
		   (map (lambda (x) (update-nodes x (node-name link))) (node-link* link)))
		 '())))))
  ;; It creates nodes for closure forms and run the algorithm and returns well-known vars
  (define prune-free
    (lambda (uvar fvar wk-vars wkmt**)
      (let* ([nodes (create-nodes uvar fvar (union uvar wkmt**))]
	    [nodes-linked (create-links nodes fvar uvar nodes)])
	    (values nodes (map (lambda (x) (node-name x)) (find-wkvar nodes wk-vars))))))
  ;; Expose free variables and wrap it around lambda body
  (define Program
    (lambda (x)
      (define Expr
	(lambda (wkmt**)
          (lambda (x)
            (match x
	      [,label (guard (label? label)) label]
              [,uvar (guard (uvar? uvar)) uvar]
              [(quote ,[Immediate ->]) x]
              [(if ,[(Expr wkmt**) -> x1] ,[(Expr wkmt**) -> x2] ,[(Expr wkmt**) -> x3]) 
		`(if ,x1 ,x2 ,x3)]
              [(begin ,[(Expr wkmt**) -> x1*] ... ,[(Expr wkmt**) -> x1]) 
		 (make-begin `(,x1* ... ,x1))]
              [(let ([,uvar* ,[(Expr wkmt**) -> x*]] ...) ,[(Expr wkmt**) -> x]) 
		`(let ([,uvar* ,x*] ...) ,x)]
              [(letrec ([,uvar* ,lmd*] ...) 
		       (closures ((,uvar ,label ,fvar* ...) ...) (well-known ,wk-vars ,x)))
		       (let-values ([(nodes wkmt*) (prune-free uvar fvar* wk-vars wkmt**)])
		                   (let* ([uvar-labl (map cons uvar label)]
					 [x* ((Expr (union wkmt* wkmt**)) x)]
					 [fvar** (map (lambda (nds) (node-free* nds)) nodes)]
					 [Lambda* (map (lambda (x y z) (Lambda x y z (union wkmt* wkmt**))) lmd* uvar fvar**)]
					 [closure* (remq '() (map (lambda (x y z) 
								    (if (memq x wkmt*) '() `(,x ,y ,z ...))) uvar label fvar**))])
                			`(letrec ([,uvar* ,Lambda*] ...) (closures (,closure* ...) ,x*))))]
              [(,prim ,[(Expr wkmt**) -> x*] ...) (guard (memq prim primitives))
		`(,prim ,x* ...)]
              [(,[(Expr wkmt**) -> x] ,[(Expr wkmt**) -> y] ,[(Expr wkmt**) -> z] ...)
		 (if (memq y wkmt**)
		    `(,x ,z ...)
		    `(,x ,y ,z ...))]
              [,x (error who "invalid Expr ~s" x)]))))
      ;; Lambda helper
      (define Lambda
	(lambda (expr uvar fvar** wkmt*)
	  (match expr
	    [(lambda (,cp ,uvar* ...) (bind-free (,cp ,wkvar* ...) ,x*))
	       (let ([ex* ((Expr wkmt*) x*)])
		    (if (memq uvar wkmt*)
		       `(lambda (,uvar* ...) (bind-free (dummy) ,ex*))
		       `(lambda (,cp ,uvar* ...) (bind-free (,cp ,fvar** ...) ,ex*))))])))
      (define (Immediate imm)
        (cond
          [(memq imm '(#t #f ())) (values)]
          [(and (integer? imm) (exact? imm))
           (unless (fixnum-range? imm)
             (error who "integer ~s is out of fixnum range" imm))
           (values)]
          [else (error who "invalid Immediate ~s" imm)]))
      ((Expr '()) x)))
  (lambda (x)
    (begin
      (let ([prg (Program x)]) prg))))
)
