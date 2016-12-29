#|
Program name    : assign-frame.ss
Functions       : assign-frame
Description     : This program assign frame-vars to uvars in the locals. It assign frame-vars based on the 
                  conflict list.
Input Language  : Scheme with a conflict graph consisting of frame-conflict list for all the uvars in locals list.
Output Language : Scheme with frame-conflict list.
|#

#!chezscheme
(library (Compiler assign-frame)
  (export
    assign-frame)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass34 of the compiler
(define-who assign-frame

  (define friends-home '())
  (define conflict-list '())
  (define spill-vars '())
  ;; This function updates the conflict list
  (define update-clist**
    (lambda (cflist var alloc)
      (cond
	[(null? cflist) '()]
	[(eq? (car cflist) var) (cons alloc (update-clist** (cdr cflist) var alloc))]
	[else (cons (car cflist) (update-clist** (cdr cflist) var alloc))])))
  ;; This function updates the conflict list
  (define update-clist*
    (lambda (cflist alloc)
      (map (lambda (ct-entry)
	     (cond
	       [(eq? (car alloc) (car ct-entry)) alloc]
	       [else (cons (car ct-entry)
			   (if (member (cadr alloc) (cdr ct-entry))
			       (remove (car alloc) (cdr ct-entry))
			       (update-clist** (cdr ct-entry) (car alloc) (cadr alloc))))])) cflist)))
  ;; This function updates the conflict list
  (define update-clist			
     (lambda (alloc cflist)
 	(cond 
 	  [(null? alloc) cflist]
 	  [else (update-clist (cdr alloc) (update-clist* cflist (car alloc)))])))
  ;; This function checks if a frame-var is available in any of its friends list in move-bias table
  (define enquire-friend
    (lambda (bt f-list)
      (cond
        ((null? f-list) #f)
	((assq (car f-list) bt) => (lambda(x) (if (memq #t (map frame-var? x)) #t (enquire-friend bt (cdr f-list)))))
	(else (enquire-friend bt (cdr f-list))))))
  ;; This function finds a frame-var from move-bias table entry. If one is not found then it gets a frame-var
  ;; using find-homes
  (define find-friend-fv
    (lambda (cvar ls conflict-entry bt homes*)
      (cond
	[(null? ls) (if (enquire-friend bt (cdr (assq cvar bt)))
			#f
			(car (cdar (find-homes (list cvar) conflict-list (append friends-home homes*)))))]
	[(and (frame-var? (car ls)) (and (not (memq (car ls) conflict-entry))
					 (not (memq (car ls) (find-used conflict-entry (append friends-home homes*)))))) (car ls)]
	[else (find-friend-fv cvar (cdr ls) conflict-entry bt homes*)])))
  ;; This function updates the friends frame-var allocations based on the move-bias table
  (define update-frd-home
    (lambda (uvar reg bt homes*)
      (let ([conflict-entry (cdr (assq uvar conflict-list))])
      (if (or (assq uvar friends-home) 
	      (memq reg conflict-entry)
	      (memq reg (find-used conflict-entry (append friends-home homes*))))
	  friends-home
 	  (begin
	    (set! friends-home (cons (list uvar reg) friends-home))
	    (set! conflict-list (update-clist (list (list uvar reg)) conflict-list))
	    (update-bias-list uvar reg bt homes*)
	    friends-home)))))
  ;; This function updates the move-bias table
  (define update-bias-list
    (lambda (uvar reg bt homes*)
      (map (lambda (entry) 
	     (let ([tail (cdr entry)])
	          (if (memq uvar tail)
	              (begin
			(set-cdr! entry (set-cons reg (cdr (remq uvar entry))))
			(if (memq (car entry) spill-vars) (update-frd-home (car entry) reg bt homes*) '())
	                entry)
	              entry))) bt)))
  ;; This function find homes for move-related spill variables
  (define find-mb-homes
    (lambda (uvar bias-tbl homes*)
      (cond
	[(null? bias-tbl) friends-home]
	[(null? uvar) friends-home]
	[else (let* ([cvar (car uvar)]
		     [bias-tbl-entry (assq cvar bias-tbl)]
		     [frd-vars (if bias-tbl-entry (cdr bias-tbl-entry) '())]
		     [cf-entry (cdr (assq cvar conflict-list))])
      		    (if (null? frd-vars) 
	  		(find-mb-homes (cdr uvar) bias-tbl homes*)
	  		(let ([friend-fv (find-friend-fv cvar frd-vars cf-entry bias-tbl homes*)])
	  		     (cond
	    		       [(eq? friend-fv #f) (find-mb-homes (cdr uvar) bias-tbl homes*)]
	    		       [else 
				  (begin 
				    (set! conflict-list (update-clist (list (list cvar friend-fv)) conflict-list))
		       		    (let* ([updated-bias (update-bias-list cvar friend-fv bias-tbl homes*)])
			    		  (begin
		 	      		    (unless (assq cvar friends-home) 
		              		       (set! friends-home (cons (list cvar friend-fv) friends-home)))
			      		    (find-mb-homes (cdr uvar) updated-bias homes*))))]))))])))
  ;; This function remove conflicting move-related entries from move-bias table
  (define rem-bt-conflicts
    (lambda (bt ct)
      (cond
        ((null? bt) '())
        ((equal? 1 (length (car bt))) (rem-bt-conflicts (cdr bt) ct))
        (else (let* ([cvar (car bt)]
		     [cflt (assq (car cvar) ct)]
	  	     [cf-entry (if cflt (cdr cflt) '())]
		     [diff (difference (cdr cvar) cf-entry)])
		    (cons (cons (car cvar) diff) (rem-bt-conflicts (cdr bt) ct)))))))
  ;; This function removes variables without move-relation from the move-bias table
  (define filter-bias
    (lambda (ls)
      (cond
        ((null? ls) '())
	((equal? 1 (length (car ls))) (filter-bias (cdr ls)))
	(else (cons (car ls) (filter-bias (cdr ls)))))))
  ;; This function finds the conflicting frame-vars
  (define find-used
    (lambda (conflict* home*)
      (cond
        [(null? conflict*) '()]
        [(frame-var? (car conflict*))
         (set-cons (car conflict*) (find-used (cdr conflict*) home*))]
        [(assq (car conflict*) home*) =>
         (lambda (x) (set-cons (cadr x) (find-used (cdr conflict*) home*)))]
        [else (find-used (cdr conflict*) home*)])))
  ;; This function finds a suitable frame-var for allocation
  (define find-frame-var
    (lambda (used*)
      (let f ([index 0])
        (let ([fv (index->frame-var index)])
          (if (memq fv used*) (f (+ index 1)) fv)))))
  ;; This function find homes for spill variables other than move-related spills
  (define find-homes
    (lambda (var* ct home*)
      (if (null? var*)
          home*
          (let ([var (car var*)] [var* (cdr var*)])
            (let ([conflict* (cdr (assq var ct))])
              (let ([home (find-frame-var (find-used conflict* home*))])
                (find-homes var* ct `((,var ,home) . ,home*))))))))
  ;; It process the body part of the grammer
  (define Body
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (spills (,spill* ...)
               (locate (,home* ...)
                 (frame-conflict ,ct ,tail)))))

           (set! friends-home '())
           (set! conflict-list ct)
           (set! spill-vars spill*)
           (let* ([uvar* (union ulocal* local* spill*)] 
	          [bias-list (move-bias tail frame-var? uvar*)]
	          [bias-lst-wcf (filter-bias (rem-bt-conflicts bias-list conflict-list))]
 	          [biased-home* (find-mb-homes spill* bias-lst-wcf home*)]
	          [homes (if (null? biased-home*) '() (map car biased-home*))]
	          [home* (find-homes (difference spill* homes) conflict-list (append home* biased-home*))])
                `(locals (,local* ...)
                   (ulocals (,ulocal* ...)
                     (locate (,home* ...)
                       (frame-conflict ,ct ,tail)))))]
        [(locate (,home* ...) ,body) `(locate (,home* ...) ,body)]
        [,body (error who "invalid Body ~s" body)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))

;; Setting this true enables move-bias refinements
(define enable-move-bias #t)

;; This function exposes move-relations in the input program
(define-who move-bias
  (define bias-list '())
  (define fn '())

  ;; It process the statements in Effect from backwards
  (define Effect*
    (lambda (x)
      (match x
        [() '()]
        [(,ef* ... ,ef) (begin (Effect ef) (Effect* ef*))]
        [,x (error who "invalid Effect* list ~s" x)])))
  ;; It uncover conflicts for uvars in Effect* part of grammer
  (define Effect
    (lambda (x)
      (match x
        [(nop) '()]
        [(if ,test ,[Effect -> x] ,[Effect -> y]) 
         (Pred test)]
        [(begin ,ef* ... ,[Effect -> x]) (Effect* ef*)]
        [(set! ,x ,y) (guard (and (uvar? x) (uvar? y)))
	   (begin
	     (set-cdr! (assq x bias-list) (set-cons y (cdr (assq x bias-list))))
	     (set-cdr! (assq y bias-list) (set-cons x (cdr (assq y bias-list))))
	     '())]
	[(set! ,x ,y) (guard (and (uvar? x) (fn y)))
	   (begin
	     (set-cdr! (assq x bias-list) (set-cons y (cdr (assq x bias-list))))
	     '())]
	[(set! ,x ,y) (guard (and (fn x) (uvar? y)))
	   (begin
	     (set-cdr! (assq y bias-list) (set-cons x (cdr (assq y bias-list))))
	     '())]
        [,x '()])))
  ;; It uncover conflicts for uvars in Predicate part of grammer
  (define Pred
    (lambda (x)
      (match x
        [(true) '()]
        [(false) '()]
        [(if ,test ,[Pred -> x] ,[Pred -> y])
         (Pred test)]
        [(begin ,ef* ... ,[Pred -> x]) (Effect* ef*)]
        [,x '()])))
  ;; It uncover conflicts for uvars in Tail part of grammer
  (define Tail
    (lambda (x)
      (match x
        [(begin ,ef* ... ,[Tail -> x]) (Effect* ef*)]
        [(if ,test ,[Tail -> x] ,[Tail -> y]) 
         (Pred test)]
        [(,x ,y ...) '()]
        [,x '()])))

  (lambda (tail func uvar*)
    (cond
      [(eq? enable-move-bias '#f) '()]
      [else (begin 
	      (set! bias-list (map (lambda (x) (cons x '())) uvar*))
	      (set! fn func)
	      (let* ([new-bias-list (Tail tail)])
		    bias-list))])))
)
