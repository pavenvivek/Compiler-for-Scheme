#|
Program name    : assign-registers.ss
Functions       : assign-registers
Description     : This program assign registers to uvars in the locals. It assign registers recursivley based 
                  on a particular alogorithm as follows:
                  1] It selects a uvar with least no of conflicts. 
                  2] If no such least conflicting uvars are there, it select one at random and proceed.
                  3] It assign register to it based on the conflict list. 
Input Language  : Scheme with a conflict graph consisting of conflict list for all the uvars in locals list.
Output Language : Scheme with locals list replaced by locate statement and registers assigned for uvars.
|#

(library (Compiler assign-registers)
  (export assign-registers)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework helpers)
    (Framework match))

;; Defines pass32 of the compiler
(define-who assign-registers
  (define friends-home '())
  (define conflict-list '())
  ;; Minimal set of registers defined
  (define registers '(rcx rdx rbx r10 r11 r12))
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
  ;; This function remove conflicting move-related entries from move-bias table
  (define rem-bt-conflicts
    (lambda (bt ct)
      (cond
        ((null? bt) '())
        ((equal? 1 (length (car bt))) (rem-bt-conflicts (cdr bt) ct))
        (else (let* ([cvar (car bt)]
	  	     [cf-entry (cdr (assq (car cvar) ct))]
		     [diff (difference (cdr cvar) cf-entry)])
		    (cons (cons (car cvar) diff) (rem-bt-conflicts (cdr bt) ct)))))))
  ;; This function removes variables without move-relation from the move-bias table
  (define filter-bias
    (lambda (ls)
      (cond
        ((null? ls) '())
	((equal? 1 (length (car ls))) (filter-bias (cdr ls)))
	(else (cons (car ls) (filter-bias (cdr ls)))))))
  ;; This function finds a register from move-bias table entry
  (define find-friend-reg
    (lambda (ls conflict-entry)
      (cond
	[(null? ls) #f]
	[(and (register? (car ls)) (not (memq (car ls) conflict-entry))) (car ls)]
	[else (find-friend-reg (cdr ls) conflict-entry)])))
  ;; This function updates the friends register allocations based on the move-bias table
  (define update-frd-home
    (lambda (uvar reg bt cvar)
      (let ([conflict-entry (cdr (assq uvar conflict-list))])
      (if (or (assq uvar friends-home) (memq reg conflict-entry) (memq cvar conflict-entry))
	  friends-home
 	  (begin
	    (set! friends-home (cons (list uvar reg) friends-home))
	    (set! conflict-list (update-clist (list (list uvar reg)) conflict-list))
	    (update-bias-list uvar reg bt)
	    friends-home)))))
  ;; This function updates the move-bias table
  (define update-bias-list
    (lambda (uvar reg bt)
      (map (lambda (entry) 
	     (let ([tail (cdr entry)])
	          (if (memq uvar tail)
	              (begin
			(set-cdr! entry (set-cons reg (cdr (remq uvar entry))))
			(update-frd-home (car entry) reg bt uvar)
	                entry)
	              entry))) bt)))
  ;; This function find homes for move-related spill variables
  (define find-mb-homes
    (lambda (var* bt)
      (cond
	[(null? bt) friends-home]
	[(null? var*) friends-home]
	[else (let* ([cvar (car var*)]
		     [bias-tbl-entry (assq cvar bt)]
		     [frd-vars (if bias-tbl-entry (cdr bias-tbl-entry) '())]
		     [cf-entry (cdr (assq cvar conflict-list))])
      		    (if (null? frd-vars) 
	  		(find-mb-homes (cdr var*) bt)
	  		(let ([friend-register (find-friend-reg frd-vars cf-entry)])
	  		     (cond
	    		       [(equal? friend-register #f) (find-mb-homes (cdr var*) bt)]
	    		       [else 
				   (begin (set! conflict-list (update-clist (list (list cvar friend-register)) conflict-list))
		       		  	  (let ([updated-bias (update-bias-list cvar friend-register bt)])
			    		       (begin
		 	      			 (unless (assq cvar friends-home) 
		              			 (set! friends-home (cons (list cvar friend-register) friends-home)))
			      			 (find-mb-homes (cdr var*) updated-bias))))]))))])))
  ;; This function checks if a register is available in any of its friends list in home*
  (define enquire-friend
    (lambda (fb-list home*)
      (cond
	((null? fb-list) #f)
	((register? (car fb-list)) (enquire-friend (cdr fb-list) home*))
	((assq (car fb-list) home*) => (lambda (x) (cadr x)))
	(else (enquire-friend (cdr fb-list) home*)))))

  ;; It identifies the conflicting registers
  (define find-used
    (lambda (conflict* home*)
      (cond
        [(null? conflict*) '()]
        [(register? (car conflict*))
         (set-cons (car conflict*) (find-used (cdr conflict*) home*))]
        [(assq (car conflict*) home*) =>
         (lambda (x) (set-cons (cadr x) (find-used (cdr conflict*) home*)))]
        [else (find-used (cdr conflict*) home*)])))
  ;; It selects appropriate register for given uvar
  (define select-register
    (lambda (var conflict* home* bias-lst)
      (let ([used* (find-used conflict* home*)])
	(let* ([frds (assq var bias-lst)]
	       [fb-list (if frds (cdr frds) #f)]
	       [fr-reg (if fb-list (enquire-friend fb-list home*) #f)])
              (let* ([fr-reg* (if fr-reg (difference (list fr-reg) used*) '())]
		     [available* (if (null? fr-reg*) (difference registers used*) fr-reg*)])
                    (and (not (null? available*)) (car available*)))))))
  ;; It is used to remove conflicting variables
  (define rem-conflicts!
    (lambda (ct var conflict*)
      (for-each
        (lambda (x)
          (when (uvar? x)
            (let ([a (assq x ct)])
              (set-cdr! a (remq var (cdr a))))))
        conflict*)))
  ;; It allocates register for uvars
  (define find-homes
    (lambda (var* ct bias-lst)
      (define k (length registers))
      (define low-degree?
        (lambda (var)
          (< (length (cdr (assq var ct))) k)))
      (let f ([var* var*])
        (if (null? var*)
            '()  ; empty homes to begin with
            (let ([var (or (find low-degree? var*) (car var*))])
              (let ([conflict* (cdr (assq var ct))] [var* (remq var var*)])
                (rem-conflicts! ct var conflict*)
                (let ([home* (f var*)])
                  (let ([reg (select-register var conflict* home* bias-lst)])
                    (if reg
                        (cons `[,var ,reg] home*)
                        home*)))))))))
  ;; It process the incomplete and complete body statements
  (define (Body x)
    (match x
      [(locals (,local* ...)
         (ulocals (,ulocal* ...)
           (locate (,frame-home* ...)
             (frame-conflict ,fv-ct
               (register-conflict ,ct ,tail)))))
         (set! friends-home '())
         (set! conflict-list ct)
         (let* ([uvar* (append local* ulocal*)] 
	        [bias-list (move-bias tail register? uvar*)]
	        [bias-lst-wcf (filter-bias (rem-bt-conflicts bias-list conflict-list))])
               (let* ([biased-home* (find-mb-homes uvar* bias-lst-wcf)]
	  	      [homes (if (null? biased-home*) '() (map car biased-home*))]
		      [home* (find-homes (difference uvar* homes) conflict-list bias-lst-wcf)])
                     (let ([spill* (difference uvar* (union (map car home*) homes))])
                          (cond
                            [(null? spill*) `(locate (,frame-home* ... ,biased-home* ... ,home* ...) ,tail)]
                            [(null? (intersection ulocal* spill*))
                              (let ([local* (difference local* spill*)])
                                  `(locals (,local* ...)
                                     (ulocals (,ulocal* ...)
                                       (spills (,spill* ...)
                                         (locate (,frame-home* ...)
                                           (frame-conflict ,fv-ct ,tail))))))]
                            [else
                              (error who "unspillable variables (~s) have been spilled"
                                (difference spill* local*))]))))]
      [(locate (,home* ...) ,tail) `(locate (,home* ...) ,tail)]
      [,x (error who "invalid Body ~s" x)]))
  ;; It process the letrec statement
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
