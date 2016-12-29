#|
Program name    : parse-scheme.ss
Functions       : parse-scheme
Description     : This program verify the scheme code and restructure code obeying current grammer to 
		  a code that obeys assignment 14 grammer
Input Language  : Scheme Code
Output Language : Scheme Code obeying grammer of assignment 14
|#

#!chezscheme
(library (Compiler parse-scheme)
  (export
    parse-scheme)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass1 of the compiler
(define-who parse-scheme
  (define primitives
    '((+ . 2) (- . 2) (* . 2) (<= . 2) (< . 2) (= . 2)
      (>= . 2) (> . 2) (boolean? . 1) (car . 1) (cdr . 1)
      (cons . 2) (eq? . 2) (fixnum? . 1) (make-vector . 1)
      (null? . 1) (pair? . 1) (procedure? . 1) (set-car! . 2)
      (set-cdr! . 2) (vector? . 1) (vector-length . 1)
      (vector-ref . 2) (vector-set! . 3) (void . 0)))
  ;; Check if the given value is a constant
  (define (constant? x)
    (or (memq x '(#t #f ()))
        (and (and (integer? x) (exact? x))
             (or (fixnum-range? x)
                 (error who "integer ~s is out of fixnum range" x)))))
  ;; Check if the given value is a datum
  (define (datum? x)
    (or (constant? x)
        (if (pair? x)
            (and (datum? (car x)) (datum? (cdr x)))
            (and (vector? x) (andmap datum? (vector->list x))))))
  ;; Add new bindings to environment shadowing older bindings if any
  (define shadow-vars
    (lambda (lst env env*)
      (cond
        ((null? lst) env)
	((assq (car lst) env) (cons (car env*) (shadow-vars (cdr lst) (remq (assq (car lst) env) env) (cdr env*))))
	(else (cons (car env*) (shadow-vars (cdr lst) env (cdr env*)))))))
  ;; It the given list for duplicates
  (define check-duplicates
    (lambda (lst)
      (cond
        ((null? lst) #f)
        ((memq (car lst) (cdr lst)) #t)
        (else (check-duplicates (cdr lst))))))
  (define Program
    (lambda (x)
      (define all-uvar* '())
      ;; Handle Expression part of the grammer
      (define Expr
        (lambda (env)
          (lambda (x)
            (match x
	      [,x (guard (constant? x)) `(quote ,x)]
	      [,x (guard (symbol? x)) 
		(if (assq x env)
		    (cdr (assq x env))
		    (error who "unbound variable ~s" x))]
              [(quote ,x) (guard (not (assq 'quote env)))
                 (unless (datum? x) (error who "invalid datum ~s" x))
                `(quote ,x)]
              [(if ,[(Expr env) -> x] ,[(Expr env) -> y] ,[(Expr env) -> z]) (guard (not (assq 'if env))) `(if ,x ,y ,z)]
	      [(if ,[(Expr env) -> x] ,[(Expr env) -> y]) (guard (not (assq 'if env))) `(if ,x ,y (void))]
              [(begin ,[(Expr env) -> x*] ... ,[(Expr env) -> x]) (guard (not (assq 'begin env))) (make-begin `(,x* ... ,x))]
              [(lambda (,fml* ...) ,tail* ...) (guard (not (assq 'lambda env)))
		 (when (null? tail*) (error who "too few arguments for ~s") 'lambda)
		 (when (check-duplicates fml*) (error who "non-unique arguments for ~s") 'lambda)
		 (when (memq #f (map symbol? fml*)) (error who "invalid arguments for ~s") 'lambda)
		 (let* ([new-uvars (map (lambda (x) (unique-name x)) fml*)]
			[env* (map cons fml* new-uvars)]
			[shd-env* (shadow-vars fml* env env*)]
			[tail (map (Expr shd-env*) tail*)])
		       `(lambda ,new-uvars ,(make-begin `(,tail ...))))]
              [(let ([,new-var* ,[(Expr env) -> x*]] ...) ,tail* ...) (guard (not (assq 'let env)))
		 (when (null? tail*) (error who "too few arguments for ~s") 'let)
		 (when (check-duplicates new-var*) (error who "non-unique arguments for ~s") 'let)
		 (let* ([new-uvars (map (lambda (x) (unique-name x)) new-var*)]
			[env* (map cons new-var* new-uvars)]
			[shd-env* (shadow-vars new-var* env env*)]
			[tail (map (Expr shd-env*) tail*)])
		       `(let ([,new-uvars ,x*] ...) ,(make-begin `(,tail ...))))]
              [(letrec ([,new-var* ,rhs*] ...) ,tail* ...) (guard (not (assq 'letrec env)))
		 (when (null? tail*) (error who "too few arguments for ~s") 'letrec)
		 (when (check-duplicates new-var*) (error who "non-unique arguments for ~s") 'letrec)
		 (let* ([new-uvars (map (lambda (x) (unique-name x)) new-var*)]
			[env* (map cons new-var* new-uvars)]
			[shd-env* (shadow-vars new-var* env env*)]
			[tail (map (Expr shd-env*) tail*)]
			[rhs** (map (Expr shd-env*) rhs*)])
		       `(letrec ([,new-uvars ,rhs**] ...) ,(make-begin `(,tail ...))))]
              [(set! ,var ,[(Expr env) -> x]) (guard (not (assq 'set! env)))
                 (if (assq var env)
                    `(set! ,(cdr (assq var env)) ,x)
                     (error who "unbound uvar ~s" var))]
	      [(not ,[(Expr env) -> e]) (guard (not (assq 'not env))) `(if ,e (quote #f) (quote #t))]
 	      [(and ,[(Expr env) -> x*] ...) (guard (not (assq 'and env)))
     		 (if (null? x*)
         	    '(quote #t)
         	     (let f ([x* x*])
           		(let ([x (car x*)] [x* (cdr x*)])
             		     (if (null? x*)
                		 x
                 		`(if ,x ,(f x*) (quote #f))))))]
 	      [(or ,[(Expr env) -> x*] ...) (guard (not (assq 'or env)))
     		 (if (null? x*)
         	    '(quote #f)
         	     (let f ([x* x*])
           		(let ([x (car x*)] [x* (cdr x*)])
             		     (if (null? x*)
                		 x	
				 (let ([t (unique-name 't)])
                 		     `(let ([,t ,x]) (if ,t ,t ,(f x*))))))))]	      
              [(,prim ,[(Expr env) -> x*] ...) (guard (and (assq prim primitives) (not (assq prim env))))
               (unless (= (length x*) (cdr (assq prim primitives)))
                 (error who "too many or few arguments ~s for ~s" (length x*) prim))
               `(,prim ,x* ...)]
              [(,[(Expr env) -> x] ,[(Expr env) -> y] ...) `(,x ,y ...)]
              [,x (error who "invalid Expr ~s" x)]))))
      ((Expr '()) x)))
  (lambda (x) (let ([prg (Program x)]) prg)))

)

