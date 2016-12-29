#|
Program name    : expose-basic-blocks.ss
Functions       : expose-basic-blocks
Description     : This program changes the structure of the code by adding bindings to different statements.
                  It converts the code with nested if and begin statements into a code containing only basic blocks.
Input Language  : Scheme code with mset!/mref replaced by displacement/index mode operands
Output Language : Code containing only basic blocks
|#

#!chezscheme
(library (Compiler expose-basic-blocks)
  (export
    expose-basic-blocks)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass40 of the compiler
(define-who expose-basic-blocks
  ;; It process set!, if, begin statements and convert the nested if and begin statements into basic-blocks
  ;; in Effect
  (define Effect
    (lambda (effect effect* joinblock)
      (match effect
        [(set! ,x ,rhs) (Effect_processfromback effect* `((set! ,x ,rhs) ,joinblock ...))]
        [(if ,pred ,effect1 ,effect2) 
         (let*-values ([(alb clb joinlb) (values (unique-label 'a) (unique-label 'c) (unique-label 'j))]
                       [(pred_exp predbindings) (Pred pred clb alb)]
                       [(c_exp cbindings) (Effect effect1 '() `((,joinlb)))]
                       [(a_exp abindings) (Effect effect2 '() `((,joinlb)))]
                       [(frontexp frontbindings) (Effect_processfromback effect* `(,pred_exp))])
         (values frontexp `(,frontbindings ... ,predbindings ...  
                 [,clb (lambda() ,c_exp)] ,cbindings ... 
                 [,alb (lambda() ,a_exp)] ,abindings ...
                 [,joinlb (lambda () ,(make-begin joinblock))])))]
        [(begin ,effect1* ... ,effect1) 
         (Effect_processfromback (append effect* (append effect1* (list effect1))) joinblock)]
	[(return-point ,rp-label ,tail)
	   (let*-values ([(tail_val tailbindings) (Tail tail)]
			 [(effect_val frontbindings) (Effect_processfromback effect* `(,tail_val))])
           (values effect_val `(,frontbindings ... ,tailbindings ... (,rp-label (lambda() ,(make-begin joinblock))))))]
        [(,x) (guard (equal? x 'nop)) (Effect_processfromback effect* joinblock)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It helps in processing the Effect statements from back to front.
  (define Effect_processfromback 
    (lambda (effect* joinblock)
      (match effect*
        [(,effect* ... ,effect) (Effect effect effect* joinblock)]
        [() (values (make-begin joinblock) '())]
        [,x (errorf who "unexpected effect*: ~s" x) x])))
  ;; It process (bool), if, begin statements and convert the nested if and begin statements into basic-blocks
  ;; in Predicate
  (define Pred
    (lambda (pred clb alb)
      (match pred
        [(,bool) (if (equal? 'true bool) (values `(,clb) '()) (values `(,alb) '()))]
        [(,relop ,triv1 ,triv2) (guard (memq relop '(< <= = >= >))) (values `(if (,relop ,triv1 ,triv2) (,clb) (,alb)) '())]
        [(if ,pred0 ,pred1 ,pred2)
         (let*-values ([(alb1 clb1) (values (unique-label 'a) (unique-label 'c))]
                       [(pred_exp predbindings) (Pred pred0 clb1 alb1)]
                       [(c_exp cbindings) (Pred pred1 clb alb)]
                       [(a_exp abindings) (Pred pred2 clb alb)])
         (values pred_exp `(,predbindings ...  [,clb1 (lambda() ,c_exp)] ,cbindings ... [,alb1 (lambda() ,a_exp)] ,abindings ...)))]
        [(begin ,effect* ... ,pred) 
         (let*-values ([(pred_val predbindings) (Pred pred clb alb)]
                       [(effect_val frontbindings) (Effect_processfromback effect* `(,pred_val))])
         (values effect_val `(,frontbindings ... ,predbindings ...)))]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It process (triv), if, begin statements and convert the nested if and begin statements into basic-blocks
  ;; in Tail
  (define Tail
    (lambda (tail)
      (match tail
        [(,triv) (values `(,triv) '())]
        [(begin ,effect* ... ,tail)
         (let*-values ([(tail_val tailbindings) (Tail tail)]
                       [(effect_val frontbindings) (Effect_processfromback effect* `(,tail_val))])
         (values effect_val `(,frontbindings ... ,tailbindings ...)))]
        [(if ,pred ,tail1 ,tail2)
         (let*-values ([(alb clb) (values (unique-label 'a) (unique-label 'c))]
                       [(pred_exp predbindings) (Pred pred clb alb)]
                       [(c_exp cbindings) (Tail tail1)]
                       [(a_exp abindings) (Tail tail2)])
         (values pred_exp `(,predbindings ...  [,clb (lambda() ,c_exp)] ,cbindings ... [,alb (lambda() ,a_exp)] ,abindings ...)))]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It process letrec statement and convert the nested if and begin statements into basic-blocks
  ;; in the program
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Tail -> tail* tailbindings*])] ...) ,[Tail -> tail tailbindings])
      `(letrec ([,label* (lambda () ,tail*)]... ,tailbindings* ... ... ,tailbindings ...) ,tail)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))
)
