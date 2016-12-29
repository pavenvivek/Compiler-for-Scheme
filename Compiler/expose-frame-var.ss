#|
Program name    : expose-frame-var.ss
Functions       : expose-frame-var
Description     : This program converts the occurrences of frame-var into displacement mode
                  operands. Then it returns the modified code to the flatten-program pass.
Input Language  : Scheme with uvars replaced by corresponding locations and (locate ...), (nop) statements
                  removed
Output Language : Scheme code with frame-vars replaced by displacement mode operands
|#

#!chezscheme
(library (Compiler expose-frame-var)
  (export
    expose-frame-var)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass38 of the compiler
(define-who expose-frame-var
  (define nb 0)
  ;; converts the frame-var to displacement mode operand with rbp as base register
  (define Triv
    (lambda (t)
      (if (frame-var? t)
          (make-disp-opnd frame-pointer-register
            (- (ash (frame-var->index t) word-shift) nb))
          t)))
  ;; It process relop, if, begin, bool statements and replace the frame-vars with displacement mode operand
  ;; in Predicate
  (define Pred
    (lambda (pred)
      (match pred
        [(if ,[Pred -> pred0] ,[Pred -> pred1] ,[Pred -> pred2]) `(if ,pred0 ,pred1 ,pred2)]
        [(begin ,[Effect -> effect*] ... ,[Pred -> pred]) `(begin ,effect* ... ,pred)]
        [(,relop ,[Triv -> triv1] ,[Triv -> triv2]) `(,relop ,triv1 ,triv2)]
        [(true) `(true)]
        [(false) `(false)]
        [,tl (error who "invalid syntax for Predicate" tl)])))
  ;; It process set!, if, begin statements and replace the frame-vars with displacement mode operand
  ;; in Effect
  (define Effect
    (lambda (st)
      (match st
	[(set! rbp (+ rbp ,nb-val)) (begin (set! nb 0) `(set! rbp (+ rbp ,nb-val)))]
	[(set! rbp (- rbp ,nb-val)) (begin (set! nb nb-val) `(set! rbp (- rbp ,nb-val)))]
	[(set! ,[Triv -> lhs] (mref ,[Triv -> x] ,[Triv -> y])) `(set! ,lhs (mref ,x ,y))]
	[(mset! ,[Triv -> lhs] ,[Triv -> var1] ,[Triv -> var2]) `(mset! ,lhs ,var1 ,var2)] 
        [(set! ,[Triv -> var] (,binop ,[Triv -> t1] ,[Triv -> t2]))
         `(set! ,var (,binop ,t1 ,t2))]
        [(set! ,[Triv -> var] ,[Triv -> t])
         `(set! ,var ,t)]
        [(if ,[Pred -> pred] ,[Effect -> effect1] ,[Effect -> effect2]) `(if ,pred ,effect1 ,effect2)]
        [(begin ,[Effect -> effect*] ... ,[Effect -> effect]) `(begin ,effect* ... ,effect)]
	[(return-point ,rp-label ,[Tail -> tail]) `(return-point ,rp-label ,tail)]
        [(,x) (guard (equal? x 'nop)) `(,x)]
        [,st (errorf who "invalid syntax for Effect ~s" st)])))
  ;; It process (triv), if, begin statements and replace the frame-vars with displacement mode operand
  ;; in Tail
  (define Tail
    (lambda (tail)
      (match tail
        [(,[Triv -> t]) `(,t)]
        [(begin ,[Effect -> ef*] ... ,[Tail -> tail])
        `(begin ,ef* ... ,tail)]
        [(if ,[Pred -> pred] ,[Tail -> tail1] ,[Tail -> tail2]) `(if ,pred ,tail1 ,tail2)]
        [,tail (errorf who "invalid syntax for Tail ~s" tail)])))
  ;; It process letrec statement and replace the frame-vars with displacement mode operand
  ;; in the program
  (lambda (program)
    (match program
      [(letrec ([,label* (lambda () ,[Tail -> tail*])] ...) ,[Tail -> tail])
	;(set! nb 0)
       `(letrec ([,label* (lambda () ,tail*)] ...) ,tail)]
      [,program (errorf who "invalid syntax for Program: ~s" program)])))
)
