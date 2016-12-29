#|
Program name    : uncover-frame-conflict.ss
Functions       : uncover-frame-conflict
Description     : This program will identify the conflicting frame-vars and uvars for each uvar in the
                  locals list.
Input Language  : Scheme with allocation pointers exposed
Output Language : Scheme with a frame-conflict graph consisting of conflict list for all the uvars in locals list.
|#

#!chezscheme
(library (Compiler uncover-frame-conflict)
  (export
    uncover-frame-conflict)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

(define warn-if-dead-at-assignment (make-parameter #f))

;; Defines pass27 of the compiler
(define-who uncover-frame-conflict
  (define call-live '())
  ;; It updates the conflict list based on new conflicts
  (define add-conflicts!
    (lambda (ct lhs live*)
      (define add-conflict!
        (lambda (var1 var2)
          (let ([a (assq var1 ct)])
            (set-cdr! a (set-cons var2 (cdr a))))))
      (when (uvar? lhs)
        (for-each
          (lambda (live) (add-conflict! lhs live))
          live*))
      (for-each
        (lambda (live) (when (uvar? live) (add-conflict! live lhs)))
        live*)))
  (define Triv (lambda (x) (if (or (uvar? x) (frame-var? x)) `(,x) '())))
  ;; It process the statements in Effect from backwards
  (define Effect*
    (lambda (x live* ct)
      (match x
        [() live*]
        [(,ef* ... ,ef) (Effect* ef* (Effect ef live* ct) ct)]
        [,x (error who "invalid Effect* list ~s" x)])))
  ;; It process the Effect part of the grammer in reverse
  (define Effect
    (lambda (x live* ct)
      (match x
        [(nop) live*]
        [(if ,test ,[c-live*] ,[a-live*]) 
         (Pred test c-live* a-live* ct)]
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        [(set! ,lhs (mref ,[Triv -> x-live*] ,[Triv -> y-live*]))
         (let ([live* (difference live* `(,lhs))])
           (when (or (uvar? lhs) (frame-var? lhs))
             (add-conflicts! ct lhs live*))
           (union x-live* y-live* live*))]
        [(set! ,lhs ,rhs)
         (guard (or (uvar? lhs) (frame-var? lhs)) (not (memq lhs live*)))
         (when (warn-if-dead-at-assignment)
           (warning who "~s is not live at assignment ~s" lhs `(set! ,lhs ,rhs)))
         (Effect `(set! ,lhs ,rhs) (cons lhs live*) ct)]
        [(set! ,lhs (,binop ,[Triv -> x-live*] ,[Triv -> y-live*]))
         (let ([live* (difference live* `(,lhs))])
           (when (or (uvar? lhs) (frame-var? lhs))
             (add-conflicts! ct lhs live*))
           (union x-live* y-live* live*))]
        [(set! ,lhs ,var)
         (let ([live* (difference live* `(,lhs))])
           (when (or (uvar? lhs) (frame-var? lhs))
             (add-conflicts! ct lhs (remq var live*)))
           (union (Triv var) live*))]
	[(mset! ,lhs ,var1 ,var2) 
           (union (Triv lhs) (Triv var1) (Triv var2) live*)]
	[(return-point ,label ,tail) (begin (set! call-live (union live* call-live)) (union (Tail tail ct) live*))]
        [,x (error who "invalid Effect list ~s" x)])))
  ;; It process the Predicate part of the grammer
  (define Pred
    (lambda (x t-live* f-live* ct)
      (match x
        [(true) t-live*]
        [(false) f-live*]
        [(if ,test ,[c-live*] ,[a-live*])
         (Pred test c-live* a-live* ct)]
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        [(,relop ,[Triv -> x-live*] ,[Triv -> y-live*])
         (union t-live* f-live* x-live* y-live*)]
        [,x (error who "invalid Pred ~s" x)])))
  ;; It process the Tail part of the grammer
  (define Tail
    (lambda (x ct)
      (match x
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        [(if ,test ,[c-live*] ,[a-live*]) 
         (Pred test c-live* a-live* ct)]
        [(,[Triv -> target-live*] ,live* ...)
         (union target-live*
           (filter
             (lambda (x) (or (frame-var? x) (uvar? x)))
             live*))]
        [,x (error who "invalid Tail ~s" x)])))
  ;; It process the Body part of the grammer
  (define Body
    (lambda (x)
      (match x
        [(locals (,uvar* ...) (new-frames (,Frame* ...) ,tail)) 
	 (set! call-live '())
         (let ([ct (map (lambda (x) (cons x '())) uvar*)])
           (let ([uvar* (filter uvar? (Tail tail ct))])
             (unless (null? uvar*)
               (warning who "found variables ~s live on entry" uvar*)))
           `(locals ,(difference uvar* call-live) (new-frames (,Frame* ...) (spills ,(filter uvar? call-live)
              (frame-conflict ,ct (call-live ,call-live ,tail))))))]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body]) 
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
)
