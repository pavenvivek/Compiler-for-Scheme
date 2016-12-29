#|
Program name    : uncover-register-conflict.ss
Functions       : uncover-register-conflict
Description     : This program will identify the conflicting registers and uvars for each uvar in the
                  locals list.
Input Language  : Scheme
Output Language : Scheme with a conflict graph consisting of conflict list for all the uvars in locals list.
|#

#!chezscheme
(library (Compiler uncover-register-conflict)
  (export
    uncover-register-conflict)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

(define warn-if-dead-at-assignment (make-parameter #f))

;; Defines pass31 of the compiler
(define-who uncover-register-conflict
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
  (define Triv (lambda (x) (if (or (uvar? x) (register? x)) `(,x) '())))
  ;; It process the statements in Effect from backwards
  (define Effect*
    (lambda (x live* ct)
      (match x
        [() live*]
        [(,ef* ... ,ef) (Effect* ef* (Effect ef live* ct) ct)]
        [,x (error who "invalid Effect* list ~s" x)])))
  ;; It uncover conflicts for uvars in Effect* part of grammer
  (define Effect
    (lambda (x live* ct)
      (match x
        [(nop) live*]
        [(if ,test ,[c-live*] ,[a-live*]) 
         (Pred test c-live* a-live* ct)]
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        [(set! ,lhs (mref ,[Triv -> x-live*] ,[Triv -> y-live*]))
         (let ([live* (difference live* `(,lhs))])
           (when (or (uvar? lhs) (register? lhs))
             (add-conflicts! ct lhs live*))
           (union x-live* y-live* live*))]
	[(mset! ,lhs ,var1 ,var2) 
           (union (Triv lhs) (Triv var1) (Triv var2) live*)]
        [(set! ,lhs ,rhs)
         (guard (or (uvar? lhs) (register? lhs)) (not (memq lhs live*)))
         (when (warn-if-dead-at-assignment)
           (warning who "~s is not live at assignment ~s" lhs `(set! ,lhs ,rhs)))
         (Effect `(set! ,lhs ,rhs) (cons lhs live*) ct)]
        [(set! ,lhs (,binop ,[Triv -> x-live*] ,[Triv -> y-live*]))
         (let ([live* (difference live* `(,lhs))])
           (when (or (uvar? lhs) (register? lhs))
             (add-conflicts! ct lhs live*))
           (union x-live* y-live* live*))]
        [(set! ,lhs ,var)
         (let ([live* (difference live* `(,lhs))])
           (when (or (uvar? lhs) (register? lhs))
             (add-conflicts! ct lhs (remq var live*)))
           (union (Triv var) live*))]
	[(return-point ,rp-label ,tail) (Tail tail ct)]
        [,x (error who "invalid Effect list ~s" x)])))
  ;; It uncover conflicts for uvars in Predicate part of grammer
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
  ;; It uncover conflicts for uvars in Tail part of grammer
  (define Tail
    (lambda (x ct)
      (match x
        [(begin ,ef* ... ,[live*]) (Effect* ef* live* ct)]
        [(if ,test ,[c-live*] ,[a-live*]) 
         (Pred test c-live* a-live* ct)]
        [(,[Triv -> target-live*] ,live* ...)
         (union target-live*
           (filter
             (lambda (x) (or (register? x) (uvar? x)))
             live*))]
        [,x (error who "invalid Tail ~s" x)])))
  ;; It uncover conflicts for uvars in Body part of grammer
  (define Body
    (lambda (x)
      (match x
        [(locals (,uvar* ...) (ulocals (,uvar2* ...) (locate (,x* ...) (frame-conflict (,y* ...) ,tail))))
         (let ([ct (map (lambda (x) (cons x '())) (append uvar* uvar2*))])
           (let ([uvar* (filter uvar? (Tail tail ct))])
             (unless (null? uvar*)
               (warning who "found variables ~s live on entry" uvar*)))
            `(locals (,uvar* ...) (ulocals (,uvar2* ...) (locate (,x* ...) (frame-conflict (,y* ...)
             (register-conflict ,ct ,tail))))))]
        [(locate (,x* ...) ,tail) `(locate (,x* ...) ,tail)]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
      [(letrec ([,label* (lambda () ,[Body -> body*])] ...) ,[Body -> body])
       `(letrec ([,label* (lambda () ,body*)] ...) ,body)]
      [,x (error who "invalid Program ~s" x)])))
)
