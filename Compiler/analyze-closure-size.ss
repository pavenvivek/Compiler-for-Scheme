#|
Program name    : analyze-closure-size.ss
Functions       : analyze-closure-size
Description     : This program will identify the free variables inside letrec body
Input Language  : Scheme
Output Language : Scheme with free variables exposed
|#

#!chezscheme
(library (Compiler analyze-closure-size)
  (export
    analyze-closure-size)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

(define-who analyze-closure-size
  (define primitives
    '(+ - * <= < = >= > boolean? car cdr cons eq? fixnum?
      make-vector null? pair? procedure? set-car! set-cdr! vector?
      vector-length vector-ref vector-set! void))
  (define Lambda
    (lambda (x)
      (match x
        [(lambda (,fml* ...)
           (bind-free (,cp ,free* ...)
             ,[Expr -> s*]))
         s*]
        [,x (error who "invalid Lambda ~s" x)])))
  (define Expr
    (lambda (x)
      (match x
        [,label (guard (label? label)) '()]
        [,uvar (guard (uvar? uvar)) '()]
        [(quote ,imm) '()]
        [(if ,[test-s*] ,[conseq-s*] ,[altern-s*])
         (append test-s* conseq-s* altern-s*)]
        [(begin ,[s**] ... ,[s*]) (apply append s* s**)]
        [(let ([,lhs* ,[s**]] ...) ,[s*]) (apply append s* s**)]
        [(letrec ([,llabel* ,[Lambda -> s**]] ...)
           (closures ([,name* ,clabel* ,free** ...] ...)
             ,[s*]))
         (apply append (map length free**) s* s**)]
        [(,prim ,[s**] ...)
         (guard (memq prim primitives))
         (apply append s**)]
        [(,[s*] ,[s**] ...) (apply append s* s**)]
        [,x (error who "invalid Expr ~s" x)])))
  (lambda (x)
    (let ([s* (Expr x)])
      (let ([n (length s*)])
        (printf "num = ~s, avg = ~s: ~s\n"
          n
          (if (= n 0) '* (exact->inexact (/ (apply + s*) n)))
          s*)))
    x))
)
