#|
Program name    : flatten-program.ss
Functions       : flatten-program
Description     : This program flattens the scheme code by removing begin forms, letrec forms, 
                  turning calls into explicit jumps and turning names of procedures into
                  label forms. Then it returns the modified code to the generate-x86-64 pass.
                  It also handles the two-way conditional if expressions and unconditional jumps
                  in tail.
Input Language  : Code with basic blocks
Output Language : flattened scheme code which closely resembles assembly code
|#

#!chezscheme
(library (Compiler flatten-program)
  (export
    flatten-program)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass42 of the compiler
(define-who flatten-program
  (define labl-list '())
  (define eff-list '())
  ;; Flattens the Effect* part of the code
  (define Effect
    (lambda (st)
      (match st
        [(set! ,x ,rhs) 
        `(set! ,x ,rhs)]
        [,st (error who "unexpected effect ~s" st)])))
  ;; Flattens the Tail part of code
  (define Tail
   (lambda (next_labl)
     (lambda (tl)
       (match tl
         [(begin ,[Effect -> x*] ... ,[(Tail next_labl) -> tail]) `(,x* ... ,tail ...)]
         [(if ,pred (,clb) (,alb))
          (if (equal? clb next_labl)
          (cons `(if (not ,pred) (jump ,alb)) (list clb))
          (if (equal? alb next_labl) 
          (cons `(if ,pred (jump ,clb)) (list alb)) 
          (cons `(if ,pred (jump ,clb)) (list `(jump ,alb) next_labl))))]
         [(,x) (if (equal? next_labl '())
          `((jump ,x))
          (if (label? x) (if (equal? x next_labl) `(,next_labl) `((jump ,x) ,next_labl)) `((jump ,x) ,next_labl)))]
         [,tl (error who "invalid syntax for Tail" tl)]))))
  ;; Flattens the Program
  (lambda (code)
    (match code
      [(letrec ([,labl (lambda() ,val*)] ...) ,tail)
       (begin
         (set! labl-list labl)
         (set! eff-list val*) 
       (let* ([val* (do ([i 0 (+ i 1)] [lst '()])
                          ((>= i (length labl)) lst)
                          (if (equal? i (sub1 (length labl)))
                              (set! lst (append lst ((Tail '()) (list-ref val* i))))
                              (set! lst (append lst ((Tail (list-ref labl (+ i 1))) (list-ref val* i))))))]
                [tail (if (not (equal? '() labl)) ((Tail (car labl)) tail) ((Tail '()) tail))])
               `(code ,tail ... ,val* ...)))]
      [() (void)]
      [,x (error who "Invalid Syntax: ~s\n" exp)])))
)
