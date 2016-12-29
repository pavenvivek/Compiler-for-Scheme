#|
Program name    : generate-x86-64.ss
Functions       : generate-x86-64
Description     : This program takes the flattend scheme code as input and converts that
                  into an equivalent assembly code.
Input Language  : flattened scheme code which closely resembles assembly code
Output Language : assembly code
|#

#!chezscheme
(library (Compiler generate-x86-64)
  (export
    generate-x86-64)
  (import 
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass43 of the compiler
(define-who generate-x86-64
  ;; emit X86_64 instructions according to the given binery operator
  (define prim->inst
    (lambda (op)
      (case op
        [(+) 'addq]
        [(-) 'subq]
        [(*) 'imulq]
        [(logand) 'andq]
        [(logor) 'orq]
        [(sra) 'sarq]
        [else (error who "unexpected binop ~s" op)])))
  ;; emit X86_64 instructions according to the given relational operator
  (define relop->inst
    (lambda (op)
      (case op
        [(=) 'je]
        [(>) 'jg]
        [(<) 'jl]
        [(>=) 'jge]
        [(<=) 'jle])))
  (define relop_not->inst
    (lambda (op)
      (case op
        [(=) 'jne]
        [(>) 'jle]
        [(<) 'jge]
        [(>=) 'jl]
        [(<=) 'jg])))
  ;; emit equivalent X86_64 instructions for the flattened scheme code
  (define Effect
    (lambda (st)
      (match st
        [(set! ,x1 (,op ,x1 ,x2)) 
         (emit (prim->inst op) x2 x1)] 
        [(set! ,x ,rhs) (guard (label? rhs))
         (emit 'leaq rhs x)]
        [(set! ,x ,rhs)
         (emit 'movq rhs x)]
        [(if (not (,relop ,triv1 ,triv2)) (jump ,lb)) (emit 'cmpq triv2 triv1) (emit-jump (relop_not->inst relop) lb)]
        [(if (,relop ,triv1 ,triv2) (jump ,lb)) (emit 'cmpq triv2 triv1) (emit-jump (relop->inst relop) lb)]
        [() (void)]
        [(jump ,ins)
         (emit-jump 'jmp ins)]
        [,x (guard (label? x)) (emit-label x)]
        [,st (error who "unexpected effect ~s" st)])))
  (lambda (code)
    (match code
      [(code ,x* ...) (emit-program (for-each Effect x*))]
      [() (void)]
      [,x (error who "Invalid Syntax: ~s\n" exp)])))
)
