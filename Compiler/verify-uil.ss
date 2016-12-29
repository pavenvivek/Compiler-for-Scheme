#|
Program name    : verify-uil.ss
Functions       : verify-uil
Description     : This program verify whether the language-dependent portion creates well-formed UIL code.
                  If not it raises Invalid syntax exception. If the given code is valid with respect to the 
		  grammer then it returns the code to the expose-frame-var pass.
Input Language  : Scheme with let removed
Output Language : Scheme
|#

(library (Compiler verify-uil)
  (export verify-uil)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Defines pass22 of the compiler
(define-who verify-uil
  (define binops '(+ - * logand logor sra))
  (define relops '(< > <= >= =))
  (define verify-x-list
    (lambda (x* x? what)
      (let loop ([x* x*] [idx* '()])
        (unless (null? x*)
          (let ([x (car x*)] [x* (cdr x*)])
            (unless (x? x)
              (error who "invalid ~s ~s found" what x))
            (let ([idx (extract-suffix x)])
              (when (member idx idx*)
                (error who "non-unique ~s suffix ~s found" what idx))
              (loop x* (cons idx idx*))))))))
  (define Triv
    (lambda (label* uvar*)
      (lambda (t)
        (unless (or (label? t) (uvar? t) (and (integer? t) (exact? t)))
          (error who "invalid Triv ~s" t))
        (when (and (integer? t) (exact? t))
          (unless (int64? t)
            (error who "integer out of 64-bit range ~s" t)))
        (when (uvar? t)
          (unless (memq t uvar*)
            (error who "reference to unbound uvar ~s" t)))
        (when (label? t)
          (unless (memq t label*)
            (error who "unbound label ~s" t)))
        (values))))
  ;; check the validity of Value part of grammer
  ;; It process if, begin, mref, alloc, binop statements and report if they have any invalid syntax
  ;; as per the constraints defined in the grammer 
  (define Value
    (lambda (label* uvar*)
      (lambda (val)
        (match val
          [(if ,[(Pred label* uvar*) ->] ,[] ,[]) (values)]
          [(begin ,[(Effect label* uvar*) ->] ... ,[]) (values)]
	  [(mref ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->]) (values)]
	  [(alloc ,[(Value label* uvar*) ->]) (values)]
          [(sra ,[] ,y)
           (unless (uint6? y)
             (error who "invalid sra operand ~s" y))
           (values)]
          [(,binop ,[] ,[])
           (guard (memq binop binops))
           (values)]
          [(,[] ,[] ...) (values)]
          [,[(Triv label* uvar*) ->] (values)]))))
  ;; check the validity of Effect* part of grammer
  ;; It process set!, if, begin, mset!, nop statements and report if they have any invalid syntax
  ;; as per the constraints defined in the grammer 
  (define Effect
    (lambda (label* uvar*)
      (lambda (ef)
        (match ef
          [(nop) (values)]
          [(if ,[(Pred label* uvar*) ->] ,[] ,[]) (values)]
          [(begin ,[] ... ,[]) (values)]
	  [(mset! ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->]) (values)]
          [(set! ,var ,[(Value label* uvar*) ->])
           (unless (memq var uvar*)
             (error who "assignment to unbound var ~s" var))
           (values)]
          [(,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->] ...) (values)]
          [,ef (error who "invalid Effect ~s" ef)]))))
  ;; check the validity of Predicate part of grammer
  ;; It process (bool), if, begin, relop statements and report if they have any invalid syntax
  ;; as per the constraints defined in the grammer 
  (define Pred
    (lambda (label* uvar*)
      (lambda (pr)
        (match pr
          [(true) (values)]
          [(false) (values)]
          [(if ,[] ,[] ,[]) (values)]
          [(begin ,[(Effect label* uvar*) ->] ... ,[]) (values)]
          [(,relop ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->])
           (guard (memq relop relops))
           (values)]
          [,pr (error who "invalid Pred ~s" pr)]))))
  ;; check the validity of Tail part of grammer
  ;; It process if, begin, mref, alloc, binop statements and report if they have any invalid syntax
  ;; as per the constraints defined in the grammer 
  (define Tail
    (lambda (label* uvar*)
      (lambda (tail)
        (match tail
          [(if ,[(Pred label* uvar*) ->] ,[] ,[]) (values)]
          [(begin ,[(Effect label* uvar*) ->] ... ,[]) (values)]
	  [(mref ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->]) (values)]
	  [(alloc ,[(Value label* uvar*) ->]) (values)]
          [(sra ,[(Value label* uvar*) ->] ,y)
           (unless (uint6? y)
             (error who "invalid sra operand ~s" y))
           (values)]
          [(,binop ,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->])
           (guard (memq binop binops))
           (values)]
          [(,[(Value label* uvar*) ->] ,[(Value label* uvar*) ->] ...) (values)]
          [,[(Triv label* uvar*) ->] (values)]))))
  ;; check the validity of Body part of grammer
  (define Body
    (lambda (label* fml*)
      (lambda (x)
        (match x
          [(locals (,local* ...) ,tail)
           (let ([uvar* `(,fml* ... ,local* ...)])
             (verify-x-list uvar* uvar? 'uvar)
             ((Tail label* uvar*) tail)
             (values))]
          [,x (error who "invalid Body ~s" x)]))))
  (define Lambda
    (lambda (label*)
      (lambda (x)
        (match x
          [(lambda (,fml* ...) ,[(Body label* fml*) ->]) (values)]
          [,x (error who "invalid Lambda ~a" x)]))))
  (lambda (x)
    (match x
      [(letrec ([,label* ,[(Lambda label*) ->]] ...) ,[(Body label* '()) ->])
       (verify-x-list label* label? 'label)]
      [,x (error who "invalid Program ~s" x)])
    x))

)
