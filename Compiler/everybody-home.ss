#|
Program name    : everybody-home.ss
Functions       : everybody-home
Description     : This program is used to iterate the passes from select-instructions to finalize-frame-locations
                  if it finds incomplete body statements otherwise it continues with discard-call-live pass after 
                  assign-registers.
Input Language  : Scheme
Output Language : Scheme
|#

(library (Compiler everybody-home)
  (export everybody-home?)
  (import
    ;; Load Chez Scheme primitives
    (chezscheme)
    ;; Load provided compiler framework
    (Framework match)
    (Framework helpers))

;; Code to iterate the intermediate passes
(define-who everybody-home?
  (define all-home?
    (lambda (body)
      (match body
        [(locals (,local* ...)
           (ulocals (,ulocal* ...)
             (spills (,spill* ...)
               (locate (,home* ...)
                 (frame-conflict ,ct ,tail))))) #f]
        [(locate (,home* ...) ,tail) #t]
        [,x (error who "invalid Body ~s" x)])))
  (lambda (x)
    (match x
       [(letrec ([,label* (lambda () ,body*)] ...) ,body)
        (andmap all-home? `(,body ,body* ...))]
       [,x (error who "invalid Program ~s" x)])))
)
