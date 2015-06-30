#lang racket
(require "nanopass.rkt")

; Nanopass is a framework that makes it easy to construct 
; compilers with many passes.

; As an example, let's consider a source language, Lsrc, 
; with primitives +,-,*,/ :
(define (primitive? x) (and (symbol? x) (member x '(+ - * /)) #t))

; The only datums are numbers.
(define (datum? x)     (number? x))

; The grammar is:

;  Expr ::= d              ; where d        is a Datum       (i.e. a number)
;       ::= (pr e1 e2)     ; where pr       is a Primitive 
;                          ;   and e1, e2 are an Expr
;

(define-language L                ; Lsrc is the name of the language
  (entry Expr)                       ; A program is an Expr
  (terminals                         ; There are two types of terminals:
   (datum     (d))                   ;   datums      begin with d
   (primitive (pr)))                 ;   primitives  begin with pr
  ;                                  ; There is only one non-terminal:
  (Expr (e)                          ;   Expr        begin with e
        ;                            ;   which has two productions
        d                            ;     a single datum
        (call pr e1 e2)))            ;     application of a primitive to two arguments

; The definition (define-language LSrc ...) will define:
;   1. Each non-terminals is represented as a struct.
;      The non-terminal that starts with the keyword call is represented as:
;       (struct Lsrc:Expr:call (pr e1 e2))
;   2. L-parse    which parses an s-expression to the structure representation
;   3. L-unparse  which converts the structure representation back to s-expressions.

; Example:
(L-parse  '(call + 41 42))  ; '#s(L:Expr:call + 41 42)
(L-unparse 
 (L-parse '(call + 41 42))) ; '(call + 41 42)

