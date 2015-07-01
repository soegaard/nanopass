#lang racket
(require "nanopass.rkt")

;;; TUTORIAL PART 1

;;; Nanopass is a framework that makes it easy to construct 
;;; compilers with many passes.

;;; Given a grammar for a language, Nanopass will define
;;; structures that can represent a parsed program.
;;; Nanopass also provides support for defining transformations
;;; from one intermediate language to another.

;;; In this first part of the tutorial, we will see how 
;;; a language is defined with define-language and how
;;; parsing and unparsing to and from s-expressions work.

;;; As an example, let's consider a simple source language, Lsrc.
;;; This is an example of a program:
;;;     (call + 1 (call * 2 3))
;;; Numbers are the only datums.
;;; Applications are restricted to applications of the primitives +,-,*,/.

;;; The grammar of Ltut1 is:

;;;  Expr ::= d                   ; where d        is a datum       (i.e. a number)
;;;       ::= (call pr e1 e2)     ; where pr       is a primitive   (call is the symbol call)
;;;                               ;   and e1, e2 are an Expr

;;; The grammar makes use of two types of terminals `primitive` and `datum`.
;;; For each terminal we need to define a predicate that recognizes
;;; terminal values. The predicates have the same name as the literal with
;;; followed by a question mark.

(define (datum? x)  
  (number? x))                  ; The only datums are numbers.

(define (primitive? x) 
  (and (symbol? x)              ; identifiers are represented as symbols
       (member x '(+ - * /))    ; the available primitives
       #t))

;;; The language Ltut1 can now be defined.

(define-language Ltut1               ; Ltut1 is the name of the language
  (entry Expr)                       ; A program is an Expr
  (terminals                         ; There are two types of terminals:
   (datum     (d))                   ;   datums      begin with d
   (primitive (pr)))                 ;   primitives  begin with pr
  ;                                  ; There is only one non-terminal:
  (Expr (e)                          ;   Expr        begin with e
        ;                            ;   which has two productions
        d                            ;     a single datum
        (call pr e1 e2)))            ;     application of a primitive to two arguments

; The definition (define-language Ltut1 ...) will define:
;   1. Each non-terminals is represented as a struct.
;      The non-terminal that starts with the keyword call is represented as:
;       (struct Ltut1:Expr:call (pr e1 e2))
;   2. Ltut1-parse    which parses an s-expression to the structure representation
;   3. Ltut1-unparse  which converts the structure representation back to s-expressions.

; Example:
;   Let's parse an s-expression and see what the structure representation look like:

    (Ltut1-parse  '(call + 41 42))  ; '#s(Ltut1:Expr:call + 41 42)


;   Unparse it to get a value that prints nicely.

    (Ltut1-unparse 
      (Ltut1-parse '(call + 41 42))) ; '(call + 41 42)

