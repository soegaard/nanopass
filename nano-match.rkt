#lang racket
(require (for-syntax "pattern-rewriting.rkt")
         (for-syntax syntax/parse))
(module+ test (require rackunit))
; (pattern->match-pattern pattern literal? datum? keyword?)

(begin-for-syntax
  (define (literal? x) #f)
  (define (datum? x)   (or (number? x) (string? x) (char? x) (void? x) (null? x)))
  #;(define (keyword? x) (and (syntax? x) (identifier? x) (free-identifier=? x #'foo))))

; nano-match : syntax syntax -> environment
;   the environment is an assocation list from identifiers to matched subforms
(define-syntax (nano-match stx)
  (syntax-parse stx
    [(_ (keyword ...) input [pattern template] ...)
     (define (keyword? x)
       (and (identifier? x) 
            (for/first ([k (syntax->list #'(keyword ...))])
              (free-identifier=? x k))))            
     (define (rewrite pattern) 
       (define-values (mpat pvars) (pattern->match-pattern pattern literal? datum? keyword?))
       mpat)
     (define match-patterns (map rewrite (syntax->list #'(pattern ...))))
     (with-syntax ([(pat ...) match-patterns])
       (syntax/loc stx 
         (match input
           [pat template]
           ...)))]))

(module+ test
  (struct foo (bar))
  (check-equal? (nano-match () 1 [2 3] [1 4]) 4)
  (check-equal? (nano-match () '((a 1) (b 2) (c 3)) [((x v) ...) (list x v)]) '((a b c) (1 2 3)))
  (check-equal? (nano-match (foo) (foo 1) [(foo x) x]) 1)
  (check-equal? (nano-match (foo) (list (foo 1) (foo 2) (foo 3)) [((foo x) ...) x]) '(1 2 3)))