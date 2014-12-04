#lang racket
(require (for-syntax syntax/parse syntax/id-table))

; (x* ...)     = (,@x*)
; ((x* 1) ...) = (,@(map (λ(x) `(,x 1)) x*))

(begin-for-syntax
  (require (for-syntax racket/base))
  (define-syntax (with-lifts stx)
    (syntax-case stx ()
      [(_ (id ...) clauses expr ...)
       (syntax/loc stx (with-syntax ([id id] ...) (with-syntax clauses expr ...)))])))

(define-syntax (qq stx)
  (define (displayln* x) (displayln x) x)
  (define pattern-variables (make-free-id-table))
  (define (var? x) (free-id-table-ref pattern-variables x #f))
  (define-syntax-class dots (pattern (~literal ...)))
  (define msg1 "no pattern variables found - expected due to ellipsis")
  (define msg2 
    "pattern variables at the same ellipsis depth must be bound to lists of the same length")
  (define (qq0 stx)
    (syntax-parse stx
      [()              (syntax/loc stx '())]
      [(s d:dots . sn) (define-values (expr vars) (qq1 #'s))
                       (when (null? vars) (raise-syntax-error 'qq0 msg1  #'s))
                       (with-lifts (vars expr msg2) 
                         ([exprn (qq0 #'sn)])
                         (syntax/loc stx 
                           (let ()
                             (define xss (list . vars))
                             (unless (null? (cdr xss))
                               (unless (apply = (map (λ(xs) (and (list? xs) (length xs))) xss))
                                 (raise-syntax-error 'qq msg2 #'s)))
                             (append (map (λ vars expr) . vars)
                                     exprn))))]
      [(s d:dots)      (define-values (expr vars) (qq1 #'s))
                       (when (null? vars) (raise-syntax-error 'qq0 msg1  #'s))
                       (with-syntax ([vars vars] [expr expr])
                         (syntax/loc stx (map (λ vars expr) . vars)))]
      
      [(a . d)    (quasisyntax/loc stx (cons #,(qq0 #'a) #,(qq0 #'d)))]
      [x:id       (if (var? #'x)
                      (syntax/loc stx x)
                      (syntax/loc stx 'x))]
      [_          stx]))
  (define (qq1 stx)
    (displayln (list 'qq1-in stx))
    (define seen (make-free-id-table))
    (define (seen! x) (displayln (list 'saw: x)) (free-id-table-set! seen x #t))
    (define (vars-seen) (free-id-table-map seen (λ (x _) x)))
    (define (r stx)
      (syntax-parse stx
        [()      (syntax/loc stx '())]
        [(a . d) (quasisyntax/loc stx (cons #,(r #'a) #,(r #'d)))]
        [x:id    (if (var? #'x) 
                     (begin (seen! #'x) #'x)
                     (syntax/loc stx 'x))]
        [_       stx]))
    (values (r stx) (displayln* (vars-seen))))
  
  (syntax-parse stx
    [(_ (~and vars (var ...)) s-exp)
     (for ([v (in-list (syntax->list #'vars))])
       (free-id-table-set! pattern-variables v #t))
     (qq0 #'s-exp)]))

(expand #'(qq () (1 x)))

(define x 42)

(module+ test (require rackunit)
  (check-equal? (list (qq () 1) (qq () x) (qq () (1 x)) (qq () (1 x (2 x))))
                '(           1         x         (1 x)         (1 x (2 x))))
  (check-equal? (let ([x '(x1 x2)]) (qq (x) (x ...))) '(x1 x2))
  (check-equal? (let ([x '(x1 x2)] [y '(y1 y2)]) (qq (x)   ((x 1 y) ...)))  '((x1 1 y)  (x2 1 y)))
  (check-equal? (let ([x '(x1 x2)] [y '(y1 y2)]) (qq (x y) ((x 1 y1) ...))) '((x1 1 y1) (x2 1 y1))))

