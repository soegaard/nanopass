#lang racket
(provide qq)

;;; syntax (qq (var ...) template)
;;;   qq is an "extended" quasiquote.
;;;   It constructs a value from template.
;;;   Variables named in (var ...) are automatically unquoted.
;;;   If  var  is bound to a list, one can use var ... in the template.
;;;   Nested as well as sequential occurences of ... in template is supported
;;;   See tests below for examples

(require (for-syntax syntax/parse syntax/id-table))

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
  (define-syntax-class dots     (pattern       (~literal ...)))
  (define-syntax-class non-dots (pattern (~not (~literal ...))))
  (define msg1 "no pattern variables found - expected due to ellipsis")
  (define msg2 
    "pattern variables at the same ellipsis depth must be bound to lists of the same length")
  (define msg3 "... may appear only in proper lists")
  (define msg4 "... must follow an s-expression")
  (define (qq0 tvars stx)
    (syntax-parse stx
      [() (syntax/loc stx '())]
      [((~literal unquote) expr) #'expr]
      ; lists with at least one ellipsis
      [(more ... s:non-dots d:dots ds:dots ... sn:non-dots ...)
       ; The more ... is recursively expanded
       (define more-expr (with-lifts (tvars) () 
                           #'(qq tvars (more ...))))
       ; s is expanded at a level higher (and omit one ...)
       (define levels (make-free-id-table))
       (define-values (s-expr s-vars) (qq1 levels tvars 1 #'(s ds ...)))
       ; (displayln (list 'levels (free-id-table-map levels list)))
       ; (displayln (list #'(s ds ...) s-vars))
       ; at least one variable must be present in s
       (when (null? s-vars) (raise-syntax-error 'qq0 msg1 #'s))
       ; at the end we have sn ... which is a the same level
       (define sn-expr (qq0 #'tvars #'(sn ...)))
       ; the result is: (list* more ... s-expr sn-expr)
       (with-lifts (more-expr s-expr sn-expr s-vars msg2) ()
         (syntax/loc stx 
           (let ([xss (list . s-vars)])
             ; check that variables at the same level are bound
             ; to lists of the same lengths
             (unless (null? (cdr xss))
               (unless (apply = (map (λ(xs) (and (list? xs) (length xs))) xss))
                 (raise-syntax-error 'qq msg2 #'s-expr)))
             ; construct the list from the pieces, mapping over s-vars for s
             (append more-expr
                     (append-map (λ s-vars s-expr) . s-vars)
                     sn-expr))))]
      [(_ . d:dots) (raise-syntax-error 'qq msg3 stx)]
      [(a:dots . _) (raise-syntax-error 'qq msg4 stx)]
      [(a . d)      (quasisyntax/loc stx (cons #,(qq0 tvars #'a) #,(qq0 tvars #'d)))]
      ; identifiers and template variables
      [a:dots       (raise-syntax-error 'qq "bad syntax" #'a)]
      [x:id         (if (var? #'x)
                        (syntax/loc stx x)
                        (syntax/loc stx 'x))]
      [_  stx]))
  (define (qq1 levels tvars level stx)
    ; (displayln (list 'qq1 levels tvars level stx))
    ; keep a table over template variables used in stx,
    ; the maximum depth of each template variable can be used for early error checking
    (define seen (make-free-id-table))
    (define (seen! x) (free-id-table-set! seen x (max level (free-id-table-ref seen x (λ () level)))))
    (define (level! x) 
      (free-id-table-set! levels x (max level (free-id-table-ref levels x (λ () level)))))
    (define (vars-seen) (free-id-table-map seen (λ (x _) x)))
    (define (r stx)
      (syntax-parse stx
        [() (syntax/loc stx '())]
        ; lists with at least one ellipsis
        [(more ... s:non-dots d:dots ds:dots ... sn:non-dots ...)
         ; The more ... is recursively expanded
         (define-values (more-expr more-vars) (qq1 levels tvars level #'(more ...)))
         (for-each seen!  more-vars)
         (for-each level! more-vars)
         ; s is expanded at a level higher (and omit one ...)
         (define-values (s-expr s-vars) (qq1 levels tvars (+ level 1) #'(s ds ...)))
         (for-each seen!  s-vars)
         (for-each level! s-vars)
         ; at least one variable must be present in s
         (when (null? s-vars) (raise-syntax-error 'qq0 msg1 #'s))
         ; at the end we have sn ... which is a the same level
         (define-values (sn-expr sn-vars) (qq1 levels tvars level #'(sn ...)))
         (for-each seen!  sn-vars)
         (for-each level! sn-vars)
         ; the result is: (list* more ... s-expr sn-expr)
         (with-lifts (more-expr s-expr sn-expr s-vars msg2) ()
           (syntax/loc stx 
             (let ([xss (list . s-vars)])
               ; check that variables at the same level are bound
               ; to lists of the same lengths
               (unless (null? (cdr xss))
                 (unless (apply = (map (λ(xs) (and (list? xs) (length xs))) xss))
                   (raise-syntax-error 'qq msg2 #'s-expr)))
               ; construct the list from the pieces, mapping over s-vars for s
               (append more-expr
                       (append-map (λ s-vars s-expr) . s-vars)
                       sn-expr))))]
        [(_ . d:dots) (raise-syntax-error 'qq msg3 stx)]
        [(a:dots . _) (raise-syntax-error 'qq msg4 stx)]
        [(a . d)      (quasisyntax/loc stx (cons #,(r #'a) #,(r #'d)))]
        [a:dots       (error)]
        [x:id         (if (var? #'x) 
                          (begin (seen! #'x) #'x)
                          (syntax/loc stx 'x))]
        [_            stx]))
    (define r-stx (r stx))
    (values r-stx (vars-seen)))
  (syntax-parse stx
    [(_ (~and vars (var ...)) s-exp)
     (for ([v (in-list (syntax->list #'vars))])
       (free-id-table-set! pattern-variables v #t))
     ; (define-values (expr vars) (qq1 #'vars 0 #'s-exp)) expr
     (qq0 #'vars #'s-exp)]
    [(_ vars s-exp more0 more1 ...)
     (raise-syntax-error 
      'qq "expected (qq (<template-variable> ...) s-expression), got an extra s-expression" #'more0)]
    [_ (raise-syntax-error 'qq "expected (qq (<template-variable> ...) s-expression), got Y" stx)]))

(module+ test (require rackunit)
  (check-equal? (list (qq () 1) (qq () x) (qq () (1 x)) (qq () (1 x (2 x))))
                '(           1         x         (1 x)         (1 x (2 x))))
  (check-equal? (let ([x '(x1 x2)]) (qq (x) (x ...))) '(x1 x2))
  (check-equal? (let ([x '(x1 x2)] [y '(y1 y2)]) (qq (x)   ((x 1 y) ...)))  '((x1 1 y)  (x2 1 y)))
  (check-equal? (let ([x '(x1 x2)] [y '(y1 y2)]) (qq (x y) ((x 1 y1) ...))) '((x1 1 y1) (x2 1 y1)))
  (check-equal? (let ([x '(x1 x2)] [y '(y1 y2)]) (qq (x y) (x ... y ...))) '(x1 x2 y1 y2))
  (check-equal? (let ([x '(x1 x2)] [y '(y1 y2)]) (qq (x y) (1 x ... 2 y ...))) '(1 x1 x2 2 y1 y2))
  (check-equal? (let ([x '((x1) (x2 x3) (x4 x5 x6))]) (qq (x y) (x ... ...))) '(x1 x2 x3 x4 x5 x6))
  (check-equal? (let ([x '((x1) (x2 x3) (x4 x5 x6))] [y '(a b c)])
                  (qq (x y) (x ... ... y ...)))
                '(x1 x2 x3 x4 x5 x6 a b c))
  (check-equal? (let ([x '((x1 x2) (x3 x4 x5))] [y '(y1 y2)]) 
                  (qq (x y) ((x ...) ... y ...)))
                '((x1 x2) (x3 x4 x5) y1 y2))
  (check-equal? (let ([x '((x1 x2) (x3 x4 x5))] [y '(y1 y2)]) 
                  (qq (x y) ((x ...) ...)))
                '((x1 x2) (x3 x4 x5))))

