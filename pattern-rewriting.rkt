#lang racket
;;; The main export of this module is 
;;;     pattern->match-pattern
;;; which rewrite a nanopass pattern into a match pattern.
;;; I.e. it rewrites a nanopass pattern into a pattern that can
;;; be used with the standard Racket match construct. This
;;; way we avoid implementing a pattern matcher ourselves.

;;; Besides returning the rewritten pattern it also returns
;;; a list of pattern variables occuring in the pattern.
;;; Pattern variables are represented a struct
;;;    (struct pattern-variable (id n))
;;; The n indicates the ellipsis depth.
;;; In the pattern (x y ... (z ...) ...) the pattern variables x, y, and, z
;;; have dephts 0, 1, and, 2 respectively.
;;; Note:   x ... ... is an incorrect pattern.

(require racket/contract)
(provide pattern->match-pattern
         (struct-out ellipsis)          ; (ellipsis pat) represents pat ...
         (struct-out pattern-variable)  ; (pattern-variable id n) where n is the ellipsis depth
         (contract-out [dots? (-> any/c boolean?)])) ; predicate for the identifier ...

(module+ test (require rackunit))


;;;
;;; STRUCTS
;;;

(struct pattern-variable (id depth) #:transparent)
(struct ellipsis         (pat)      #:transparent)

; The ellipsis is used rewrite postfix ... to prefix notation.
; That makes the processing in pattern->match-pattern easier.

(define make-ellipsis ellipsis) ; an alternative binding for the ellipsis constructor

;;; HELPERS

(define (dots? x)
  (and (identifier? x)
       (free-identifier=? x #'(... ...))))

(module+ test
  (check-true  (dots? #'(... ...)))
  (check-false (dots? '...)))

; unwrap
;   like syntax->list but also handles dotted pairs
(define (unwrap stx)
  (if (syntax? stx)
      (if (identifier? stx)
          stx
          (let ([unwrapped (syntax-e stx)])
            (cond 
              [(pair? unwrapped) (cons (car unwrapped) (unwrap (cdr unwrapped)))]
              [else unwrapped])))
      stx))

; introduce-prefix-ellipsis : syntax -> syntax
;     rewrite   pat ...  into  (... pat)
(define (introduce-prefix-ellipsis pattern [ellipsis ellipsis])
  ; the ellipsis constructor is optional (useful for testing)
  (define (i p) (introduce-prefix-ellipsis p ellipsis))
  (define (wrap-in-ellipsis pat n)
    (match n
      [0 pat]
      [1 (ellipsis pat)]
      [_ (raise-syntax-error 'rewrite "two ellipses in a row is not allowed, got: ~a" pat)]))
  (match (unwrap pattern)
    [(list-rest pat (? dots? dots) ... more)
     #`(#,(wrap-in-ellipsis (i pat) (length dots)) . #,(i more))]
    [(cons pat more)
     #`(pat . #,(i more))]
    [pat pat]))

(module+ test
  (define (test-ellipsis x) (list 'ellipsis x))
  (define (test-ellipsis? x) (match x [(list 'ellipsis _) #t] [_ #f]))
  (define (->datum x) 
    (define r ->datum)
    (match x
      [(? syntax? x)        (r (syntax-e x))]
      [(? test-ellipsis? p) (test-ellipsis (r p))]
      [(cons a d)           (cons (r a) (r d))]
      [else x]))
  (with-syntax ([dots #'(... ...)])
    (let () 
      (define (test pat) (->datum (introduce-prefix-ellipsis pat test-ellipsis)))
      (check-equal? (map test (list #'1 #'x #'(1 2) #'(1 x)))  '(1 x (1 2) (1 x)))
      (check-equal? (test #'(x dots))               '((ellipsis x)))
      (check-equal? (test #'(x dots y))             '((ellipsis x) y))
      (check-equal? (test #'(x dots y dots))        '((ellipsis x) (ellipsis y)))
      (check-equal? (test #'((x dots) dots y dots)) '((ellipsis ((ellipsis x))) (ellipsis y)))
      (check-equal? (test #'((x 1) dots))           '((ellipsis (x 1)))))))

; reintroduce-postfix-ellipsis : syntax -> syntax
;   rewrite (ellipsis pat)  to  pat ...
;   here (ellipsis pat) is an instance of the ellipsis struct 
(define (reintroduce-postfix-ellipsis p)
  (define (r* p*) (map r p*))
  (define (r p)
    (with-syntax ([dots #'(... ...)])
      (match (unwrap p)
        [(ellipsis pat) (append (r pat) (list #'dots))]
        [(list p* ...)  (list (append-map r p*))]
        [(cons a d)     (list (cons (first (r a)) (first (r d))))]
        [pat            (list pat)])))
  (first (r p)))

(module+ test
  (with-syntax ([dots #'(... ...)])
    (let () 
      (define (test pat) (->datum (reintroduce-postfix-ellipsis pat)))
      (check-equal? (map test '(1 x (1 2) (1 x)))  (list '1 'x '(1 2) '(1 x)))
      (check-equal? (test (list (ellipsis 'x)))                          '(x ...))
      (check-equal? (test (list (ellipsis 'x) 'y))                       '(x ... y))
      (check-equal? (test (list (ellipsis 'x) (ellipsis 'y)))            '(x ... y ...))
      (check-equal? (test (list (ellipsis (ellipsis 'x)) (ellipsis 'y))) '(x ... ... y ...))
      (check-equal? (test (list (ellipsis (list 'x '1))))                '((x 1) ...))
      (check-equal? (test (cons 1 2))                                    '(1 . 2)))))

; pattern->match-pattern : syntax predicate predicate predicate -> syntax assoc
;     rewrite a nonpass pattern into a match pattern
;     in this context a keyword is an identifier (the name of a struct)
;     Two values are returned:
;         the rewritten pattern
;         an assocation list from pattern variables to their ellipsis depths
(define (pattern->match-pattern pattern literal? datum? keyword?)
  (define pvars '())   ; pattern variables detected in pattern
  (define (add-pattern-var! v n) (set! pvars (cons (pattern-variable v n) pvars)))
  (define (r* is n) (map (λ(i) (r i n)) is))
  (define (r input [n 0])  ; n = ellipsis depth 
    (match (unwrap input)
      [(and (? identifier? x) 
            (? literal?))           #`(? (λ (y) (free-identifier=? #,x y)))]
      [(? identifier? x)            (add-pattern-var! x n) 
                                    x]
      [(list (? keyword? k) p* ...) #`(#,k  #,@(r* p* n))]
      [(list p* ...)                #`(list #,@(r* p* n))]
      [(cons a d)                   #`(cons #,(r a n) #,(r d n))]
      ['()                          #''()]
      [(? datum? d)                 d]
      [(ellipsis pat)               (ellipsis (r pat (+ n 1)))]
      [p                            (error 'here "got: ~a" p)]))
  (values 
   (datum->syntax #'here (reintroduce-postfix-ellipsis (r (introduce-prefix-ellipsis pattern))))
   pvars))

(module+ test
  (let ()
    (define (literal? x) #f)
    (define (datum? x)   (or (number? x) (string? x) (char? x) (void? x) (null? x)))
    (struct foo (bar baz) #:transparent)
    (define (keyword? x) (and (identifier? x) (free-identifier=? x #'foo)))
    (define (test x) 
      (define-values (mp pvars) (pattern->match-pattern x literal? datum? keyword?))
      (->datum mp))
    (with-syntax ([dots #'(... ...)])
      (check-equal? (test #'1)                    1)
      (check-equal? (test #'x)                    'x)
      (check-equal? (test #'(x 1))                '(list x 1))
      (check-equal? (test #'(x . 1))              '(cons x 1))
      (check-equal? (test #'(x dots 1))           '(list x ... 1))
      (check-equal? (test #'((x 1) dots 2))       '(list (list x 1) ... 2))
      (check-equal? (test #'((x dots) dots))      '(list (list x ...) ...))
      (check-equal? (test #'(λ (x* dots) b dots)) '(list λ (list x* ...) b ... ))      
      (check-equal? (test #'(let ([x* e*] dots) b* dots b)) 
                    '(list let (list (list x* e*) ...) b* ... b))
      (check-equal? (test #'(foo 1 2))            '(foo 1 2))
      (check-equal? (test #'(bar 1 2))            '(list bar 1 2))
      (check-equal? (test #'(mlet (([x e] dots) dots) body))
                    '(list mlet (list (list (list x e) ...) ...) body)))))

; syntax-match : syntax syntax -> environment
;   the environment is an assocation list from identifiers to matched subforms
(define (syntax-match pattern input)
  (syntax-parse input ...))
