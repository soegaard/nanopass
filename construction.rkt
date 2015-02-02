#lang racket
; TODO:  (let ([x '(1 2 3)]) (construct  (z 1 x ...)))
; Works: (let ([x '(1 2 3)]) (construct- (z 1 (... (x) x))))
; Something makes construct- not recognized ... when constructed from construct.
(require racket/stxparam (for-syntax syntax/parse syntax/id-table))

;;; Construction
;;;   construct is to construction as match is to deconstruction
;;;   For datums and unbound identifiers, construct works like quote.

;; Datums
; (construct 1)             => 1

; For x unbound in the construction environment:
;    (construct x)             => 'x
;    (construct (x . d))       => (cons (construct x) (construct d))

;; For x bound to construction transformer t in the construction environment
;    (construct x)             => (t x)
;    (construct (x a ...))     => (t x (list (construct a) ...)))

;; For x bound to v a non-transformer value in the construction environment
;    (construct x)             => x
;    (construct ((x ...) . d)  => (list* (construct x) ... d)

;;; During expansion a compile time environment is need to keep
;;; track of which identifiers are bound as variables and catas.
(define-syntax-parameter env    (make-immutable-free-id-table))
(begin-for-syntax (struct expansion-cata (id) #:transparent))
(struct construction-transformer (transform))
(struct construction-cata        (cata))

; If (r x) = 'variable  
; then x is a variable, which means x is evaluated at runtime.
;    If x evaluates to (construction-transformer t), 
;    then (construct (x v ...)) will insert evaluate (t v ...) and insert the result in the output.
;    If x evaluates to a value v, then the value v is inserted in the output.
; If (r x) = (expansion-cata f) 
; then (f x) is inserted in the output.

; syntax (with-variables (id ...) body ...)
;    bind id ... as variables in the construction environment, then evaluate body ...
;    Example:   > (let ([x 42]) (with-variables (x) (construct (1 x y))))
;               '(1 42 y)
(define-syntax (with-variables stx)
  (syntax-parse stx
    [(_ (id:id ...) body ...)
     (define new-env
       (for/fold ([r (syntax-parameter-value #'env)]) ([id (syntax->list #'(id ...))])
         (if (free-id-table-ref r id #f)
             r ; don't override an existing binding
             (free-id-table-set r id 'variable))))
     #`(syntax-parameterize ([env #,new-env])
                            body ...)]
    [_ (raise-syntax-error 'with-variables "expected (with-variables (id ...) body ...)" stx)]))

; syntax (with-catas (id ...) f body ...)
;   Bind id ... as cata variables.
;   If id is referenced inside a (construct ...), then (f id) is inserted.
;   Example: > (let ([x 16]) (with-catas (x) sqrt (construct (9 x))))
;            '(9 4)
(define-syntax (with-catas stx)
  (syntax-parse stx
    [(_ (id:id ...) f body ...)
     (define new-env
       (for/fold ([r (syntax-parameter-value #'env)]) ([id (syntax->list #'(id ...))])
         (free-id-table-set r id (expansion-cata #'f))))
     #`(syntax-parameterize ([env #,new-env])
                            body ...)]))

; syntax (with-catas* ([c f] ...) body ...)
;   Bind the c ... as cata variables, the corresponding catamorphism is f.
(define-syntax (with-catas* stx)
  (syntax-parse stx
    [(_ () body ...)                     #'(let () body ...)]
    [(_  ([c0 f0] [c f] ...) body ...)   #'(with-catas (c0) f0
                                             (with-catas* ([c f] ...)
                                               body ...))]))

(begin-for-syntax 
  ;; References to variables in the construction environment
  (define (ref id) (free-id-table-ref (syntax-parameter-value #'env) id #f))
  (define (bound? id)    (ref id))
  (define (unbound? id)  (not (bound? id)))
  (define (variable? id) (eq? (ref id) 'variable))
  (define (cata? id) (expansion-cata? (ref id)))
  
  ;; Syntax classes for the various variable types
  (define-syntax-class variable
    #:description "identifier bound in the construction environment"
    (pattern var:id
             #:fail-unless (variable? #'var) 
             "identifier bound in the construction environment expected"))
  
  (define-syntax-class unbound
    #:description "an identifier not bound in the construction environment"
    (pattern var:id
             #:fail-unless (unbound? #'var)
             "an identifier not bound in the construction environment expected"))
  
  (define-syntax-class cata
    #:description "identifier bound to catamorphism in the construction environment"
    #:attributes (f)
    (pattern var:id
             #:fail-unless (cata? #'var) 
             "identifier bound to catamorphism in the construction environment expected"
             #:attr f (cata? #'var)))
  
  #;(define-syntax-class ooo
      #:description "literal ..."
      (pattern (~literal ...)))
  
  #;(define-syntax-class non-ooo
    #:description "not literal ..."
    (pattern (~not (~datum ...)))))  ; todo ~literal


;; Debug flag, if #t then construct will display useful info during expansion.
(begin-for-syntax (define flag #f) (set! flag #f))

(module reverse-syntax racket
  (provide reverse-syntax)
  (require racket/match)
  (define (reverse-syntax stx)
    ;(displayln (list 'reverse-syntax stx))
    (define loc (if (syntax? stx) stx #f))
    (define r reverse-syntax)
    (define as (if (syntax? stx) (syntax->list stx) stx))
    (if (list? as) 
        (datum->syntax loc (reverse (map r as)))
        (let ()
          (match (if (syntax? stx) (syntax-e stx) stx)
            [(cons a d) (datum->syntax loc (cons (r d) (r a)))]
            [_          stx])))))

(require (for-syntax (submod "." reverse-syntax)))

(module+ test
  (require (submod ".." reverse-syntax))
  (define sd syntax->datum)
  (check-equal? (sd (reverse-syntax #'1)) 1)
  (check-equal? (sd (reverse-syntax #'(1 2 3))) '(3 2 1))
  (check-equal? (sd (reverse-syntax #'(3 . 4))) '(4 . 3))
  (check-equal? (sd (reverse-syntax #'(3 . (4 . 5)))) '((5 . 4) . 3)))

(module rewrite-ellipsis racket/base
  (provide rewrite-ellipsis)
  (require syntax/parse racket/list racket/match)
  ; rewrite-ellipsis : syntax -> syntax
  ;   input is in postfix form
  ;   a ...      ->  (... a)
  ;   a ... ...  ->  (... (... a))
  (define-syntax-class non-ooo
    #:description "not literal ..."
    (pattern (~not (~datum ...))))  ; <== todo ~literal
  (define (rewrite-ellipsis stx)
    ;(displayln (list 're-in stx))
    (with-syntax ([dots (datum->syntax stx '...)])
      (define (dots? x) (and (identifier? x) 
                             ; (eq? (syntax-e x) '...)
                             (free-identifier=? x #'dots)))
      (define (r stx)
        ;(displayln stx)
        (syntax-parse stx
          [(a:non-ooo . d)
           #`(#,(r #'a) . #,(r #'d))]
          [(a ...)
           (displayln (list 'rewritting-...!))  ; <= test case
           (define as (syntax->list #'(a ...)))
           (define-values (ds a-more) (splitf-at as dots?))
           (cond
             ; no ellipsis, do nothing
             [(null? ds) stx]
             [else ; at least one ellipsis, wrap around the s-exp after 
              (match a-more
                [(cons a more) ; a is the s-exp to be repeated
                 (define wrapped-a (for/fold ([a (r a)]) ([d ds])
                                     #`(#,a dots)))
                 #`(#,wrapped-a . #,(r more))]
                ['() (displayln stx)
                     (error 'rewrite-ellipsis "no s-expression after ellipsis")])])]
          [(a . d) #`(#,(r #'a) . #,(r #'d))]
          [other   #'other]))
      (define out (r stx))
      ;(displayln (list 're-out out))
      out)))

(module add-ellipsis-variables racket/base
  (provide add-ellipsis-variables)
  (require syntax/parse racket/list racket/match syntax/id-table)
  (define empty-free-id-set (make-immutable-free-id-table))
  (define (list->free-id-set vs)
    (for/fold ([s empty-free-id-set]) ([v vs])
      (free-id-table-set s v #t)))
  (define (free-id-set . vs)
    (list->free-id-set vs))
  (define (free-id-set->list s)
    (free-id-table-map s (λ (k v) k)))
  (define (free-id-set-union vs ws)
    (for/fold ([s ws]) ([v (free-id-set->list vs)])
      (free-id-table-set s v #t)))
  
  (define (add-ellipsis-variables stx)
    ;(displayln (list 'aev stx))
    (define r add-ellipsis-variables)
    (with-syntax ([dots (datum->syntax stx '...)])
      (syntax-parse stx
        [((~literal ...) a)
         (define-values (vars ra) (r #'a))
         (values vars
                 (with-syntax ([vars (free-id-set->list vars)])
                   (quasisyntax/loc stx (dots vars #,ra))))]
        [x:id
         (values (free-id-set #'x) #'x)]
        [(a . d) 
         (define-values (avars ra) (r #'a))
         (define-values (dvars rd) (r #'d))
         (values (free-id-set-union avars dvars)
                 (quasisyntax/loc stx (#,ra . #,rd)))]
        [_ 
         (values empty-free-id-set stx)]))))

(require (submod "." add-ellipsis-variables))

(require (submod "." rewrite-ellipsis))
(module+ test 
  (require (submod ".." rewrite-ellipsis))
  (define (r stx) (reverse-syntax (rewrite-ellipsis (reverse-syntax stx))))
  (provide r)
  (with-syntax ([ooo #'(... ...)])
    (check-equal? (sd (r #'(1 2 3)))                         '(1 2 3))
    (check-equal? (sd (r #'(1 x ooo 2)))               '(1 (... x) 2))
    (check-equal? (sd (r #'(1 x (... ...) (... ...) 2)))     '(1 (... (... x)) 2))
    (check-equal? (sd (r #'(1 2 (3 x (... ...)) (... ...)))) '(1 2 (... (3 (... x)))))))

(require (for-syntax (submod "." rewrite-ellipsis)
                     (submod "." add-ellipsis-variables)
                     (submod "." reverse-syntax)))

#;(define-syntax (construct stx)
  (syntax-parse stx
    [(_ . more)
     ;(displayln (list 'in: stx #'more))
     (define tmp (reverse-syntax
                  (rewrite-ellipsis
                   (reverse-syntax 
                    #'more))))
     ; (displayln (list 'tmp: tmp))
     (define-values (_ more-)
       (add-ellipsis-variables tmp))
     (displayln more-)
     (define out
       (with-syntax ([more- more-]
                     [construct- (datum->syntax stx 'construct-)])
         (syntax/loc stx (construct- . more-))))
     (displayln (list 'out: out))
     out]))

#;(define-syntax (construct stx)
  (syntax-parse stx
    [(_ . more)
     #'(construct- . more)]))

(define-syntax (construct stx)
  (syntax-parse stx
    [(_ . more)
     #`(construct- . #,(reverse-syntax
                        (reverse-syntax
                         #'more)))]))

;; syntax (construct s-exp)
;;   construct a value according to the s-exp template
(define-syntax (construct- stx)
  (when flag 
    (displayln stx)
    (displayln (free-id-table-map (syntax-parameter-value #'env) list)))
  (syntax-parse stx
    [(_ x:number)                      #'x]
    ; [(_ (~literal ...))                (raise-syntax-error 'construct "illegal use of ... ~a" stx)]
    [(_ x:unbound)                     #''x]
    [(_ x:cata)                        (with-syntax ([f (expansion-cata-id (ref #'x))])
                                         #'(f x))]
    [(_ x:variable)                    (syntax/loc #'x
                                         (match x
                                           [(construction-transformer t) (t)]
                                           [(construction-cata c)        (c)]
                                           [_                             x]))]
    [(_ (x:cata ((~literal ...) {bv ...} a*) . d)) ; <= TODO: find test case / is this case needed
     #'(cons (construct- x) (construct- (((... ...) {bv ...} a*) . d)))]
    [(_ (x:cata d ...))                #'(cons (construct- x) (construct- (d ...)))]
    [(_ (x:variable d ...))            #'(let ([vds (construct- (d ...))])
                                           (match x
                                             [(construction-transformer t) (apply t vds)]
                                             [_                            (cons x vds)]))]
    [(_ (((~literal ...) {bv ...} a*) . d)) ; <= TODO XXX ought to be (~literal ...)
     (with-syntax ([(u ...) (filter unbound? (syntax->list #'(bv ...)))]
                   [(c ...) (filter cata?    (syntax->list #'(bv ...)))])
       (with-syntax ([(f ...) (map (λ (v) (expansion-cata-id (ref v)))
                                   (syntax->list #'(c ...)))])
         #'(append (append-map (λ (bv ...)
                                 (with-variables (bv ...)
                                   (with-catas*  ([c f] ...)
                                     (construct- (a*)))))
                               bv ...)
                   (construct- d))))]
    ; [(_ ((~literal ...) . _))          (raise-syntax-error 'construct "illegal use of ..." stx)]
    [(_ (a . d))                       #'(cons (construct- a) (construct- d))]
    [(_ ())                            #''()]
    [(_ #:catas {c ...} f . more)      #'(with-catas (c ...) f (construct- . more))]
    [(_ {v ...} . more)                #'(with-variables {v ...} (construct- . more))]
    
    [(_ datum)                         #'datum]
    [_ (displayln stx)
       (error 'construct "got ~a" stx)]))



(module+ test (require rackunit)
  (struct foo (bar) #:transparent)
  (check-equal? (construct 1) 1)
  (check-equal? (construct x) 'x)
  (check-equal? (construct y) 'y)
  (check-equal? (let ([x 42])
                  (with-variables (x)
                    (construct 42)))
                42)
  (check-equal? (let ([x (construction-transformer (λ v (cons 'x: v)))])
                  (with-variables (x)
                    (construct x)))
                '(x:))
  (check-equal? (let ([Foo (construction-transformer (λ v (apply foo v)))])
                  (with-variables (Foo)
                    (construct (Foo 42))))
                (foo 42))
  (check-equal? (let ([Foo (construction-transformer (λ v (apply foo v)))])
                  (with-variables (Foo)
                    (construct (foo (Foo foo)))))
                `(foo, (foo 'foo)))
  (check-equal? (let ([a '(1 2 3)])
                  (with-variables (a)
                    (construct (x (... {a} a) y))))            ; read as  x a ... y
                '(x 1 2 3 y))
  (check-equal? (let ([a '(1 2 3)])
                  (with-variables (a)
                    (construct (x (... {a} (y a)) z))))        ; read as  x (y a) ... z
                '(x (y 1) (y 2) (y 3) z))
  (check-equal? (let ([a '((1 2 3) (x y z))])  
                  (with-variables (a)
                    (construct (x (... {a} (... {a} a)) z))))  ; read as  x a ... ... y
                '(x 1 2 3 x y z z))
  (check-equal? (let ([a '((1 2 3) (x y z))] [b '(11 12)])
                  (with-variables (a)
                    (construct (x (... {a b} (b (... {a} a))) z)))) ; reads as x (b a ...) ... z
                '(x (11 1 2 3) (12 x y z) z))
  (check-equal? (let ([a '(((1 2 3) (4 5 6)) ((11 12 13) (14 15 16)))])
                  (construct {a}
                             ((... {a} (... {a} (... {a} a))))))
                '(1 2 3 4 5 6 11 12 13 14 15 16))
  (check-equal? (let ([a '((1 2 3) (x y z))] [b '(11 12)])
                  (with-variables (a b)
                    (construct 
                     (x (... {a b} (b (... {a} a))) z))))
                '(x (11 1 2 3) (12 x y z) z))
  (check-equal? (let ([x 16])
                  (with-variables (x)
                    (with-catas (x) sqrt
                      (with-variables (x)
                        (construct {x} (1 x))))))
                '(1 4))
  (check-equal? (let ([a '(1 4 9 16)])
                  (with-catas (a) sqrt
                    (construct ((... {a} a)))))
                '(1 2 3 4)))


(module+ test
  (define (simplify s-exp)
    ; (displayln s-exp)
    (match s-exp
      [(? symbol? x)                          x]
      [(list)                                 '()]
      [(? number? n)                          n]
      ; 
      [(list 'quote d)                        (construct {d} d)]
      [(list 'if e0 e1)                       (construct #:catas {e0 e1} simplify
                                                         (if e0 e1 (void)))]
      [(list 'if e0 e1 e2)                    (construct #:catas {e0 e1 e2} simplify
                                                         (if e0 e1 e2))]
      [(list 'begin e* ... en)                (construct #:catas {e* en} simplify
                                                         (begin (... {e*} e*) en))]
      [(list 'lambda (list x* ...) 
             body* ... body)                  (construct {x*} #:catas {body* body} simplify
                                                         (lambda ((... {x*} x*)) 
                                                           (begin (... {body*} body*) body)))]
      [(list 'letrec (list (list x* e*) ...)
             body* ... body)                  (construct {x*} #:catas {e* body* body} simplify
                                                         (letrec ((... {x* e*} [x* e*]))
                                                           (begin (... {body*} body*) body)))]
      [(list e e* ...)                        (construct #:catas {e e*} simplify
                                                         (e e* ...))]
      
      [_ (error 'simplify "got ~a" s-exp)]))
  
  (check-equal? (simplify '(if 1 (letrec ([x (if 2 3)]) 4 5)))
                '(if 1 (letrec ((x (if 2 3 (void)))) (begin 4 5)) (void)))
  (check-equal? (simplify '(if (if 1 2 (if 3 4)) (if 5 6)))
                '(if (if 1 2 (if 3 4 (void))) (if 5 6 (void)) (void))))

; (require (submod "." test))