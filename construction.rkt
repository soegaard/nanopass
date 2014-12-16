#lang racket
;;; Current problem: catas are not working for ellipsis varibles

(require (for-syntax syntax/parse
                     syntax/id-table)
         racket/stxparam)

;;; Construction

; construct is to construction as match is to deconstruction

; (construct 1)             => 1
; For x unbound in the construction environment:
; (construct x)             => 'x
; (construct (x . d))       => (cons (construct x) (construct d))
;; For x bound to construction transformer t in the construction environment
; (construct x)             => (t x)
; (construct (x a ...))     => (t x (list (construct a) ...)))
;; For x bound to v a non-transformer value in the construction environment
; (construct x)             => x
; (construct ((x ...) . d)  => (list* (construct x) ... d)

(define-syntax-parameter env    (make-immutable-free-id-table))
(define-syntax-parameter levels (make-immutable-free-id-table))
(define-syntax-parameter level  0)
(struct construction-transformer (transform))
(struct construction-cata        (cata))
(begin-for-syntax
  (struct expansion-cata         (id) #:transparent))

(define-syntax (with-variables stx)
  (syntax-parse stx
    [(_ (id ...) body ...)
     (define new-env
       (for/fold ([r (syntax-parameter-value #'env)]) ([id (syntax->list #'(id ...))])
         (if (free-id-table-ref r id #f)
             r ; don't override an existing binding
             (free-id-table-set r id 'variable))))
     #`(syntax-parameterize ([env #,new-env])
                            body ...)]))

(define-syntax (with-catas stx)
  (syntax-parse stx
    [(_ (id:id ...) f body ...)
     (define new-env
       (for/fold ([r (syntax-parameter-value #'env)]) ([id (syntax->list #'(id ...))])
         (free-id-table-set r id (expansion-cata #'f))))
     #`(syntax-parameterize ([env #,new-env])
                            body ...)]))

(define-syntax (with-catas* stx)
  (syntax-parse stx
    [(_ () body ...)                     #'(let () body ...)]
    [(_  ([c0 f0] [c f] ...) body ...)   #'(with-catas (c0) f0
                                             (with-catas* ([c f] ...)
                                               body ...))]))

(begin-for-syntax  
  (define (ref id) (free-id-table-ref (syntax-parameter-value #'env) id #f))
  (define (bound? id)    (ref id))
  (define (unbound? id)  (not (bound? id)))
  (define (variable? id) (eq? (ref id) 'variable))
  (define (cata? id) (expansion-cata? (ref id)))
  
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
             #:attr f (cata? #'var))))


(begin-for-syntax
  (define flag #f)
  (set! flag #f))
(define-syntax (construct stx)
  (when flag (displayln stx))
  (when flag (displayln (free-id-table-map (syntax-parameter-value #'env) list )))
  (define l  (syntax-parameter-value #'level))
  (define ls (syntax-parameter-value #'levels))
  (syntax-parse stx
    [(_ x:number)                      #'x]
    [(_ x:unbound)                     #''x]
    [(_ x:cata)                        (with-syntax ([f (expansion-cata-id (ref #'x))])
                                         #'(f x))]
    [(_ x:variable)                    #'(match x
                                           [(construction-transformer t) (t)]
                                           [(construction-cata c)        (c)]
                                           [_                             x])]
    [(_ (x:cata     ((~literal ...) {bv ...} a*) . d)) 
     (displayln 'rule1)
     #'(cons (construct x) (construct (((... ...) {bv ...} a*) . d)))]
    [(_ (x:variable ((~literal ...) {bv ...} a*) . d))
     (displayln 'rule2)
     #'(let ([tail         (construct (((... ...) {bv ...} a*) . d))])
         (match x
           [(construction-transformer t) (apply t tail)]
           [_                             x]))]
    [(_ (x:cata d ...))                #'(cons (construct x) (construct (d ...)))]
    [(_ (x:variable d ...))            #'(let ([vds (construct (d ...))])
                                           (match x
                                             [(construction-transformer t) (apply t vds)]
                                             [_                            (cons x vds)]))]
    [(_ (((~literal ...) {bv ...} a*) . d))
     (displayln 'rule3)
     (with-syntax ([(u ...) (filter unbound? (syntax->list #'(bv ...)))]
                   [(c ...) (filter cata?    (syntax->list #'(bv ...)))])
       (with-syntax ([(f ...) (map (λ (v) (expansion-cata-id (ref v)))
                                   (syntax->list #'(c ...)))])
       #'(append (append-map (λ (bv ...)
                               (with-variables (u ...)
                                 (with-catas*  ([c f] ...)
                                   (construct (a*)))))
                             bv ...)
                 (construct d))))]
    [(_ (a . d))                           #'(cons (construct a) (construct d))]
    [(_ ())                                #''()]
    [(_ #:catas {c ...} f . more)          #'(with-catas (c ...) f
                                               (construct . more))]
    #;[(_ #:catas {c ...} f . more)        (with-syntax ([(t ...) (generate-temporaries #'(c ...))])
                                             #'(let ([t (construction-cata (λ () (f c)))] ...)
                                                 ; TODO: postpone the wrapping of the cata to 
                                                 ;       the references of c
                                                 ;       Why? This will handle ellipsis.
                                                 (let ([c t] ...)
                                                   (with-variables (c ...)
                                                     (construct . more)))))]
    [(_ {v ...} . more)                #'(with-variables {v ...} (construct . more))]
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
  #;(check-equal? (let ([a '((1 2 3) (x y z))] [b '(11 12)])
                    (with-variables (a)
                      (construct (x (... {a b} (b (... {a} a))) z)))) ; reads as x (b a ...) ... z
                  '(x (11 1 2 3) (12 x y z) z))
  #;(check-equal? (let ([a '(((1 2 3) (4 5 6)) ((11 12 13) (14 15 16)))])
                    (construct {a}
                               ((... {a} (... {a} (... {a} a))))))
                  '(1 2 3 4 5 6 11 12 13 14 15 16))
  #;(check-equal? (let ([a '((1 2 3) (x y z))] [b '(11 12)])
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

(define (simplify-lite s-exp)
  (define recur simplify-lite)
  (displayln s-exp)
  (match s-exp
    ; datums
    [(? symbol? x)                          x]
    [(list)                                 '()]
    [(? number? n)                          n]
    ; 
    [(list 'quote d)                        (construct {d} d)]
    [(list 'if e0 e1)                       (construct #:catas {e0 e1} recur
                                                       (if e0 e1 (void)))]
    [(list 'if e0 e1 e2)                    (construct {e0 e1 e2}
                                                       (if e0 e1 e2))]
    [(list 'begin e* en)                    (construct #:catas {e* en} recur
                                                       (begin e* en))]
    [(list 'lambda (list x* ...) 
           body* body)                      (construct {x*} #:catas {body* body} recur
                                                       (lambda x* (begin body* body)))]
    [(list 'letrec (list (list x* e*))
           body*  body)                     (construct {x*} #:catas {e* body* body} recur
                                                       (letrec ([x* e*]) (begin body* body)))]
    #;[(list e e*)                          (construct #:catas {e e*} recur
                                                       (e e*))]
    [_ (error 'simplify-litt "got ~a" s-exp)]))

(define (simplify s-exp)
  (displayln s-exp)
  (match s-exp
    ; datums
    [(? symbol? x)                          x]
    [(list)                                 '()]
    [(? number? n)                          n]
    ; 
    [(list 'quote d)                        (construct {d} d)]
    [(list 'if e0 e1)                       (construct #:catas {e0 e1} simplify
                                                       (if e0 e1 (void)))]
    [(list 'if e0 e1 e2)                    (construct {e0 e1 e2}
                                                       (if e0 e1 e2))]
    [(list 'begin e* ... en)                (construct #:catas {e* en} simplify
                                                       (begin e* ... en))]
    [(list 'lambda (list x* ...) 
           body* ... body)                  (construct {x*} #:catas {body* body} simplify
                                                       (lambda (x* ...) (begin body* ... body)))]
    [(list 'letrec (list (list x* e*) ...)
           body* ... body)                  (construct {x*} #:catas {e* body* body} simplify
                                                       (letrec ([x* e*] ...) (begin body* ... body)))]
    [(list e e* ...)                        (construct #:catas {e e*} simplify
                                                       (e e* ...))]
    
    [_ (error 'simplify "got ~a" s-exp)]))

(simplify '(if 1 (letrec ([x (if 2 3)]) 4 5)))
