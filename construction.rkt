#lang racket
;;; Notes: two level ... work (with explicit variables)

(require (for-syntax syntax/parse
                     syntax/id-table)
         racket/stxparam)

;;; Construction

; construct is to construction as match is to deconstruction

; (construct 1)          => 1
; For x unbound in the construct environment:
; (construct x)          => 'x
; (construct (x . d))    => (cons (construct x) (construct d))
;; For x bound to construction transformer t in the construction environment
; (construct x)          => (t x)
; (construct (x a ...))  => (t x (list (construct a) ...)))
;; For x bound to v a non-transformer value in the construction environment
; (construct x)          => x
; (construct (x ...))    => ?



(define-syntax-parameter env (make-immutable-free-id-table))
(struct construction-transformer (transform))

(begin-for-syntax  
  (define (bound? id)   (free-id-table-ref (syntax-parameter-value #'env) id #f))
  (define (unbound? id) (not (bound? id)))
  
  (define-syntax-class bound
    #:description "identifier bound in the construction environment"
    (pattern var:id
             #:fail-unless (bound? #'var) 
             "identifier bound in the construction environment expected"))
  
  (define-syntax-class unbound
    #:description "an identifier not bound in the construction environment"
    (pattern var:id
             #:fail-unless (unbound? #'var)
             "an identifier not bound in the construction environment expected")))

(define-syntax (with-constructors stx)
  (syntax-parse stx
    [(_ (id ...) body ...)
     (define new-env
       (for/fold ([r (syntax-parameter-value #'env)]) ([id (syntax->list #'(id ...))])
         (free-id-table-set r id #t)))
     #`(syntax-parameterize ([env #,new-env])
                            body ...)]))

(define-syntax (construct stx)
  (syntax-parse stx
    [(_ x:number)      #'x]
    [(_ x:unbound)     #''x]
    [(_ x:bound)       #'(if (construction-transformer? x)
                             ((construction-transformer-transform x))
                             x)]
    [(_ (x:bound . d)) #'(let ([vd (construct d)])
                           (if (construction-transformer? x)
                               (apply (construction-transformer-transform x) vd)
                               (cons x vd)))]
    [(_ (((~literal ...) {bv ...} ((~literal ...) {bv2 ...} a*)) . d))
     #'(append (append-map (λ (bv ...)
                             (with-constructors (bv ...)
                               (construct (((... ...) {bv2 ...} a*)))))
                           bv ...)
               (construct d))]
    [(_ (((~literal ...) {bv ...} a*) . d))
     (with-syntax (#;[(v ...) (bound-vars-of a*)])
       #'(append (map (λ (bv ...)
                        (with-constructors (bv ...)
                          (construct a*)))
                      bv ...)
                 (construct d)))]
    
    
    
    [(_ (a . d))       #'(cons (construct a) (construct d))]
    [(_ ())            #''()]
    [_ (error 'construct "got ~a" stx)]))


(module+ test (require rackunit)
  (struct foo (bar) #:transparent)
  (check-equal? (construct 1) 1)
  (check-equal? (construct x) 'x)
  (check-equal? (construct y) 'y)
  (check-equal? (let ([x 42])
                  (with-constructors (x)
                    (construct 42)))
                42)
  (check-equal? (let ([x (construction-transformer (λ v (cons 'x: v)))])
                  (with-constructors (x)
                    (construct x)))
                '(x:))
  (check-equal? (let ([Foo (construction-transformer (λ v (apply foo v)))])
                  (with-constructors (Foo)
                    (construct (Foo 42))))
                (foo 42))
  (check-equal? (let ([Foo (construction-transformer (λ v (apply foo v)))])
                  (with-constructors (Foo)
                    (construct (foo (Foo foo)))))
                `(foo, (foo 'foo)))
  (check-equal? (let ([a '(1 2 3)])
                  (with-constructors (a)
                    (construct (x (... {a} a) y))))      ; read as  x a ... y
                '(x 1 2 3 y))
  (check-equal? (let ([a '(1 2 3)])
                  (with-constructors (a)
                    (construct (x (... {a} (y a)) z))))  ; read as  x (y a) ... z
                '(x (y 1) (y 2) (y 3) z))
  (check-equal? (let ([a '((1 2 3) (x y z))])  ; <=== TODO 
                  (with-constructors (a)
                    (construct (x (... {a} (... {a} a)) z))))  ; read as  x a ... ... y
                '(x 1 2 3 x y z z))
  #;(check-equal? (let ([a '((1 2 3) (x y z))] [b '(11 12)])  ; <=== TODO 
                    (with-constructors (a)
                      (construct (x (... {a b} (b (... {a} a))) z))))
                  '(x (11 1 2 3) (12 x y z))))


