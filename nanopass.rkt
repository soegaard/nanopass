#lang racket
;;; TODO
;;;   done  - parse define-language into structures
;;;         - produce structure definitions for nonterminals
;;;         - 

;;;
;;; The nanopass framework is a framework for writing compilers.
;;; This implementation follows the specification in 
;;; "A Nanopasss Framework for Commercial Compiler Development"
;;; by Andy Keep.

;;;
;;; Example 1
;;;

; syntax
;     (DEFINE-LANGUAGE lang-name clause ...)
; where 
;     lang-name is an identifier and
; and 
;          clause           =   entry-clause 
;                           |   terminals-clause 
;                           |   nonterminal-clause 
;                           |   extension-clause

;       entry-clause        = (ENTRY nonterminal-name)

;     terminals-clause      = (TERMINALS terminal-clause-spec ...)
;     terminals-clause-spec = (terminal-name (meta-var ...))
;                           | (=> (terminal-name (meta-var ...)) prettifier)
;                           | (terminal-name (meta-var ...)) => prettifier)

;  nonterminal-clause = (non-terminal-id  (meta-var ...) production-clause ...)

;   production-clause = terminal-meta-var
;                     | nonterminal-meta-var
;                     | production-s-expression
;                     | (keyword . production-s-expression)


; Notes:
;  1) The entry nonterminal-name must be specified in the language
;  2) Only one entry clause can be present
;  3) For each terminal-name a predicate terminal-name? must be in scope.
;  4) meta-var is used to refer to this terminal type in the langauge and pass definitions
;  5) prettifier is a procedure of one arguments used to unparse that terminal type
;  6) A keyword is a name that is neither a terminal-meta-var nor a nonterminal-meta-var
;     which must be matched exactly (i.e. a literal)
;  

(require (for-syntax syntax/parse racket/match racket/list racket/syntax))

;;; KEYWORDS
; The keywords entry and terminals are used by define-language.
; Bind them to syntax signaling an error, if used outside define-language.

(define-syntax (entry stx)
  (raise-syntax-error 'entry "entry keyword used outside define-language" stx))
(define-syntax (terminals stx)
  (raise-syntax-error 'terminals "terminals keyword used outside define-language" stx))
(define-syntax (=> stx)
  (raise-syntax-error '=> "used outside define-language" stx))


;;; STRUCTURES
; The define-language constructs parses its input into
; structures representing terminals and nonterminals.

(begin-for-syntax
  (struct terminal    (stx name meta-vars prettifier)  #:prefab)
  ; name is an identifier, meta-vars is a list of identifeirs and prettifier
  ; is a syntax-object representing an expression.
  (struct nonterminal (stx name meta-vars productions) #:prefab)
  ; productions is a list of syntax-objects of the follwing forms:
  ;   terminal-meta-var
  ;   nonterminal-meta-var
  ;   producition-s-expression
  ;   (keyword . production-s-expression)
  ; where keyword is neither type of meta var.
  terminal-meta-vars
  )


;;; SYNTAX CLASSES
; Define syntax classes to match the grammar of define-language.
(begin-for-syntax  
  (define-syntax-class meta-vars
    #:attributes (vars)
    (pattern (var:id ...)
             #:attr vars (syntax->list #'(var ...))))
  
  (define-syntax-class entry-clause 
    #:attributes (name) #:literals (entry)
    (pattern (entry nonterminal-name)
             #:with name #'nonterminal-name))
  
  (define-syntax-class terminals-clause-spec
    #:attributes (terminal) #:literals (=>)    
    (pattern (~and stx (name:id mvs:meta-vars))
             #:attr terminal  
             (terminal #'stx #'name (attribute mvs.vars) #'identity))
    (pattern (~and stx (=> (name:id mvs:meta-vars) prettifier))
             #:attr terminal  (terminal #'stx #'name (attribute mvs.vars) #'prettifier))
    (pattern (~and stx (name:id mvs:meta-vars => prettifier))
             #:attr terminal  (terminal #'stx #'name (attribute mvs.vars) #'prettifier)))
  
  (define-syntax-class terminals-clause 
    #:attributes (terminals) #:literals (terminals)
    (pattern (terminals spec:terminals-clause-spec ...)
             #:attr terminals (attribute spec.terminal)))
  
  (define-syntax-class production-clause
    #:attributes (production)
    (pattern (~and prod ; to bind prod
                   (~or meta-var:id ; either terminal-meta-var or nonterminal-meta-var
                        (keyword:id . production-s-expression)
                        production-s-expression))
             #:attr production #'prod))
  
  (define-syntax-class nonterminal-clause
    #:attributes (nonterminal)
    (pattern (~and stx (name:id mvs:meta-vars c:production-clause ...))
             #:attr nonterminal 
             (nonterminal #'stx #'name (attribute mvs.vars) (attribute c.production))))
  
  (define-syntax-class lang-clause
    #:attributes (entry-name terminals nonterminal)
    (pattern c:entry-clause 
             #:attr entry-name (attribute c.name)
             #:attr terminals #f
             #:attr nonterminal #f)
    (pattern c:terminals-clause
             #:attr entry-name #f
             #:attr terminals (attribute c.terminals)
             #:attr nonterminal #f)
    (pattern c:nonterminal-clause
             #:attr entry-name #f
             #:attr terminals #f
             #:attr nonterminal (attribute c.nonterminal))))

;; Various helpers
(begin-for-syntax
  (define (qualified-name ctx prefix suffix [src ctx])
    (format-id ctx "~a:~a" prefix suffix #:source src))
  
  (define (qualified-struct-name ctx lang nt prod [src ctx])
    (format-id ctx "~a:~a:~a" lang nt prod #:source src)))


(define-syntax (define-language stx)
  (define (syntax-error error-msg) (raise-syntax-error 'define-langauge error-msg stx))
  (syntax-parse stx
    [(define-language language-name:id clause:lang-clause ...)
     ;; The components of the define-language construct are:
     (define lang-name    (syntax-e #'language-name))
     (define entry-names  (filter values (attribute clause.entry-name)))
     (define terminals    (apply append (filter values (attribute clause.terminals))))
     (define nonterminals (filter values (attribute clause.nonterminal)))
     
     (when (empty? nonterminals)
       (syntax-error "At least one nonterminal must be present"))
     
     (define entry-name
       ; If no entry name is defined, then the entry is the first nonterminal
       (match entry-names
         [(list)      (first nonterminals)]
         [(list name) name]
         [__ (raise-syntax-error 'define-language "only one entry is allowed" stx)]))
     
     ;; Check that all meta variables are associated with only one terminal or nonterminal
     ; First we define a hash table that associates a meta variable to its terminal or nonterminal
     (define meta-vars-ht (make-hash ))
     (define (meta-vars-ref v) (hash-ref meta-vars-ht (syntax-e v) #f))
     (define (meta-vars-set! v a) (hash-set! meta-vars-ht (syntax-e v) a))
     ; The error message will highlight the second use of a meta variable 
     (define (raise-meta-var-error v)
       (raise-syntax-error 'define-language 
                           "a meta variable can only be associated to one terminal or nonterminal"
                           v))
     (define (register-meta-var v a)
       (cond [(meta-vars-ref v) (raise-meta-var-error v)]
             [else              (meta-vars-set! v a)]))
     ; Check them
     (for ([t terminals])
       (for ([v (terminal-meta-vars t)])
         (register-meta-var v t)))
     (for ([nt nonterminals])
       (for ([v (nonterminal-meta-vars nt)])
         (register-meta-var v nt)))
     
     (define all-terminal-meta-vars    (append-map terminal-meta-vars terminals))
     ; (define all-nonterminal-meta-vars (append-map 

     (display (list 'define-language 'all-terminal-meta-vars all-terminal-meta-vars))
     

     ;; At this point we are ready to 
     ;;   1) define structures representing the nonterminals
     ;;   2) save information on the language for define-pass and others
     ;;   3) define an unparser
     
     ;; Ad 1) For each nonterminal production of the form (keyword . production-s-expression)
     ;;       we define a struct lang-name:keyword
     ;; (define-language L (nt (mv ...) (keyword . production-s-expression) ...)
     ;; will generate structs (struct L:nt:keyword f0 f1 f2 ...) where
     ;; the number of fields are given by production-s-expression.
     
     (define struct-names
       (for/list ([nt nonterminals])
         (match nt
           [(nonterminal nt-stx nt-name meta-vars productions)
            (for/list ([prod productions])
              ; TODO: only for productions that are keyword applications
              (syntax-case prod ()
                [(keyword . more)
                 (begin
                   (displayln #'keyword)
                   (qualified-struct-name prod lang-name nt-name #'keyword))]
                [_ #f]))]
           [_ #f])))
     (displayln (list 'define-language 'struct-names struct-names))
     
     (datum->syntax #'here
                    (list 'quote
                          (list (list (list "lang-name"   (syntax-e #'lang-name)))
                                (list "entry-name"  entry-name)
                                (list "terminals"   terminals)
                                (list "non-terms"   nonterminals))))]))

(define-language Lsrc
  (entry Expr) 
  (terminals
   (uvar (x))
   (primitive (pr))
   (datum (d)))
  (Expr (e body)
        x
        (quote d)
        (if e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body)
        (let ([x* e*] ...) body) 
        (letrec ([x* e*] ...) body) 
        (set! x e)
        (pr e* ...)
        (call e e* ...)))

