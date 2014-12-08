#lang racket
(module+ test (require rackunit))
;;;
;;; CURRENT - writing unparser
;;;         - todo: use the terminal prettifier

;;; TODO
;;;   done  - parse define-language into structures
;;;   done  - produce pure definitions for nonterminals
;;;   done  - produce type checking constructors for the nonterminal structures
;;;   done  - accept nonterminals as productions in nonterminals
;;;         - check References to meta-variables in a production must be unique
;;;         - handle keywords that appear in multiple clauses such as (if e0 e1) and (if e0 e1 e2)
;;;         - unparsing
;;;         - with-language + construct
;;;         - unconstruct
;;; TODO
;;;         - should ... be disallowed as a keyword?

;;; IDEAS (from akeep/nanopass)
;;;         * Added a prune-language form that, when given a language, starts traversing
;;;           the language from the entry nontermainal and determines if there are any
;;;           dead nonterminals or terminals in the language, prunes them, and returns an
;;;           S-expression representing only the reachable parts of the language.
;;;         * added checking for mutually recursive nonterminals so that we now report
;;;           an error to the user.  this was a simple change, and if we want to support
;;;           this in the future, there is probably a way to do so, we just need to be
;;;           careful about pass generation.
;;;
;;; The nanopass framework is a framework for writing compilers.
;;; This implementation follows the specification in 
;;; "A Nanopasss Framework for Commercial Compiler Development"
;;; by Andy Keep.

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
;                     | (keyword . production-s-expr)

;   production-s-expr = meta-variable
;                     | (MAYBE meta-variable)
;                     | (production-s-expr ellipsis)
;                     | (production-s-expr ellipsis production-s-expr ... . prod-s-expr)
;                     | (production-s-expr . production-s-expr)
;                     | ()
;  where meta-variable is either a terminal-meta-var or a nonterminal-meta-var possibly
;  followed by a sequence of ?, * or digits.

; Notes:
;  1) The entry nonterminal-name must be specified in the language
;  2) Only one entry clause can be present
;  3) For each terminal-name a predicate terminal-name? must be in scope.
;  4) meta-var is used to refer to this terminal type in the langauge and pass definitions
;  5) prettifier is a procedure of one arguments used to unparse that terminal type
;  6) A keyword is a name that is neither a terminal-meta-var nor a nonterminal-meta-var
;     which must be matched exactly (i.e. a literal)
;  7) Note that keywords can not appear in production-s-expression
;  8) No "unknown" symbols can appear in production-s-expression 


(require (for-syntax syntax/parse racket/match racket/list racket/syntax))
(require (for-syntax "fancier-quote.rkt"))
(require racket/stxparam "fancier-quote.rkt")

;;; KEYWORDS
; The keywords entry and terminals are used by define-language.
; Bind them to syntax signaling an error, if used outside define-language.

(define-syntax (entry stx)
  (raise-syntax-error 'entry "entry keyword used outside define-language" stx))
(define-syntax (terminals stx)
  (raise-syntax-error 'terminals "terminals keyword used outside define-language" stx))
(define-syntax (=> stx)
  (raise-syntax-error '=> "used outside define-language" stx))
(define-syntax (maybe stx)
  (raise-syntax-error '=> "used outside define-language" stx))


;;; STRUCTURES
; The define-language constructs parses its input into
; structures representing terminals and nonterminals.

(begin-for-syntax 
  (struct language    (stx name entry terminals nonterminals keywords+constructors
                           metavars-ht) #:transparent)
  ; name is an identifier
  ; entry is an identifier (of a nonterminal)
  ; terminals and nonterminals are lists of terminals and nonterminals respectively
  ; keywords+constructors is a list of elements of the form (list keyword struct-name)
  
  (struct terminal    (stx name meta-vars prettifier)  #:transparent)
  ; name is an identifier, meta-vars is a list of identifiers and 
  ; prettifier is a syntax-object representing an expression.
  
  (struct nonterminal (stx name meta-vars productions) #:transparent #:mutable)
  ; productions is a list of syntax-objects of the follwing forms:
  ;   terminal-meta-var
  ;   nonterminal-meta-var
  ;   production-s-expression
  ;   (keyword . production-s-expression)
  ; where keyword is neither type of meta var.
  
  (struct production (stx) #:transparent)
  ; stx is used for the syntax location (the original production appearing in define-language)
  (struct    terminal-production production (terminal)    #:transparent)
  (struct nonterminal-production production (nonterminal) #:transparent)
  (struct     keyword-production production 
    (keyword struct-name field-count field-names field-depths s-exp) #:transparent)
  (struct s-exp-production production ())
  ; a keyword production will generate a structure definition with
  ; where field-count is the number of fields,
  ;       field-names is a list of names (identifiers) of the fields
  ;       field-depths is a list of variable depths
  ;       (i.e.  x          has depth 0)
  ;              x ...      has depth 1
  ;             (x ...) ... has depth 2
  ;             etc
  (struct ellipsis (production-s-expression) #:transparent))

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
  
  (define (syntax-pair? stx) 
    ; if stx is a syntax pair, return a pair of syntaxes,
    ; otherwise return #f
    (and (syntax? stx) 
         (let ([x (syntax-e stx)])
           (and (pair? x) x))))
  
  (define (qualified-name ctx prefix suffix [src ctx])
    (format-id ctx "~a:~a" prefix suffix #:source src))
  
  (define (qualified-struct-name ctx lang nt prod [src ctx])
    (format-id ctx "~a:~a:~a" lang nt prod #:source src))
  
  (require (only-in srfi/13 string-reverse))
  (define (strip-meta-var-suffix s)
    (define (strip-string s)
      (match (regexp-match #rx"(^[0-9*?]*).*$" (string-reverse s))
        [(list _ suffix-reversed)
         (define m (string-length s))
         (define n (string-length suffix-reversed))
         (substring s 0 (- m n))]
        [_ s]))
    (define (strip-symbol s)
      (string->symbol (strip-string (symbol->string s))))
    (define (strip-syntax s)
      (datum->syntax s (strip-symbol (syntax-e s))))
    (cond
      [(syntax? s) (strip-syntax s)]
      [(symbol? s) (strip-symbol s)]
      [(string? s) (strip-string s)]
      [else (error 'strip-meta-var-suffix "expected identifer, symbol, or, string, got:~a" s)])))

;;; COMPILE TIME INFORMATION
(define-for-syntax defined-languages '())


;;; METAVARIABLES
; Each terminal and nonterminal has an associated set of (normally short) names
; used to refer to them in productions. These abbreviations are called metavariables.
; The producedure parse-defined-language produce a hash table which maps
; metavariables (identifiers) to their terminal or nonterminal (represented as syntax-objects).
(begin-for-syntax
  (define (meta-vars-ref ht v)
    (unless (identifier? v) (error 'meta-vars-ref "got ~a" v))
    (hash-ref  ht (strip-meta-var-suffix (syntax-e v)) #f))
  
  (define (meta-vars-set! ht v a) 
    (hash-set! ht (strip-meta-var-suffix (syntax-e v)) a))
  
  (define (register-meta-var ht v a)
    (cond [(meta-vars-ref ht v) (raise-meta-var-error v)]
          [else                 (meta-vars-set! ht v a)]))
  
  
  
  ; The error message will highlight the second use of a meta variable 
  (define (raise-meta-var-error v)
    (raise-syntax-error 'define-language 
                        "a metavariable can only be associated to one terminal or nonterminal"
                        v))
  (define (terminal-meta-var? ht v)
    ; ht is usually metavars-ht
    (cond [(meta-vars-ref ht v) => terminal?]
          [else #f]))
  (define (nonterminal-meta-var? ht v)
    (cond [(meta-vars-ref ht v) => nonterminal?]
          [else #f]))
  (define (meta-var? ht v)
    (match v
      [(? identifier?) (meta-vars-ref ht v)]
      [(ellipsis v)    (meta-var? v)]
      [_               #f])))

(begin-for-syntax
  (define (parse-define-language stx)
    (define (syntax-error error-msg [stx stx]) (raise-syntax-error 'define-language error-msg stx))
    (syntax-parse stx
      [(define-language language-name:id clause:lang-clause ...)
       ;; 1. Find language and entry name, gather terminals and nonterminals.
       (define lang-name    (syntax-e #'language-name))
       (define entry-names                (filter values (attribute clause.entry-name)))
       (define terminals    (apply append (filter values (attribute clause.terminals))))
       (define nonterminals               (filter values (attribute clause.nonterminal)))
       ;; 2. Check terminals
       ;     (TODO: check that the terminal names are unique)
       (when (empty? nonterminals)
         (syntax-error "At least one nonterminal must be present"))
       ;; 3. Find entry name and make sure there is only one.
       ;;    If none are present, use the name of the first nonterminal.
       (define entry-name
         (match entry-names
           [(list)      (nonterminal-name (first nonterminals))]
           [(list name) name]
           [__ (raise-syntax-error 'define-language "only one entry is allowed" stx)]))
       ;; 4.   Check that metavariables refer to one terminal or nonterminal only.
       ;; 4.a  Create hash table from a metavariable to its terminal or nonterminal
       (define meta-vars-ht (make-hash))
       
       ;; 4.b Insert all terminal and nonterminal metavariables in hash table.
       ;;     This also checks for duplicates (see register meta-var)
       (for ([t terminals])
         (for ([v (terminal-meta-vars t)])
           (register-meta-var meta-vars-ht v t)))
       (for ([nt nonterminals])
         (for ([v (nonterminal-meta-vars nt)])
           (register-meta-var meta-vars-ht v nt)))
       ;; 4.c We can now determine what kind of metavariable an identifier refers to.
       ;;     See terminal-meta-var? and nonterminal-meta-var?
       
       ;; 5.  Collect all keywords and store the associated production.
       ;; 5.a Create hash table from a keyword to its production
       (define keywords-ht (make-hash))
       (define (keywords-ref v)    
         (hash-ref keywords-ht (strip-meta-var-suffix (syntax-e v)) #f))
       (define (keywords-set! v p) 
         (define old-productions (hash-ref keywords-ht (strip-meta-var-suffix (syntax-e v)) '()))
         (hash-set! keywords-ht (strip-meta-var-suffix (syntax-e v)) (list p old-productions)))
       (define (register-keyword k nt p) 
         ; todo: add additional checks here
         (keywords-set! k (list nt p)))
       ;; 5.b Each production of a nonterminal can potentially introduce a new keyword.
       ;;     Run through them and store them.
       (for ([nt nonterminals])
         (for ([prod (nonterminal-productions nt)])
           (syntax-parse prod #:literals (maybe)
             [x:id 
              ; A reference to another nonterminal or a terminal is ok. Other references are errors.
              (unless (meta-vars-ref meta-vars-ht #'x)
                (syntax-error 
                 "variable in production is not associated to a terminal or a nonterminal" #'x))]
             [(x:id . _)
              (if (meta-vars-ref meta-vars-ht #'x)
                  (void) ; (x . _) is an application of where x stands for a terminal or a nonterminal
                  (register-keyword #'x nt prod))] ; a new constructs implies a new keyword
             [(maybe meta-var)   'todo-a-maybe-production]
             [(something . more) 'todo-an-application-production] ; TODO: remove
             [__ 'ok])))
       ;; 6. At this point the representation of productions changes from syntax objects
       ;;    to a structure representation. There are four types of productions:
       ;;        (struct production (stx))
       ;;        (struct    terminal-production production (terminal))
       ;;        (struct nonterminal-production production (nonterminal))
       ;;        (struct     keyword-production production 
       ;;                            (keyword struct-name field-count field-names field-depths s-exp))
       ;;        (struct s-exp-production production ())
       
       ;; 6.a Processing the productions in syntax object form is easier,
       ;;     we rewrite ellipsis patterns to prefix i.e. pat ... besomes (ellipsis pat)
       (define (maybe?    stx) (and (identifier? stx) (eq? (syntax-e stx) 'maybe)))
       (define (make-ellipsis-prefix se)
         (define (mvar? v) (meta-var? meta-vars-ht v))
         (define (ellipsis? stx) (eq? (syntax-e stx) '...))
         (define (recur se)
           (match (or (syntax-pair? se) se)
             [(? identifier? v)               (if (meta-var? meta-vars-ht v) v (error 'here "foo"))]
             [(? syntax? s)                   (recur (syntax-e s))]
             [(list (? maybe?) (? mvar?))     se]   ; todo: ntroduce maybe struct ?
             [(cons (? maybe?) _)             (raise-syntax-error 
                                               'define-language "(maybe meta-var) expected" se)]
             [(list se0 (? ellipsis?))        (list (ellipsis (recur se0)))]
             [(list se0 (? ellipsis?) se* ... sen)
              (cons (ellipsis (recur se0)) (append (map recur se*) (list (recur sen))))]
             [(cons se0 se1)                  (cons (recur se0) (recur se1))]
             ['()                             '()]
             [_ 
              (raise-syntax-error 'define-language "not allowed in production-s-expression"
                                  se)]))
         (recur se))
       ;; 6.b Generate the structure representation for nonterminals, 
       ;;     here the hardest case the keyword production.  
       ;   production-clause = | (keyword . production-s-expr)
       ;   production-s-expr = meta-variable
       ;                     | (maybe meta-variable)
       ;                     | (production-s-expr ellipsis)
       ;                     | (production-s-expr ellipsis production-s-expr ... . prod-s-expr)
       ;                     | (production-s-expr . production-s-expr)
       ;                     | ()              
       (define (generate-keyword-production prod x fields s-exp nt ps)
         ; the production has the form (x field ...) and x is a keyword
         ; and orig-nt and ps are the result of (keyword-ref #'x)
         (with-syntax ([x x] [(field ...) fields] [s-exp s-exp])
           ;; 6.b.1 Each keyword have a struct associated.
           ;;       The fields of the struct consists of the pattern variables
           ;;       present in the s-expressions of (keyword s-exp ...).
           ;;       First we must extract the names of the pattern variables.
           ;;       At the same time we determine their depth.
           ;;       x in x has depth 0,  x in x ... depth 1,  x in (x ...) ... depth 2 etc
           (struct extracted-name (name depth) #:prefab)
           (define (extract-names se)
             (define (meta-var? v)
               (define ht meta-vars-ht)
               (match v
                 [(? identifier?) (meta-vars-ref ht v)]
                 [(ellipsis v)    (meta-var? v)]
                 [_               #f]))
             (define (recur se d)
               (define (map-recur se* d) (map (λ (se) (recur se d)) se*))
               (match (if (and (syntax? se) (not (identifier? se)))
                          (syntax-e se)
                          se)
                 [(ellipsis se)                         (recur se d)]
                 [(? meta-var? v)                       (list (extracted-name v d))]
                 [(list (ellipsis se) se* ...)          (list (recur se (+ d 1))
                                                              (map-recur se* d))]
                 [(list (? maybe?) (? meta-var? v))     (list v)]
                 [(cons se0 se1)                        (list (recur se0 d) (recur se1 d))]
                 ['()                                   '()]                                  
                 [_ (error 'extract-names "got~a" se)]))
             (flatten (recur se 0)))
           (define extracted-names (extract-names (make-ellipsis-prefix #'(field ...))))
           ;; 6.b.2 The name of the struct, names of fields and their depths are now ready.
           (define fields       (map extracted-name-name  extracted-names))
           (define field-depths (map extracted-name-depth extracted-names))
           (define keyword #'x)
           (define field-count (length fields))
           (define struct-name 
             (qualified-struct-name prod lang-name (nonterminal-name nt) keyword))
           (define field-names (for/list ([f fields])
                                 (match f 
                                   [(ellipsis name) name]
                                   [_ f])))
           ;; 6.b.3 Store all information in a keyword-production.
           (keyword-production prod keyword struct-name 
                               field-count field-names field-depths 
                               (make-ellipsis-prefix #'s-exp))))
       ;; 6.c Finally we can generate the production structures
       (for ([nt nonterminals])
         (define prods
           (for/list ([prod (nonterminal-productions nt)])
             (syntax-parse prod #:literals (maybe)
               [x:id 
                (match (meta-vars-ref meta-vars-ht #'x)
                  [(? terminal? t)     (terminal-production prod t)]
                  [(? nonterminal? nt) (nonterminal-production prod nt)]
                  [_ (error 'define-language "internal error - expected earlier detection")])]
               [(maybe meta-var)   (error 'todo-a-maybe-production)]
               [(~and (x:id field ...) (_ . s-exp))
                (match (keywords-ref #'x)
                  [(list orig-nt ps)
                   (generate-keyword-production prod #'x #'(field ...) #'s-exp nt ps)]
                  ;; otherwise it is an s-exp-production
                  [_ (s-exp-production (make-ellipsis-prefix prod))])]
               ; an s-exp-production that doesn't begin with a terminal or nonterminal
               ; TODO: Is this case impossible?
               [(something . more) (s-exp-production prod prod)]
               [__ 'ok])))
         ; replace old contents of productions field in the nonterminal with
         ; the structure representation of productions
         (set-nonterminal-productions! nt prods))
       ; (displayln (list 'define-language 'productions: ))
       ; (displayln prods)
       
       ; keep a list of keywords and corresponding constructor names for later use
       (define keywords+constructors 
         (apply append
           (for/list ([nt nonterminals])
             (match nt
               [(nonterminal nt-stx nt-name meta-vars productions)
                (for/list ([prod productions]
                           #:when (keyword-production? prod))
                  (match prod
                    [(keyword-production stx keyword struct-name 
                                         field-count field-names field-depths s-exp)
                     (list keyword struct-name)]))]))))
       
       (language 'stx #'language-name 
                 entry-name terminals nonterminals keywords+constructors
                 meta-vars-ht)])))
;;; 

;;; define-language
(define-syntax (define-language stx)
  (define (syntax-error error-msg [stx stx]) (raise-syntax-error 'define-language error-msg stx))
  (syntax-parse stx
    [(define-language language-name:id clause:lang-clause ...)
     ;; 0. Parse the define-language into a language struct.
     (define parsed-lang (parse-define-language stx))
     ; (displayln (list 'parsed-lang parsed-lang)) (newline)
     (match-define 
       (language _ lang-name entry-name terminals nonterminals keywords+constructors metavars-ht) 
       parsed-lang)
     (define all-terminal-meta-vars    (append-map terminal-meta-vars terminals))
     
     ;; At this point we are ready to 
     ;;   1) define structures representing the nonterminals
     ;;   2) define an parser from s-exps to structures for the language
     ;;   2) save information on the language for define-pass and others
     ;;   3) define an unparser
     
     ;; Ad 1) For each nonterminal production of the form (keyword . production-s-expression)
     ;;       we define a struct lang-name:keyword
     ;; (define-language L (nt (mv ...) (keyword . production-s-expression) ...)
     ;; will generate structs 
     ;;      (struct L:nt:keyword f0 f1 f2 ...) 
     ;; where f0, f1, ... are the pattern variables occuring 
     ;; in production-s-expression.
     
     (define struct-definitions-stx
       (apply append
         (for/list ([nt nonterminals])
           (match-define (nonterminal nt-stx nt-name meta-vars productions) nt)
           (for/list ([prod productions]
                      #:when (keyword-production? prod))
             (match-define
               (keyword-production stx keyword struct-name field-count field-names field-depths s-exp) 
               prod)
             (with-syntax ([struct-name struct-name]
                           [(field-name ...) field-names])
               ; This is the basic structure definition:
               #'(struct struct-name (field-name ...) #:prefab)
               ; TODO: Generate constructors with "contracts"
               )))))
     
     ;; Ad 2) 
     ;; 
     ;; Generate definitions for a parser from s-exps to our language structures.
     ;; An example of the structure of such an parser.
     ;; To parse the language L a parser parse-L is defined.
     ;; In its body there are parsers for each nonterminal (in the example Expr).
     ;; The body of parse-L simply calls the parser associated with the entry nonterminal.
     
     #;(define (parse-L se)
         ; 1) define parsers for each nonterminal
         ; 2) call the entry parser
         (define (parse-Expr se)
           (define p parse-expr)
           (define (p* se*) (map p se*))
           (match se
             ;; For each terminal named name a clause [(? name? x) x]
             ;; is generated - the user has must provide bindings for name?.
             [(? uvar? x)        x]
             [(? primitive? pr) pr]
             [(? datum? d)       d]
             ;; For each keyword k we need to a pattern that matches (k . prod-s-exp).
             ;;      (list 'k . <more>)
             ;; here <more> is generated by   construct-parse-clause.
             ;; The corresponding template that actually constructs the structure
             ;; is generated by  production-s-exp->match-template.
             ;; A pattern variable of depth 0 becomes (p e) in the template.
             ;; A pattern variable of depth 1 becomes (p* e) = (map p e) in the template.
             ;; A pattern variable of depth 2 becomes (p** e) == (map p* e) in the template.
             ;; etc 
             [(list 'quote (? datum? d))                  (Lsrc:Expr:quote d)]
             [(list 'if    e0 e1 e2)                      (Lsrc:Expr:if (p e0) (p e1) (p e2))]
             [(list 'begin e* ooo e)                      (Lsrc:Expr:begin (p* e*) (p e))]
             [(list 'lambda (list (? uvar? x*) ooo) body) (Lsrc:Expr:lambda x* (p body))]
             [(list 'let    (list [list x* e*] ooo) body) (Lsrc:Expr:let    x* (p* e*) (p body))]
             [(list 'letrec (list [list x* e*] ooo) body) (Lsrc:Expr:letrec x* (p* e*) (p body))]
             [(list 'set!   (? uvar? x) e)                (Lsrc:Expr:set!   x  (p e))]
             [(list 'call e e* ooo)                       (Lsrc:Expr:call   (p e) (p* e*))]
             [(list (? primitive? pr) e* ooo)             (cons pr (p* e*))]
             [_ (error 'parse "got: ~a" se)]))
         ; the entry is Expr:
         (parse-Expr se))
     
     (define parser-definition-stx
       (with-syntax ([ooo #'(... ...)] [failure #'failure])
         ;; Due to metavariables (pattern variables) of different depth,
         ;; the parser for depth 0 is called, say, parse-Expr
         ;; and the parser for larger depths parse*-Expr.
         ;; Due to nonterminal used as alternatives, we need
         ;; two versions of each: one that signals an error when 
         ;; parsing the nonterminal fails, and one that simple returns #f.         
         ; nonterminal->parse-name
         ;   generate suitable name
         ;   suffix can be used to append a trailing "?"
         (define (nonterminal->parse-name nt depth [suffix ""])           
           (case depth
             [(0)   (format-id stx "parse-~a~a"  (nonterminal-name nt) suffix)]
             [else  (format-id stx "parse*-~a~a" (nonterminal-name nt) suffix)]))
         ; In order to generate the recursive call, we must know which
         ; nonterminal whose parser we are going to call.
         (define (field-name->nonterminal f)  (meta-vars-ref  metavars-ht f))
         
         ; construct-parse-nonterminal : nonterminal -> syntax
         ;     return a parser of s-exp representing the nonterminal nt
         (define (construct-parse-nonterminal nt)
           ; the parser names for the nonterminal
           (match-define (nonterminal stx name meta-vars productions) nt)
           (define parse-nt   (nonterminal->parse-name nt 0))
           (define parse-nt*  (nonterminal->parse-name nt 1))
           (define parse-nt?  (nonterminal->parse-name nt 0 '?))
           (define parse-nt*? (nonterminal->parse-name nt 1 '?)) 
           ; Generate the parser clauses
           (define clauses (append-map (λ(p) (construct-match-clause-for-parser name p)) productions))
           (with-syntax 
               ([(clause ...) clauses] [parse-nt  parse-nt]  [parse-nt* parse-nt*] 
                                       [parse-nt? parse-nt?] [parse-nt*? parse-nt*?])
             ; Put the clauses into parser-nt, then let the other parsers call parse-nt.
             #'(begin
                 ; parse-nt : s-exp [thunk] -> (or <lang:nt:keyword structure> (failure))
                 ;   parse the s-exp and return a struct instance,
                 ;   if parsing fails invoke the failure thunk
                 (define (parse-nt se [failure (λ () (error 'parse-nt "got: ~a" se))])
                   (match se 
                     clause ...
                     [else (failure)]))
                 ; parse-nt : lists-of-depth-d depth [thunk] -> ...
                 ;   parse the s-exps at depth d as the nonterminal nt, 
                 ;   invoke failure if an s-exp doesn't match nt
                 (define (parse-nt* se* d [failure (λ () (error 'parse-nt* "got: ~a" se*))])
                   (if (= d 1)
                       (map (λ(se) (parse-nt  se         failure)) se*)
                       (map (λ(se) (parse-nt* se (- d 1) failure)) se*)))
                 ; predicate version of the parsers (usable as match predicates): 
                 (define (parse-nt?  se)   (let/ec return (parse-nt  se   (λ() (return #f)))))
                 (define (parse-nt*? se d) (let/ec return (parse-nt* se d (λ() (return #f))))))))
         (define (construct-match-clause-for-parser nt-name prod)
           (match prod
             [(terminal-production stx term)
              (match-define (terminal stx name meta-vars prettifier) term)
              (with-syntax ([pred? (terminal->predicate-name #'here term)])
                (list #'[(? pred? x) x]))]
             [(nonterminal-production stx nonterm)
              ; The case where the nonterminal nt has another nonterminal as production.
              ; Use the predicate version of the parser, since the match might fail.
              (with-syntax ([parse-nonterm? (nonterminal->parse-name nonterm 0 '?)])
                (list #'[(app parse-nonterm? x) x]))]
             [(keyword-production stx keyword struct-name field-count field-names field-depths s-exp)
              ; To match (keyword . production-s-exp) we use production-s-exp->match-pattern
              ; to transform production-s-exp into a match pattern.
              ; The template must call constructor to generate a struct of the correct type.
              ; Each matched pattern variable that corresponds to a nonterminal needs
              ; to be wrapped in a recursive call. A pattern variable for a terminal
              ; is used as-is. The "calls" are called field-expression below.
              
              ; First the field expressions needed in the template:
              (define field-expressions
                (for/list ([f field-names] [fd field-depths])
                  (cond [(terminal-meta-var? metavars-ht f) 
                         f] ; as-is
                        [(nonterminal-meta-var? metavars-ht f)
                         (with-syntax ([parse-field 
                                        (nonterminal->parse-name (field-name->nonterminal f) fd)]
                                       [f f])
                           (if (= fd 0)
                               #'(parse-field f failure)
                               #`(parse-field f #,fd failure)))]
                        [else (error 'todo1 "got ~a" f)])))
              ; Now we just need put all the pieces together:
              (define constructor-name (qualified-struct-name stx lang-name nt-name keyword))
              (with-syntax ([keyword                keyword]
                            [(field-name ...)       field-names]
                            [constructor            constructor-name]
                            [(field-expression ...) field-expressions])
                (list #`[(cons 'keyword #,@(production-s-exp->match-pattern s-exp))
                         (constructor field-expression ...)]))]
             [(s-exp-production stx)
              (list #`[#,@(production-s-exp->match-pattern stx) 
                       #,@(production-s-exp->match-template stx)])]
             [else (error 'construct-parse-clause "todo got ~a" prod)]))
         
         (define (terminal->predicate-name loc t)
           (format-id loc "~a?" (terminal-name t)))
         
         ; production-s-exp->match-template : s-exp -> (list syntax)
         ;   generate a match template that matches the s-exp
         ;   Due to ellipsis we return lists of template expressions.
         ;   Slice them were they are used.
         (define (production-s-exp->match-template se)
           ; The recursive call to parser a subexpression depends on the ellipsis
           ; depth d of the pattern variable. We therefore need to keep track of d.       
           (define (recur se d) ; d=depth
             (with-syntax ([ooo #'(... ...)])
               (match (if (syntax-pair? se) (syntax-e se) se)
                 [(? identifier? x)
                  (define mv (meta-vars-ref metavars-ht x))
                  (with-syntax ([x x])
                    (list 
                     (match mv
                       [(terminal stx name meta-vars prettifier)
                        ; a terminal is checked in the pattern, 
                        ; just use the value it is bound as is
                        #'x]
                       [(nonterminal stx name meta-vars productions)
                        (with-syntax ([parse-nt  (nonterminal->parse-name mv 0)]
                                      [parse*-nt (nonterminal->parse-name mv 1)])
                          ; Whatever the nonterminal matched needs to be parsed.
                          ; The depths determine how.
                          (match d
                            [0 #'(parse-nt x failure)]
                            [_ (with-syntax ([d d])
                                 #'(parse*-nt x d failure))]))]
                       [_ ; unrecognized meta variable
                        (displayln se)
                        (error 'production-s-exp->match-pattern "internal error: ~a" se)])))]
                 ; TODO (support maybe in s-exps at some point)
                 ; [(maybe mv) (error 'production-s-exp->match-pattern "todo: ~a" se)]
                 [(ellipsis se0)
                  (list (recur se0 (+ d 1)))]
                 [(list-rest (ellipsis se0) se* ... sen)
                  (append (recur se0 (+ d 1))
                          (append-map (λ(se) (recur se d)) se*)
                          (recur sen d))]
                 [(cons se0 se1) 
                  (list #`(cons #,@(recur se0 d) #,@(recur se1 d)))]
                 ['() '()]
                 [_ (error 'production-s-exp->match-pattern "gotx: ~a" se)])))
           (recur se 0))
         
         
         ;   production-s-expr = meta-variable
         ;                     | (maybe meta-variable)
         ;                     | (production-s-expr ellipsis)
         ;                     | (production-s-expr ellipsis production-s-expr ... . prod-s-expr)
         ;                     | (production-s-expr . production-s-expr)
         ;                     | ()
         ;  where meta-variable is either a terminal-meta-var or a nonterminal-meta-var possibly
         ;  followed by a sequence of ?, * or digits.
         
         ; production-s-exp->match-pattern : prodcution-s-exp -> (list syntax)
         ;    generate match patterns from the prodcution-s-exp
         (define (production-s-exp->match-pattern se)
           ; due to ellipsis the return value is a list of match patterns
           (define (recur se) 
             (with-syntax ([ooo #'(... ...)])
               (match (if (syntax-pair? se) (syntax-e se) se)
                 [(? identifier? x)
                  (define mv (meta-vars-ref metavars-ht x))
                  (with-syntax ([x x])
                    (list 
                     (match mv
                       [(terminal stx name meta-vars prettifier)
                        (with-syntax ([pred? (terminal->predicate-name #'x mv)])
                          #'(? pred? x))]
                       [(nonterminal stx name meta-vars productions)
                        #'x] ; nonterminals are checked in the recursive in the template
                       [_  (error 'production-s-exp->match-pattern "goty: ~a" se)])))]
                 ; TODO [(maybe mv) (error 'production-s-exp->match-pattern "todo: ~a" se)]
                 [(ellipsis se0)
                  (list (recur se0) #'ooo)]
                 [(list-rest (ellipsis se0) se* ... sen)
                  (list #`(list-rest #,@(recur se0) ooo 
                                     #,@(append-map recur se*) 
                                     #,@(recur sen)))]
                 [(cons se0 se1) 
                  (list #`(cons #,@(recur se0) #,@(recur se1)))]
                 ['() 
                  (list #''())]
                 [_ (error 'production-s-exp->match-pattern "gotx: ~a" se)])))
           (recur se))
         ;; Generate parsers and put everything together
         (define nonterminal-parsers (map construct-parse-nonterminal  nonterminals))
         (with-syntax ([(parse-nt ...) nonterminal-parsers]
                       [parse-lang     (format-id stx "~a-parse" lang-name)]
                       [parse-entry    (format-id stx "parse-~a" entry-name)])
           (define it
             #'(define (parse-lang se)
                 ; one parser for each nonterminal (that throws exceptions on parse errors)
                 parse-nt ...
                 ; start parsing at the nonterminal named entry
                 (parse-entry se)))
           ; (displayln it)
           it)))
     
     ;;; Ad 3) Put unparser here
     ; (struct    terminal-production production (terminal)    #:transparent)
     ; (struct nonterminal-production production (nonterminal) #:transparent)
     ; (struct     keyword-production production 
     ;    (keyword struct-name field-count field-names field-depths s-exp) #:transparent)
     ; (struct s-exp-production production ())
     
     (define unparser-definition-stx
       (let ()
         (define unparse-lang  (format-id stx "~a-unparse"  lang-name))
         (define unparse*-lang (format-id stx "~a-unparse*" lang-name))
         (define (construct-unparse-clause-for-terminal t)
           (match-define (terminal stx name meta-vars prettifier) t)
           (with-syntax ([name? (format-id stx "~a?" name)])
             (list #'[(? name? t) t])))
         (define (construct-unparse-clause nt)
           (match-define (nonterminal stx name meta-vars productions) nt)
           (append* ; each case returns a list of clauses
            (for/list ([p productions])
              (match p
                [(terminal-production    so pt)
                 (construct-unparse-clause-for-terminal pt)]
                [(nonterminal-production so pnt) '()]       ; pnt is handled by other nonterminal
                [(keyword-production so keyword struct-name _ field-names field-depths s-exp)
                 (with-syntax ([u unparse-lang] [u* unparse*-lang])
                   (define unparsed-fields
                     (for/list ([fn field-names] [fd field-depths])
                       (if (= fd 0)
                           #`(u #,fn)
                           #`(u* #,fn #,fd))))
                   (with-syntax ([(fn ...) field-names]
                                 [(ufn ...) unparsed-fields]
                                 [struct-name struct-name]
                                 [keyword keyword] [so so])               
                     (list #'[(struct-name fn ...)
                              (let ([fn ufn] ...)
                                (qq (fn ...) so))])))]
                [(s-exp-production so) 
                 (list #'[(cons non-keyword more) `(,non-keyword . ,more)])]
                [_ (error 'unparser-definition-stx "internal error, got: ~a" p)]))))
         (define unparser-clauses 
           (append (append-map construct-unparse-clause nonterminals)
                   (append-map construct-unparse-clause-for-terminal terminals)))
         (with-syntax ([(unparser-clause ...) unparser-clauses]
                       [unparse-lang  unparse-lang]
                       [unparse*-lang unparse*-lang]
                       [unparse-entry (format-id stx "unparse-~a" entry-name)])
           #'(begin
               (define (unparse*-lang ss d)
                 (if (= d 0) 
                     (unparse-lang ss)
                     (map (λ (s) (unparse*-lang s (- d 1))) ss)))
               (define (unparse-lang s)
                 (match s
                   unparser-clause ...
                   [_ (displayln s) (error 'unparse-lang "got: ~a" s)]))))))
     (displayln unparser-definition-stx)
     
     
     ;; Add this language to the list of defined languages
     (set! defined-languages (cons parsed-lang defined-languages))
     
     (displayln parser-definition-stx)
     (with-syntax ([(struct-def ...) struct-definitions-stx]
                   [parser-definition parser-definition-stx]
                   [unparser-definition unparser-definition-stx]
                   [langs defined-languages])
       (quasisyntax/loc stx
         (begin struct-def ...
                parser-definition
                unparser-definition
                ; make the language definition available for future expansions
                #;(begin-for-syntax
                    (set! defined-languages 'langs)))))]
    [_
     (raise-syntax-error 'define-language "expected (define-language name clause ...), got: " stx)]))

;;; syntax: (with-language lang-name nonterminal-name expr ...)
;;;   Use keyword as short for lang-name:nontermina-name:keyword within
;;;   uses of (construct <use-short-names-here>).

(define-syntax-parameter construct (λ (stx) #'(error 'construct "used outside with-language")))

(define-syntax (with-language stx)
  (syntax-parse stx
    [(_ lang-name:id nonterminal-name:id body:expr ...)
     (define (lang-name? l) (free-identifier=? #'lang-name (language-name l)))
     (define lang (for/first ([l defined-languages] #:when (lang-name? l)) l))
     (unless lang (raise-syntax-error 'with-language "undefined language" #'lang-name))
     (match-define 
       (language stx name entry terminals nonterminals keywords+constructors metavars-ht) lang)
     (with-syntax ([((keyword constructor) ...) keywords+constructors]
                   [(qualified-constructor ...) (map second keywords+constructors)])
       #'(syntax-parameterize 
          ([construct 
            (λ (so)
              (syntax-parse so
                [(__ e:expr)
                 (with-syntax ([keyword (datum->syntax so 'keyword)] ...)
                   #'(let ([keyword qualified-constructor] ...)
                       e))]))])
          body ...))]))

;;;
;;; EXAMPLES
;;;

(define (uvar? x)      (symbol? x))
(define (primitive? x) (and (symbol? x) (member x '(+ - add1))))
(define (datum? x)     (or (number? x) (symbol? x) (string? x) (boolean? x)))

(define-language Lsrc
  (entry Expr)
  (terminals
   (uvar (x))
   (primitive (pr))
   (datum (d)))
  (Expr (e body)
        (quote d)
        (if1 e0 e1)
        (if  e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body)
        (let    ([x* e*] ...) body)
        (letrec ([x* e*] ...) body)
        (set! x e)
        (pr e* ...)
        (call e e* ...)
        x))

(define-language L1
  (entry Expr) 
  (terminals
   (uvar (x))
   (primitive (pr))
   (datum (d)))
  (Expr (e body)
        (quote d)
        (if  e0 e1 e2)
        (begin e* ... e)
        (lambda (x* ...) body)
        (let    ([x* e*] ...) body)
        (letrec ([x* e*] ...) body)
        (set! x e)
        (pr e* ...)
        (call e e* ...)
        x))

;;; This is a manually written pass.
;;; Notes:
;;; For each nonterminal (here Expr) a functions is defined.
;;; For each nonterminal a mapper is defined (here Expr*)
;;; The recursion starts at the the entry  (here (Expr e)).
;;; The output is created using construct + with-language Lsrx Expr. 
;;; TODO: Introduce patten matching in the template.


; remove-one-armed-if : Lsrc (e) -> L1 ()
(define (pass-remove-one-armed-if e)
  ; Expr : Expr (e) -> Expr ()
  (define (Expr* e*) (map Expr e*))
  (define (Expr e)
    (with-language Lsrc Expr
      (match e
        [(Lsrc:Expr:quote d)           (construct (quote d))]
        [(Lsrc:Expr:if1 e0 e1)         (construct (if (Expr e0) (Expr e1) (quote #f)))]
        [(Lsrc:Expr:if e0 e1 e2)       (construct (if  (Expr e0) (Expr e1) (Expr e2)))]
        [(Lsrc:Expr:begin e* e)        (construct (begin (Expr* e*) (Expr e)))]
        [(Lsrc:Expr:lambda x* body)    (construct (lambda x* (Expr body)))]
        [(Lsrc:Expr:let x* e* body)    (construct (let x* (Expr* e*) (Expr body)))]
        [(Lsrc:Expr:letrec x* e* body) (construct (letrec x* (Expr* e*) (Expr body)))]
        [(Lsrc:Expr:set! x e)          (construct (set! x (Expr e)))]
        [(list pr e*)                  (construct (pr (Expr* e*)))]
        [(Lsrc:Expr:call e e*)         (construct (call (Expr e) (Expr* e*)))]
        [(? uvar? x)                    x]
        [other                         (error 'pass-remove-one-armed-if "got~a" other)])))
  (Expr e))

(pass-remove-one-armed-if
 (Lsrc-parse '(if1 '1 (if1 '2 '3))))

(Lsrc-unparse
 (pass-remove-one-armed-if
  (Lsrc-parse '(if1 '1 (if1 '2 '3)))))

#;(define-language LP
    (terminals
     (uvar (x))
     (datum (d))
     (primitive (pr)))
    (Expr (e body)
          d
          x
          pr
          (set! x e)
          ; (if e1 e2)
          (if e1 e2 e3)
          (begin e1 ... e2)
          (lambda (x ...) body1 ... body2)
          (let ((x e) ...) body1 ... body2)
          (letrec ((x e) ...) body1 ... body2)
          (e0 e1 ...)))



#;(with-language LP Expr
    (construct (if 1 2 3)))
; =>
;(LP:Expr:if 1 2 3)

; Note: If more than one nonterminal has an if production, 
;       then the Expr can't be omitted.

; (with-language LP Expr
;    (construct (if 1 2 (unconstruct (if 3 4 5)))))
; => 
; (LP:Expr:if 1 2 (if 3 4 5))
; =
; (LP:Expr:if 1 2 4)


#;(define-language L0 (extends LP)
    (Expr (e body)
          (- d
             x
             pr
             (e0 e1 ...))
          (+ (datum d)
             (var x)
             (primapp pr e ...)
             (app e0 e1 ...))))

(module+ test
  (define-language L0 
    (terminals
     (uvar (x))
     (datum (d))
     (primitive (pr)))
    (Expr (e body)
          (datum d)
          (var x)
          (primapp pr e ...)
          (app e0 e1 ...)
          (set! x e)
          ; (if e1 e2)
          (if e1 e2 e3)
          (begin e1 ... e2)
          (lambda (x ...)     body1 ... body2)
          (let    ((x e) ...) body1 ... body2)
          (letrec ((x e) ...) body1 ... body2)))
  
  ; Test that constructors exist and have correct number of fields
  
  (check-not-false (L0:Expr:datum 42))
  (check-not-false (L0:Expr:var 'x))
  (check-not-false (L0:Expr:primapp '+ '(1 2)))
  (check-not-false (L0:Expr:app 'f '(1 2)))
  (check-not-false (L0:Expr:set! 'x 3))
  (check-not-false (L0:Expr:if 1 2 3))
  (check-not-false (L0:Expr:begin (list 1 2 3) 4))
  (check-not-false (L0:Expr:lambda '(x y) '() 5))
  (check-not-false (L0:Expr:let    '(x y) '() '(1 2) 3))
  ; Test with-language and construct
  (check-equal? (with-language L0 Expr 43) 43)
  (check-equal? (with-language L0 Expr (construct (begin '(4) (if 1 2 3))))
                (L0:Expr:begin '(4) (L0:Expr:if 1 2 3))))


(with-language Lsrc Expr (if 42 43 44))
(with-language Lsrc Expr (construct (if 42 43 44)))
; note: begin only takes two arguments -- we need a matcher ?

Lsrc:Expr:if

(Lsrc-unparse
 (pass-remove-one-armed-if
  (Lsrc-parse '(begin '1 '2))))