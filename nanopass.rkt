#lang racket
;;; TODO
;;;   done  - parse define-language into structures
;;;   done  - produce structure definitions for nonterminals
;;;   done  - produce type checking constructors for the nonterminal structures
;;;   done  - accept nested use of ... 
;;;         - check References to meta-variables in a production must be unique
;;;  [done] - fix todo0 in construct-parse-clause
;;;           tempory fix in place see comment in construct-parse-clause
;;;         - unparsing
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
  (struct terminal    (stx name meta-vars prettifier)  #:prefab)
  ; name is an identifier, meta-vars is a list of identifeirs and prettifier
  ; is a syntax-object representing an expression.
  (struct nonterminal (stx name meta-vars productions) #:prefab #:mutable)
  ; productions is a list of syntax-objects of the follwing forms:
  ;   terminal-meta-var
  ;   nonterminal-meta-var
  ;   producition-s-expression
  ;   (keyword . production-s-expression)
  ; where keyword is neither type of meta var.
  (struct production (stx) #:prefab)
  ; stx is used for the syntax location (the original production appearing in define-language)
  (struct    terminal-production production (terminal)    #:prefab)
  (struct nonterminal-production production (nonterminal) #:prefab)
  (struct     keyword-production production 
    (keyword struct-name field-count field-names field-depths s-exp) #:prefab)
  (struct s-exp-production production ())
  ; a keyword production will generate a structure definition with
  ; where field-count is the number of fields,
  ;       field-names is a list of names (identifiers) of the fields
  ;       field-depths is a list of variable depths
  ;       (i.e.  x          has depth 0)
  ;              x ...      has depth 1
  ;             (x ...) ... has depth 2
  ;             etc
  (struct ellipsis (production-s-expression) #:prefab)
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

;;; define-language
(define-syntax (define-language stx)
  (define (syntax-error error-msg [stx stx]) (raise-syntax-error 'define-language error-msg stx))
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
     (define meta-vars-ht (make-hash))
     (define (meta-vars-ref  v)   
       (unless (identifier? v) (error 'here "got ~a" v))
       (hash-ref  meta-vars-ht (strip-meta-var-suffix (syntax-e v)) #f))
     (define (meta-vars-set! v a) (hash-set! meta-vars-ht (strip-meta-var-suffix (syntax-e v)) a))
     (define (meta-var? v) 
       (match v
         [(? identifier?) (meta-vars-ref v)]
         [(ellipsis v)    (meta-var? v)]
         [_               #f]))
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
     ;; At this point all meta variables are stored in meta-vars-ht.
     (define (terminal-meta-var? v)
       (cond [(meta-vars-ref v) => terminal?]
             [else #f]))
     (define (nonterminal-meta-var? v)
       (cond [(meta-vars-ref v) => nonterminal?]
             [else #f]))
     
     ;; Collect all keywords used in the productions and store the associated productions.
     (define keywords-ht (make-hash))
     (define (keywords-ref v)    (hash-ref keywords-ht (strip-meta-var-suffix (syntax-e v)) #f))
     (define (keywords-set! v p) 
       (define old-productions (hash-ref keywords-ht (strip-meta-var-suffix (syntax-e v)) '()))
       (hash-set! keywords-ht (strip-meta-var-suffix (syntax-e v)) (list p old-productions)))
     (define (register-keyword k nt p) 
       ; todo: add additional checks here
       (keywords-set! k (list nt p)))
     (for ([nt nonterminals])
       (for ([prod (nonterminal-productions nt)])
         (syntax-parse prod #:literals (maybe)
           [x:id (unless (meta-vars-ref #'x)
                   (syntax-error 
                    "variable in production is not associated to a terminal or a nonterminal" #'x))]
           [(x:id . _)
            (unless (meta-vars-ref #'x)
              (register-keyword #'x nt prod))]
           [(maybe meta-var)   'todo-a-maybe-production]
           [(something . more) 'todo-an-application-production]
           [__ 'ok])))
     ;; This helper is needed to rewrite s-exprs such that pat ... becomes (ellipsis pat)
     (define (maybe?    stx) (and (identifier? stx) (eq? (syntax-e stx) 'maybe)))
     (define (make-ellipsis-prefix se)
       (define (ellipsis? stx) (eq? (syntax-e stx) '...))
       (define (recur se)
         (match (or (syntax-pair? se) se)
           [(? identifier? v)               (if (meta-var? v) v (error 'here "foo"))]
           [(? syntax? s)                   (recur (syntax-e s))]
           [(list (? maybe?) (? meta-var?)) se]   ; todo: ntroduce maybe struct ?
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
     ;; Now we can categorize the productions in the nonterminals
     (for ([nt nonterminals])
       (define prods
         (for/list ([prod (nonterminal-productions nt)])
           (syntax-parse prod #:literals (maybe)
             [x:id 
              (match (meta-vars-ref #'x)
                [(? terminal? t)     (terminal-production prod t)]
                [(? nonterminal? nt) (nonterminal-production prod nt)]
                [_ (error 'define-language "internal error - expected earlier detection")])]
             [(maybe meta-var)   (error 'todo-a-maybe-production)]
             [(~and (x:id field ...) (_ . s-exp))
              (match (keywords-ref #'x)
                [(list orig-nt ps)
                 ;; x is a keyword ...
                 ;; In order to make later processing easier we 
                 ;; rewrite the s-exp such that  s-exp ...  becomes (ellipsis s-exp)
                 
                 ; todo: should (ellipsis (maybe mv)) also count as a maybe?
                 
                 ;   production-s-expr = meta-variable
                 ;                  | (maybe meta-variable)
                 ;                  | (production-s-expr ellipsis)
                 ;                  | (production-s-expr ellipsis production-s-expr ... . prod-s-expr)
                 ;                  | (production-s-expr . production-s-expr)
                 ;                  | ()
                 (struct extracted-name (name depth) #:prefab)
                 (define (extract-names se)
                   (define (recur se d)
                     (define (map-recur se* d) (map (λ (se) (recur se d)) se*))
                     (match (if (and (syntax? se) (not (identifier? se)))
                                (syntax-e se)
                                se)
                       [(ellipsis se)                     (recur se d)]
                       [(? meta-var? v)                   (list (extracted-name v d))]
                       [(list (ellipsis se) se* ...)      (list (recur se (+ d 1))
                                                                (map-recur se* d))]
                       [(list (? maybe?) (? meta-var? v)) (list v)]
                       [(cons se0 se1)                    (list (recur se0 d) (recur se1 d))]
                       ['()                               '()]
                       [_ (error 'extract-names "got~a" se)]))
                   (flatten (recur se 0)))
                 (define extracted-names (extract-names (make-ellipsis-prefix #'(field ...))))
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
                 (keyword-production prod keyword struct-name field-count field-names field-depths 
                                     (make-ellipsis-prefix #'s-exp))]
                ;; otherwise it is an s-expression
                [_ (s-exp-production (make-ellipsis-prefix prod))])]
             [(something . more) (s-exp-production prod prod)]
             [__ 'ok])))
       ; replace old contents of productions field in the nonterminal with
       ; the structure representation of productions
       (set-nonterminal-productions! nt prods)
       ; (displayln (list 'define-language 'productions: ))
       ; (displayln prods)
       )
     
     
     (define all-terminal-meta-vars    (append-map terminal-meta-vars terminals))
     
     ;; At this point we are ready to 
     ;;   1) define structures representing the nonterminals
     ;;   2) save information on the language for define-pass and others
     ;;   3) define an unparser
     
     ;; Ad 1) For each nonterminal production of the form (keyword . production-s-expression)
     ;;       we define a struct lang-name:keyword
     ;; (define-language L (nt (mv ...) (keyword . production-s-expression) ...)
     ;; will generate structs (struct L:nt:keyword f0 f1 f2 ...) where
     ;; the number of fields are given by production-s-expression.
     
     (define structs
       (apply append
         (for/list ([nt nonterminals])
           (match nt
             [(nonterminal nt-stx nt-name meta-vars productions)
              (for/list ([prod productions]
                         #:when (keyword-production? prod))
                (match prod
                  [(keyword-production stx keyword struct-name field-count field-names field-depths 
                                       s-exp)
                   (with-syntax ([struct-name struct-name]
                                 [(field-name ...) field-names])
                     ; This is the basic structure definition:
                     #'(struct struct-name (field-name ...) #:prefab)
                     ; TODO: Generate constructors with "contracts"
                     )]
                  [_ (error)]))]
             [_ (error)]))))
     (define the-parser
       (with-syntax ([ooo #'(... ...)])
         (define (nonterminal->parse-name nt depth)
           (case depth
             [(0)  (format-id stx "parse-~a" (nonterminal-name nt))]
             [else  (format-id stx "parse*-~a" (nonterminal-name nt))]  ; XXXX
             #;[else 
                ; if you get this error implement depths larger than 1 ...
                (error 'nonterminal->parse-name "got: ~a" depth)]))
         (define (field-name->nonterminal f)  (meta-vars-ref  f))
         (define (construct-parse-nonterminal nt)
           ; return a parser of s-exp representing the nonterminal nt
           (match-define (nonterminal stx name meta-vars productions) nt)
           (define parse-nt  (nonterminal->parse-name nt 0))
           (define parse-nt* (nonterminal->parse-name nt 1))
           (define clauses (append-map (λ(p) (construct-parse-clause name p)) productions))
           (with-syntax ([parse-nt parse-nt] [parse-nt* parse-nt*] [(clause ...) clauses])
             #'(begin
                 (define (parse-nt* se* d) 
                   (if (= d 1)
                       (map parse-nt se*)
                       (map (λ(se) (parse-nt* se (- d 1))) se*)))
                 (define (parse-nt se)
                   (match se 
                     clause ...
                     [else (displayln 'parse-nt)
                           (displayln '(clause ...))
                           (displayln se)
                           (error 'parse-nt "got: ~a" se)])))))
         (define (production-s-exp->match-template se)
           (define (recur se d) ; d=depth
             (with-syntax ([ooo #'(... ...)])
               (match (if (syntax-pair? se) (syntax-e se) se)
                 [(? identifier? x)
                  (define mv (meta-vars-ref x))
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
                          ; whatever the nonterminal matched needs to be parsed.
                          ; The depths determine how.
                          (case d
                            [(0) #'(parse-nt x)]
                            [(1) #'(parse*-nt x 1)]
                            [else (with-syntax ([d d])
                                    #'(parse*-nt x d))]
                            ))]
                       [_ ; unrecognized meta variable
                        (displayln se)
                        (error 'production-s-exp->match-pattern "internal error: ~a" se)])))]
                 ; [(maybe mv) (error 'production-s-exp->match-pattern "todo: ~a" se)]
                 [(ellipsis se0)
                  (list (recur se0 (+ d 1)))]
                 [(list-rest (ellipsis se0) se* ... sen)
                  #;(displayln (list se se0 se* sen))
                  #;(displayln (append (recur se0 (+ d 1))
                                       (append-map (λ(se) (recur se d)) se*)
                                       (recur sen d)))
                  (append (recur se0 (+ d 1))
                          (append-map (λ(se) (recur se d)) se*)
                          (recur sen d))]
                 [(cons se0 se1) 
                  (list #`(cons #,@(recur se0 d) #,@(recur se1 d)))]
                 ['() '()]
                 [_ (error 'production-s-exp->match-pattern "gotx: ~a" se)])))
           (recur se 0))
         (define (construct-parse-clause nt-name prod)
           (match prod
             [(terminal-production stx term)
              (match-define (terminal stx name meta-vars prettifier) term)
              (with-syntax ([pred? (terminal->predicate-name #'here term)])
                (list #'[(? pred? x) x]))]
             [(nonterminal-production stx nonterm) 
              ; TODO: one nonterminal has another as production: do what ... ?
              ; 1. produce parse-clauses for the nonterminal and include here?
              ; 2. add new mode to parse-clause that doesn't error but return #f,
              ;    when an se doesn't parse [ and then use parse-nt in a (? parse-nt result)
              ;    pattern
              (match-define (nonterminal stx name meta-vars productions) nonterm)
              (append-map (λ(p) (construct-parse-clause name p)) productions)
              ; TODO: Note the above append-map works.
              ;       However ... the clauses will be instantiated several times,
              ;       which imply a risk of blowing up the generated code size.
              ;       It would be better to rewrite parse-nt : give it a failure
              ;       continuation (thunk) that be (lambda () #f) which makes
              ;       it usable as a mach pattern predicate - or it can be
              ;       (lambda () (raise-exception)).
              ]
             [(keyword-production stx keyword struct-name 
                                  field-count field-names field-depths s-exp)
              (with-syntax ([keyword keyword]
                            [(field-name ...) field-names]
                            [constructor  (qualified-struct-name stx lang-name nt-name keyword)]
                            [(field-expression ...)
                             (for/list ([f field-names] [fd field-depths])
                               (cond [(terminal-meta-var? f) f]
                                     [(nonterminal-meta-var? f)
                                      (with-syntax ([parse-field (nonterminal->parse-name
                                                                  (field-name->nonterminal f) fd)]
                                                    [f f])
                                        (if (= fd 0)
                                            #'(parse-field f)
                                            #`(parse-field f #,fd)))]
                                     [else (error 'todo1 "got ~a" f)]))])
                (list #`[(cons 'keyword #,@(production-s-exp->match-pattern s-exp))
                         (constructor field-expression ...)]))]
             [(s-exp-production stx)
              (list #`[#,@(production-s-exp->match-pattern stx) 
                       #,@(production-s-exp->match-template stx)])]
             [else (error 'construct-parse-clause "todo got ~a" prod)]))
         (define (terminal->predicate-name loc t)
           (format-id loc "~a?" (terminal-name t)))
         ;   production-s-expr = meta-variable
         ;                     | (maybe meta-variable)
         ;                     | (production-s-expr ellipsis)
         ;                     | (production-s-expr ellipsis production-s-expr ... . prod-s-expr)
         ;                     | (production-s-expr . production-s-expr)
         ;                     | ()
         ;  where meta-variable is either a terminal-meta-var or a nonterminal-meta-var possibly
         ;  followed by a sequence of ?, * or digits.
         (define (production-s-exp->match-pattern se)
           (define (recur se) ; recur returns a list of pattens (due to pat ... patterns)
             (with-syntax ([ooo #'(... ...)])
               (match (if (syntax-pair? se) (syntax-e se) se)
                 [(? identifier? x)
                  (define mv (meta-vars-ref x))
                  (with-syntax ([x x])
                    (list 
                     (match mv
                       [(terminal stx name meta-vars prettifier)
                        (with-syntax ([pred? (terminal->predicate-name #'x mv)])
                          #'(? pred? x))]
                       [(nonterminal stx name meta-vars productions)
                        #'x]
                       [_ 
                        (displayln se)
                        (error 'production-s-exp->match-pattern "goty: ~a" se)])))]
                 ; [(maybe mv) (error 'production-s-exp->match-pattern "todo: ~a" se)]
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
         
         (with-syntax ([(parse-nt ...) (map construct-parse-nonterminal nonterminals)]
                       [parse-lang     (format-id stx "~a-parse" lang-name)]
                       [parse-entry    (format-id stx "parse-~a" entry-name)])
           (define it
             #'(define (parse-lang se)
                 parse-nt ...
                 (parse-entry se)))
           (displayln it)
           it)
         
         ;;; Example: Handwritten parser.
         
         ;;; TODO: Implement production-s-expression->parser-match-pattern
         #;(define (parse se)
             ; 1) define parsers for each nonterminal
             ; 2) call the entry parser
             (define (parse-expr se)
               (define p parse-expr)
               (define (p* se*) (map p se*))
               (match se
                 ;[(? uvar? x)        x]
                 ;[(? primitive? pr) pr]
                 ; [(? datum? d)       d]
                 ; terminal-productions generate a pattern using the predicate
                 [(? uvar? x)         x]
                 ; a keyword k becomes 'k and terminal-meta-vars use predicates,
                 ; nonterminal-meta-vars recursivly calls the appropriate parser
                 [(list 'quote (? datum? d))                  (Lsrc:Expr:quote d)]
                 [(list 'if    e0 e1 e2)                      (Lsrc:Expr:if (p e0) (p e1) (p e2))]
                 [(list 'begin e* ooo e)                      (Lsrc:Expr:begin (map p e*) (p e))]
                 [(list 'lambda (list (? uvar? x*) ooo) body) (Lsrc:Expr:lambda x* (p body))]
                 [(list 'let    (list [list x* e*] ooo) body) (Lsrc:Expr:let    x* (p* e*) (p body))]
                 [(list 'letrec (list [list x* e*] ooo) body) (Lsrc:Expr:letrec x* (p* e*) (p body))]
                 [(list 'set!   (? uvar? x) e)                (Lsrc:Expr:set!   x  (p e))]
                 [(list 'call e e* ooo)                       (Lsrc:Expr:call   (p e) (p* e*))]
                 [(list (? primitive? pr) e* ooo)             (cons pr (p* e*))]
                 [_ (error 'parse "got: ~a" se)]))
             (parse-expr se))))
     
     (with-syntax ([(struct-def ...) structs]
                   [parser-definition the-parser])
       (syntax/loc stx
         (begin struct-def ...
                parser-definition)))
     
     #;(datum->syntax #'here
                      (list 'quote
                            (list (list (list "lang-name"   (syntax-e #'lang-name)))
                                  (list "entry-name"  entry-name)
                                  (list "terminals"   terminals)
                                  (list "non-terms"   nonterminals))))]))

(define (uvar? x)      (symbol? x))
(define (primitive? x) (and (symbol? x) (member x '(+ - add1))))
(define (datum? x)     (or (number? x) (symbol? x) (string? x)))
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
        (foo ((e*) ...) ...)  ; <= requires depth 2
        (call e e* ...)))

(define-language Lsrc1
  (entry Command) 
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
        (foo ((e*) ...) ...)
        (call e e* ...))
  (Command (c)
           e  ; <= apropos todo0
           (run e)))

(define (parse- se)
  ; 1) define parsers for each nonterminal
  ; 2) call the entry parser
  (define (parse-expr se)
    (define p parse-expr)
    (define (p* se*) (map p se*))
    (match se
      ;[(? uvar? x)        x]
      ;[(? primitive? pr) pr]
      ; [(? datum? d)       d]
      ; terminal-productions generate a pattern using the predicate
      [(? uvar? x)         x]
      ; a keyword k becomes 'k and terminal-meta-vars use predicates,
      ; nonterminal-meta-vars recursivly calls the appropriate parser
      [(list 'quote (? datum? d))                  (Lsrc:Expr:quote d)]
      [(list 'if    e0 e1 e2)                      (Lsrc:Expr:if (p e0) (p e1) (p e2))]
      [(list 'begin e* ... e)                      (Lsrc:Expr:begin (map p e*) (p e))]
      [(list 'lambda (list (? uvar? x*) ...) body) (Lsrc:Expr:lambda x* (p body))]
      [(list 'let    (list [list x* e*] ...) body) (Lsrc:Expr:let    x* (p* e*) (p body))]
      [(list 'letrec (list [list x* e*] ...) body) (Lsrc:Expr:letrec x* (p* e*) (p body))]
      [(list 'set!   (? uvar? x) e)                (Lsrc:Expr:set!   x  (p e))]
      [(list 'call e e* ...)                       (Lsrc:Expr:call   (p e) (p* e*))]
      [(list (? primitive? pr) e* ...)             (cons pr (p* e*))]
      [_ (error 'parse "got: ~a" se)]))
  (parse-expr se))
